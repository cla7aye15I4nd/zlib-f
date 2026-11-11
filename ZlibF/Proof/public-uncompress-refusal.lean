import ZlibF.Proof.«public-uncompress-memory»

/-!
# uncompr.c: local storage and the argument refusal of `uncompress2_z`

`uncompress2_z` first makes its automatic `z_stream` and the 8-byte
`stream.reserved` block. Both take the next two block identities of a `Fresh`
heap and consume no allocator attempt. On a refused argument both are freed,
and the heap equals the caller heap entry by entry.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Uncompr
set_option autoImplicit false

/-- The heap after the automatic `z_stream` is made. -/
def streamHeap (h : Heap) : Heap :=
  { h with streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc))),
           nextBlk := h.nextBlk + 1 }

/-- The bytes of the automatic `stream.reserved` block. -/
def reservedBytes (h : Heap) : Array UInt8 :=
  Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)

/-- The heap after the automatic `z_stream` and `stream.reserved` are made. -/
def localHeap (h : Heap) : Heap :=
  { streamHeap h with
    bytes := upd h.bytes (h.nextBlk + 1) (some (reservedBytes h)),
    ro := upd h.ro (h.nextBlk + 1) false, nextBlk := h.nextBlk + 2 }

theorem allocLocalZ_run {h : Heap} (fresh : Fresh h) :
    allocLocalZ h = .ok (some (.tab h.nextBlk), streamHeap h) := by
  have slot : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk = false :=
    Heap.slotUsed_eq_false.2 (fresh h.nextBlk (Nat.le_refl _))
  simp [allocLocalZ, allocZStream, slot, streamHeap]

theorem allocLocal_run {h : Heap} (fresh : Fresh h) :
    allocLocal 8 (streamHeap h) = .ok (.ref (.blk (h.nextBlk + 1)) 0, localHeap h) := by
  have free : ¬ h.live (h.nextBlk + 1) := fresh _ (by omega)
  have slot : (streamHeap h).slotUsed (streamHeap h).nextBlk = false := by
    apply Heap.slotUsed_eq_false.2
    simp only [Heap.live, streamHeap, upd_ne _ _ _ _ (show h.nextBlk + 1 ≠ h.nextBlk by omega)]
    exact free
  unfold allocLocal allocBytes
  rw [slot]
  simp only [Bool.false_eq_true, ite_false]
  rfl

/-- Heaps that keep every live byte block, its read-only flag, the deflate states,
the static tables and the borrowed error text agree on every live byte view. -/
structure ByteViewsKept (h h' : Heap) : Prop where
  bytes : ∀ b, h.bytes b ≠ none → h'.bytes b = h.bytes b ∧ h'.ro b = h.ro b
  dstates : h'.dstates = h.dstates
  static : h'.static = h.static
  borrow : h'.libcErrorBorrow = h.libcErrorBorrow

theorem ByteViewsKept.get {h h' : Heap} (k : ByteViewsKept h h') {r : BRef} {a : Array UInt8}
    (g : Space.get h r = some a) : Space.get h' r = some a ∧ Space.ro h' r = Space.ro h r := by
  cases r with
  | blk b =>
    simp only [BRef.get_blk, BRef.ro_blk] at g ⊢
    obtain ⟨e1, e2⟩ := k.bytes b (by rw [g]; simp)
    exact ⟨by rw [e1, g], e2⟩
  | str i =>
    simp only [BRef.get_str, BRef.ro_str, staticStringBytes, k.borrow] at g ⊢
    exact ⟨g, trivial⟩
  | dstate_depth i =>
    simp only [Space.get, Space.ro, k.dstates] at g ⊢
    exact ⟨g, trivial⟩
  | st_dist_code =>
    simp only [BRef.get_st_dist_code, BRef.ro_st_dist_code, k.static] at g ⊢
    exact ⟨g, trivial⟩
  | st_length_code =>
    simp only [BRef.get_st_length_code, BRef.ro_st_length_code, k.static] at g ⊢
    exact ⟨g, trivial⟩

theorem ByteViewsKept.bytes_of {h h' : Heap} (k : ByteViewsKept h h') {p : BPtr} {n : Nat}
    {xs : List UInt8} (b : Bytes h p n xs) : Bytes h' p n xs := by
  rcases b with e | ⟨r, i, a, rfl, g, hi, hx⟩
  · exact Or.inl e
  · exact Or.inr ⟨r, i, a, rfl, (k.get g).1, hi, hx⟩

theorem ByteViewsKept.writable_of {h h' : Heap} (k : ByteViewsKept h h') {p : BPtr} {n : Nat}
    (w : Writable h p n) : Writable h' p n := by
  rcases w with e | ⟨r, i, a, rfl, g, ro, hi⟩
  · exact Or.inl e
  · exact Or.inr ⟨r, i, a, rfl, (k.get g).1, by rw [(k.get g).2]; exact ro, hi⟩

theorem ByteViewsKept.cell_of {h h' : Heap} (k : ByteViewsKept h h') {p : BPtr} {v : UInt64}
    (c : LengthCell h p v) : LengthCell h' p v :=
  ⟨k.bytes_of c.1, k.writable_of c.2⟩

theorem ByteViewsKept.trans {h h' h'' : Heap} (k : ByteViewsKept h h') (k' : ByteViewsKept h' h'') :
    ByteViewsKept h h'' where
  bytes b hb := by
    obtain ⟨e1, e2⟩ := k.bytes b hb
    obtain ⟨f1, f2⟩ := k'.bytes b (by rw [e1]; exact hb)
    exact ⟨f1.trans e1, f2.trans e2⟩
  dstates := k'.dstates.trans k.dstates
  static := k'.static.trans k.static
  borrow := k'.borrow.trans k.borrow

theorem localHeap_kept {h : Heap} (fresh : Fresh h) : ByteViewsKept h (localHeap h) where
  bytes b hb := by
    have live : h.live b := Or.inl hb
    have ne : b ≠ h.nextBlk + 1 := fun e => fresh b (by omega) live
    simp [localHeap, streamHeap, upd_ne _ _ _ _ ne]
  dstates := rfl
  static := rfl
  borrow := rfl

/-- The heap after both automatic objects are freed. -/
def releasedHeap (H : Heap) (k : Nat) : Heap :=
  { H with bytes := upd H.bytes (k + 1) none, streams := upd H.streams k none }

/-- The heap after `stream.reserved` alone is freed. -/
def reservedFreed (H : Heap) (k : Nat) : Heap := { H with bytes := upd H.bytes (k + 1) none }

/-- Freeing `stream.reserved` on any heap that still holds it as a writable block. -/
theorem freeB_reserved_run {H : Heap} {k : Nat} {a : Array UInt8}
    (hb : H.bytes (k + 1) = some a) (ro : H.ro (k + 1) = false) :
    freeB (.ref (.blk (k + 1)) 0) H = .ok ((), reservedFreed H k) := by
  simp [freeB, hb, ro, reservedFreed]

/-- Freeing the automatic stream on any heap that still holds it. -/
theorem freeZStream_local_run {H : Heap} {k : Nat} {z : ZStream} (hs : H.streams k = some z) :
    freeZStream (some (.tab k)) H = .ok ((), { H with streams := upd H.streams k none }) := by
  simp [freeZStream, hs]

theorem localHeap_reserved (h : Heap) :
    (localHeap h).bytes (h.nextBlk + 1) = some (reservedBytes h) ∧
      (localHeap h).ro (h.nextBlk + 1) = false := by
  simp [localHeap]

theorem localHeap_stream (h : Heap) :
    (reservedFreed (localHeap h) h.nextBlk).streams h.nextBlk =
      some (ZStream.garbage (h.garbage h.nalloc)) := by
  simp [reservedFreed, localHeap, streamHeap]

theorem releasedHeap_eq (h : Heap) :
    { reservedFreed (localHeap h) h.nextBlk with
      streams := upd (reservedFreed (localHeap h) h.nextBlk).streams h.nextBlk none } =
      releasedHeap (localHeap h) h.nextBlk := rfl

theorem uncompress2_z_refused {h : Heap} {dest destLen source sourceLen : BPtr} {capacity n : UInt64}
    (fresh : Fresh h)
    (dcell : destLen ≠ .null → LengthCell h destLen capacity)
    (scell : sourceLen ≠ .null → LengthCell h sourceLen n)
    (bad : sourceLen = .null ∨ destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨
      (dest = .null ∧ capacity ≠ 0)) :
    C.run (uncompress2_z dest destLen source sourceLen) h =
      .ok (Z_STREAM_ERROR, releasedHeap (localHeap h) h.nextBlk) := by
  have kept := localHeap_kept fresh
  unfold uncompress2_z
  simp only [C.run, bind_app, allocLocalZ_run fresh, allocLocal_run fresh]
  by_cases hs : sourceLen = .null
  · simp only [hs, beq_self_eq_true, ite_true, bind_app, pure_app,
      freeB_reserved_run (localHeap_reserved h).1 (localHeap_reserved h).2,
      freeZStream_local_run (localHeap_stream h), releasedHeap_eq]
  have ln : load64 sourceLen (localHeap h) = .ok (n, localHeap h) := load64_cell (kept.cell_of (scell hs))
  simp only [show (sourceLen == Ptr.null) = false from beq_false_of_ne hs, Bool.false_eq_true, ite_false,
    bind_app, ln]
  have pos : ∀ x : UInt64, (decide (x > 0) = true) ↔ x ≠ 0 := by
    intro x
    simp only [decide_eq_true_eq, ne_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
    constructor
    · intro hx e; rw [e] at hx; simp at hx
    · intro hx; have : x.toNat ≠ 0 := fun e => hx (UInt64.toNat_inj.mp (by simpa using e)); omega
  by_cases c1 : n ≠ 0 ∧ source = .null
  · have e1 : (decide (n > 0) && source == Ptr.null) = true := by
      simp only [Bool.and_eq_true, (pos n).2 c1.1, c1.2, beq_self_eq_true, and_self]
    simp only [e1, ite_true, bind_app, pure_app,
      freeB_reserved_run (localHeap_reserved h).1 (localHeap_reserved h).2,
      freeZStream_local_run (localHeap_stream h), releasedHeap_eq]
  have e1 : (decide (n > 0) && source == Ptr.null) = false := by
    cases hb : (decide (n > 0) && source == Ptr.null)
    · rfl
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact absurd ⟨(pos n).1 hb.1, hb.2⟩ c1
  simp only [e1, Bool.false_eq_true, ite_false]
  by_cases hd : destLen = .null
  · simp only [hd, beq_self_eq_true, ite_true, bind_app, pure_app,
      freeB_reserved_run (localHeap_reserved h).1 (localHeap_reserved h).2,
      freeZStream_local_run (localHeap_stream h), releasedHeap_eq]
  have ld : load64 destLen (localHeap h) = .ok (capacity, localHeap h) :=
    load64_cell (kept.cell_of (dcell hd))
  simp only [show (destLen == Ptr.null) = false from beq_false_of_ne hd, Bool.false_eq_true, ite_false,
    bind_app, ld]
  by_cases c2 : capacity ≠ 0 ∧ dest = .null
  · have e2 : (decide (capacity > 0) && dest == Ptr.null) = true := by
      simp only [Bool.and_eq_true, (pos capacity).2 c2.1, c2.2, beq_self_eq_true, and_self]
    simp only [e2, ite_true, bind_app, pure_app,
      freeB_reserved_run (localHeap_reserved h).1 (localHeap_reserved h).2,
      freeZStream_local_run (localHeap_stream h), releasedHeap_eq]
  exfalso
  rcases bad with b | b | b | b
  · exact hs b
  · exact hd b
  · exact c1 ⟨b.2, b.1⟩
  · exact c2 ⟨b.2, b.1⟩

/-- After the refusal, every object of the caller heap is as before and no new
object is live: the tables may only be longer. -/
theorem released_same {h : Heap} (fresh : Fresh h) :
    SameObjectsUpToTableShape h (releasedHeap (localHeap h) h.nextBlk) := by
  have n0 := fresh h.nextBlk (Nat.le_refl _)
  have n1 := fresh (h.nextBlk + 1) (by omega)
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at n0 n1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    simp only [releasedHeap, localHeap, streamHeap, upd_apply]
    split <;> simp_all
  · intro b; rfl
  · intro b live
    have ne : b ≠ h.nextBlk + 1 := fun e => fresh b (by omega) live
    simp [releasedHeap, localHeap, streamHeap, upd_ne _ _ _ _ ne]
  · intro b
    simp only [releasedHeap, localHeap, streamHeap, upd_apply]
    split <;> simp_all
  all_goals first | (intro b; rfl) | rfl | (simp [releasedHeap, localHeap, streamHeap])

end ZlibF.Spec.Public.Proofs.Uncompress
