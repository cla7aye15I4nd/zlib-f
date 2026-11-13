import ZlibF.Proof.«gz.skeleton-model»
import ZlibF.Zlib.«gzwrite.c»
import ZlibF.Proof.«gzlib.c.base»
import ZlibF.Proof.«public-deflate-init2»

/-!
# gzwrite.c: safety of `gz_init`

`gz_init` allocates `in`, and for a compressing writer `out` and the deflate state
(`deflateInit2_(strm, level, Z_DEFLATED, MAX_WBITS + 16, DEF_MEM_LEVEL, strategy)`). Every
allocation can fail, and `level` and `strategy` are arbitrary, so `deflateInit2_` can refuse,
fail an allocation, or succeed. On failure `gz_init` frees what it allocated and records
`Z_MEM_ERROR` with `gz_error`. The proof uses the run of `deflateInit2_` (the proved contract
`init2_main` and its internal heaps, for the fields of the `gz_state` record outside the stream)
and the interface lemma `GzInv.gz_error` of the skeleton model.
-/

namespace Zlib.Gzwrite.SafeInit
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Frames and object tables -/

theorem frame_refl (h : Heap) (C : Nat → Prop) : Frame h h C :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem frame_mono {a b : Heap} {C D : Nat → Prop} (f : Frame a b C) (hCD : ∀ x, C x → D x) :
    Frame a b D := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := f
  exact ⟨f1, f2, f3, f4, f5, fun x hx hn => f6 x hx (fun c => hn (hCD x c))⟩

theorem live_of_slots {a b : Heap} {x : Nat} (e1 : b.bytes x = a.bytes x) (e2 : b.words x = a.words x)
    (e3 : b.streams x = a.streams x) (e4 : b.gzheaders x = a.gzheaders x) (e5 : b.dstates x = a.dstates x)
    (e6 : b.istates x = a.istates x) (e7 : b.gzstates x = a.gzstates x) : b.live x ↔ a.live x := by
  simp only [Heap.live, e1, e2, e3, e4, e5, e6, e7]

theorem frame_trans {a b c : Heap} {C D : Nat → Prop} (f : Frame a b C) (g : Frame b c D) :
    Frame a c (fun x => C x ∨ D x) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := f
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := g
  refine ⟨f1.trans g1, f2.trans g2, f3.trans g3, Nat.le_trans f4 g4, Nat.le_trans f5 g5, ?_⟩
  intro x hx hn
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := f6 x hx (fun c => hn (Or.inl c))
  have hb : b.live x := (live_of_slots e1 e2 e3 e4 e5 e6 e7).2 hx
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := g6 x hb (fun c => hn (Or.inr c))
  exact ⟨d1.trans e1, d2.trans e2, d3.trans e3, d4.trans e4, d5.trans e5, d6.trans e6, d7.trans e7,
    d8.trans e8⟩

theorem live_of_gz {H : Heap} {x : Nat} {t : GzState} (g : H.gzstates x = some t) : H.live x := by
  simp [Heap.live, g]

theorem live_of_bytes {H : Heap} {x : Nat} {a : Array UInt8} (g : H.bytes x = some a) : H.live x := by
  simp [Heap.live, g]

theorem live_of_words {H : Heap} {x : Nat} {a : Array UInt16} (g : H.words x = some a) : H.live x := by
  simp [Heap.live, g]

theorem live_of_dstates {H : Heap} {x : Nat} {d : DeflateState} (g : H.dstates x = some d) : H.live x := by
  simp [Heap.live, g]

theorem not_live_none {H : Heap} {x : Nat} (n : ¬ H.live x) :
    H.bytes x = none ∧ H.words x = none ∧ H.streams x = none ∧ H.gzheaders x = none ∧ H.dstates x = none ∧
      H.istates x = none ∧ H.gzstates x = none := by
  simp only [Heap.live, ne_eq, not_or, Decidable.not_not] at n
  exact n

theorem fresh_none {H : Heap} (fr : Fresh H) {x : Nat} (hx : H.nextBlk ≤ x) :
    H.bytes x = none ∧ H.words x = none ∧ H.streams x = none ∧ H.gzheaders x = none ∧ H.dstates x = none ∧
      H.istates x = none ∧ H.gzstates x = none :=
  not_live_none (fr x hx)

theorem cnt_zero {α : Type} {o : Option α} (e : Zlib.Gzlib.Spec.cnt o = 0) : o = none := by
  cases o with
  | none => rfl
  | some _ => simp at e

/-- A block that holds a `gz_state` record holds nothing else. -/
theorem uniq_gz_only {H : Heap} (u : Zlib.Gzlib.Spec.Uniq H) {x : Nat} {t : GzState} (g : H.gzstates x = some t) :
    H.bytes x = none ∧ H.words x = none ∧ H.streams x = none ∧ H.gzheaders x = none ∧ H.dstates x = none ∧
      H.istates x = none := by
  have hu := u x
  rw [g] at hu
  simp only [Zlib.Gzlib.Spec.cnt_some] at hu
  exact ⟨cnt_zero (by omega), cnt_zero (by omega), cnt_zero (by omega), cnt_zero (by omega),
    cnt_zero (by omega), cnt_zero (by omega)⟩

theorem uniq_bytes_only {H : Heap} (u : Zlib.Gzlib.Spec.Uniq H) {x : Nat} {a : Array UInt8}
    (g : H.bytes x = some a) : H.dstates x = none ∧ H.gzstates x = none := by
  have hu := u x
  rw [g] at hu
  simp only [Zlib.Gzlib.Spec.cnt_some] at hu
  exact ⟨cnt_zero (by omega), cnt_zero (by omega)⟩

theorem uniq_words_only {H : Heap} (u : Zlib.Gzlib.Spec.Uniq H) {x : Nat} {a : Array UInt16}
    (g : H.words x = some a) : H.bytes x = none ∧ H.dstates x = none := by
  have hu := u x
  rw [g] at hu
  simp only [Zlib.Gzlib.Spec.cnt_some] at hu
  exact ⟨cnt_zero (by omega), cnt_zero (by omega)⟩

theorem uniq_dstates_only {H : Heap} (u : Zlib.Gzlib.Spec.Uniq H) {x : Nat} {d : DeflateState}
    (g : H.dstates x = some d) : H.bytes x = none ∧ H.gzstates x = none := by
  have hu := u x
  rw [g] at hu
  simp only [Zlib.Gzlib.Spec.cnt_some] at hu
  exact ⟨cnt_zero (by omega), cnt_zero (by omega)⟩

/-! ## Platform object sizes -/

theorem fit_of {a b : Heap} (fit : ZlibF.PlatformMemory.ByteObjectsFit a)
    (hs : b.static = a.static) (hl : b.libcErrorBorrow = a.libcErrorBorrow)
    (hB : ∀ x arr, b.bytes x = some arr → a.bytes x = some arr ∨
      arr.size < ZlibF.PlatformMemory.byteObjectLimit)
    (hD : ∀ x d, b.dstates x = some d → (∃ d0, a.dstates x = some d0 ∧ d0.depth = d.depth) ∨
      d.depth.size < ZlibF.PlatformMemory.byteObjectLimit) :
    ZlibF.PlatformMemory.ByteObjectsFit b := by
  intro ref arr e
  cases ref with
  | blk x =>
    rcases hB x arr e with e' | e'
    · exact fit (.blk x) arr e'
    · exact e'
  | str k =>
    apply fit (.str k) arr
    have same : staticStringBytes b k = staticStringBytes a k := by
      unfold staticStringBytes
      rw [hl]
    rw [BRef.get_str] at e ⊢
    rw [← same]
    exact e
  | dstate_depth id =>
    change (b.dstates id).map (·.depth) = some arr at e
    cases hd : b.dstates id with
    | none => rw [hd] at e; cases e
    | some d =>
      rw [hd] at e
      simp only [Option.map_some, Option.some.injEq] at e
      subst e
      rcases hD id d hd with ⟨d0, h0, hdep⟩ | h'
      · apply fit (.dstate_depth id) d.depth
        change (a.dstates id).map (·.depth) = some d.depth
        rw [h0]
        simp [hdep]
      · exact h'
  | st_dist_code =>
    apply fit .st_dist_code arr
    change some a.static.dist_code = some arr
    rw [← hs]
    exact e
  | st_length_code =>
    apply fit .st_length_code arr
    change some a.static.length_code = some arr
    rw [← hs]
    exact e

/-! ## Transport of strings and buffers -/

theorem bytes_transport {a b : Heap} {p : BPtr} {n : Nat} {xs : List UInt8} {x : Nat}
    (hp : p = .ref (.blk x) 0) (hx : b.bytes x = a.bytes x) (c : Bytes a p n xs) : Bytes b p n xs := by
  rcases c with ⟨hn, _, _⟩ | ⟨r, j, arr, hr, hg, hle, hxs⟩
  · rw [hp] at hn
    cases hn
  · refine Or.inr ⟨r, j, arr, hr, ?_, hle, hxs⟩
    rw [hp] at hr
    cases hr
    change b.bytes x = some arr
    rw [hx]
    exact hg

theorem cstring_transport {a b : Heap} {p : BPtr} {xs : List UInt8} {x : Nat}
    (hp : p = .ref (.blk x) 0) (hx : b.bytes x = a.bytes x) (c : CString a p xs) : CString b p xs :=
  ⟨bytes_transport hp hx c.1, c.2.1, c.2.2⟩

theorem malloc_transport {a b : Heap} {p : BPtr} {n : Nat} {x : Nat}
    (hp : p = .ref (.blk x) 0) (hx : b.bytes x = a.bytes x) (hr : b.ro x = a.ro x)
    (m : MallocBuffer a p n) : MallocBuffer b p n := by
  obtain ⟨y, arr, hy, hb, hro, hle⟩ := m
  rw [hp] at hy
  cases hy
  exact ⟨x, arr, hp, by rw [hx]; exact hb, by rw [hr]; exact hro, hle⟩

/-! ## The invariant before `gz_init` -/

theorem owned0 {h : Heap} {i : Nat} {s : GzState} (hsz : s.size = 0) (b : Nat) :
    GzOwned h i s b ↔ b = i ∨ s.path = .ref (.blk b) 0 ∨ s.msg = .ref (.blk b) 0 := by
  simp [GzOwned, hsz]

theorem path_blk {h : Heap} {i : Nat} {s : GzState} (cm : GzCommon h i s) :
    ∃ pb, s.path = .ref (.blk pb) 0 ∧ h.live pb ∧ pb ≠ i := by
  obtain ⟨p, _, m⟩ := cm.path
  obtain ⟨pb, a, hp, hb, _, _⟩ := m
  refine ⟨pb, hp, live_of_bytes hb, ?_⟩
  exact (cm.distinct.2 s.path (by simp [ownedPtrs]) pb (by rw [hp]; rfl)).1

theorem msg_blk {h : Heap} {i : Nat} {s : GzState} (cm : GzCommon h i s) :
    s.msg = .null ∨ ∃ mb, s.msg = .ref (.blk mb) 0 ∧ h.live mb ∧ mb ≠ i := by
  rcases cm.msg with hn | ⟨q, _, m⟩
  · exact Or.inl hn
  · obtain ⟨mb, a, hp, hb, _, _⟩ := m
    refine Or.inr ⟨mb, hp, live_of_bytes hb, ?_⟩
    exact (cm.distinct.2 s.msg (by simp [ownedPtrs]) mb (by rw [hp]; rfl)).1

theorem nodup2 {a b : Nat} (h : a ≠ b) : [a, b].Nodup := by
  simp [h]

theorem nodup3 {a b c : Nat} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) : [a, b, c].Nodup := by
  simp [h1, h2, h3]

theorem blkOf_null : blkOf (.null : BPtr) = none := rfl

theorem msg_of_blkOf {h : Heap} {i : Nat} {s : GzState} (cm : GzCommon h i s) {b : Nat}
    (e : blkOf s.msg = some b) : s.msg = .ref (.blk b) 0 := by
  rcases msg_blk cm with hn | ⟨mb, hm, _, _⟩
  · rw [hn] at e; cases e
  · rw [hm] at e ⊢
    cases e
    rfl

/-- `avail_in` is zero before the buffers exist (W4 with `size = 0`). -/
theorem avail_zero {h : Heap} {i : Nat} {s : GzState} (wr : GzWriteInv h i s) (hsz : s.size = 0) :
    s.strm.avail_in = 0 := by
  rcases wr.input with e | ⟨a, _, hle⟩
  · exact e
  · rw [hsz] at hle
    have : s.strm.avail_in.toNat = 0 := by simp at hle; omega
    exact UInt32.toNat_inj.mp (by simpa using this)

/-! ## Heap steps of `gz_init` -/

/-- The heap after a successful `malloc(n)` (`allocB`). -/
def aHeap (H : Heap) (n : Nat) : Heap :=
  { H with bytes := upd H.bytes H.nextBlk (some (Array.ofFn (n := n) fun j => Junk.of (H.garbage H.nalloc j.val))),
           ro := upd H.ro H.nextBlk false, nextBlk := H.nextBlk + 1, nalloc := H.nalloc + 1 }

/-- The heap after a failed `malloc`. -/
def fHeap (H : Heap) : Heap := { H with nalloc := H.nalloc + 1 }

/-- The heap after `free` of the byte block `b`. -/
def dHeap (H : Heap) (b : Nat) : Heap := { H with bytes := upd H.bytes b none }

theorem allocB_eq (n : Nat) (H : Heap) : allocB n H =
    if H.allocOk H.nalloc then
      (if H.slotUsed H.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
       else .ok (.ref (.blk H.nextBlk) 0, aHeap H n))
    else .ok (.null, fHeap H) := rfl

theorem freeB_eq (b : Nat) (H : Heap) : freeB (.ref (.blk b) 0) H =
    match H.bytes b with
    | some _ => if H.ro b then .error (.ub "free of a read-only block") else .ok ((), dHeap H b)
    | none => .error (.ub "free of a freed or invalid pointer") := rfl

theorem aHeap_gz (H : Heap) (n : Nat) : (aHeap H n).gzstates = H.gzstates := rfl
theorem aHeap_allocOk (H : Heap) (n : Nat) : (aHeap H n).allocOk = H.allocOk := rfl
theorem aHeap_nalloc (H : Heap) (n : Nat) : (aHeap H n).nalloc = H.nalloc + 1 := rfl
theorem aHeap_nextBlk (H : Heap) (n : Nat) : (aHeap H n).nextBlk = H.nextBlk + 1 := rfl
theorem aHeap_bytes (H : Heap) (n : Nat) : (aHeap H n).bytes =
    upd H.bytes H.nextBlk (some (Array.ofFn (n := n) fun j => Junk.of (H.garbage H.nalloc j.val))) := rfl
theorem aHeap_ro (H : Heap) (n : Nat) : (aHeap H n).ro = upd H.ro H.nextBlk false := rfl
theorem fHeap_gz (H : Heap) : (fHeap H).gzstates = H.gzstates := rfl
theorem fHeap_allocOk (H : Heap) : (fHeap H).allocOk = H.allocOk := rfl
theorem fHeap_nalloc (H : Heap) : (fHeap H).nalloc = H.nalloc + 1 := rfl
theorem fHeap_nextBlk (H : Heap) : (fHeap H).nextBlk = H.nextBlk := rfl
theorem fHeap_bytes (H : Heap) : (fHeap H).bytes = H.bytes := rfl
theorem fHeap_ro (H : Heap) : (fHeap H).ro = H.ro := rfl
theorem dHeap_gz (H : Heap) (b : Nat) : (dHeap H b).gzstates = H.gzstates := rfl
theorem dHeap_bytes (H : Heap) (b : Nat) : (dHeap H b).bytes = upd H.bytes b none := rfl
theorem dHeap_ro (H : Heap) (b : Nat) : (dHeap H b).ro = H.ro := rfl
theorem dHeap_nextBlk (H : Heap) (b : Nat) : (dHeap H b).nextBlk = H.nextBlk := rfl

theorem slot_setS (H : Heap) (j b : Nat) (t : GzState) (hb : b ≠ j) :
    (Zlib.Gzlib.Spec.setS H j t).slotUsed b = H.slotUsed b := by
  simp [Heap.slotUsed, Zlib.Gzlib.Spec.setS, upd_ne _ _ _ _ hb]

theorem slot_aHeap (H : Heap) (n b : Nat) (hb : b ≠ H.nextBlk) : (aHeap H n).slotUsed b = H.slotUsed b := by
  simp [Heap.slotUsed, aHeap, upd_ne _ _ _ _ hb]

/-! ## Heaps that differ from the start only in the record and in new byte blocks -/

/-- `X` is `h` with the record `i` replaced by `t` and byte blocks added from `h.nextBlk` on. -/
structure Ext (h X : Heap) (i : Nat) (t : GzState) : Prop where
  bytes : ∀ x, x < h.nextBlk → X.bytes x = h.bytes x
  ro : ∀ x, x < h.nextBlk → h.live x → x ≠ i → X.ro x = h.ro x
  words : ∀ x, X.words x = h.words x
  streams : ∀ x, X.streams x = h.streams x
  gzheaders : ∀ x, X.gzheaders x = h.gzheaders x
  dstates : ∀ x, X.dstates x = h.dstates x
  istates : ∀ x, X.istates x = h.istates x
  gzstates : ∀ x, X.gzstates x = if x = i then some t else h.gzstates x
  static : X.static = h.static
  allocOk : X.allocOk = h.allocOk
  garbage : X.garbage = h.garbage
  libc : X.libcErrorBorrow = h.libcErrorBorrow
  next : h.nextBlk ≤ X.nextBlk
  nalloc : h.nalloc ≤ X.nalloc
  fresh : ∀ x, X.nextBlk ≤ x → X.bytes x = none
  small : ∀ x a, h.nextBlk ≤ x → X.bytes x = some a → a.size < ZlibF.PlatformMemory.byteObjectLimit

section Ext
variable {h X : Heap} {i : Nat} {s t : GzState}

theorem rec_lt (hs : h.gzstates i = some s) (fr : Fresh h) : i < h.nextBlk :=
  Fresh.lt fr (live_of_gz hs)

theorem Ext.recd (E : Ext h X i t) : X.gzstates i = some t := by
  rw [E.gzstates, if_pos rfl]

theorem Ext.live_iff (E : Ext h X i t) (hs : h.gzstates i = some s) (fr : Fresh h) (x : Nat) :
    X.live x ↔ h.live x ∨ (h.nextBlk ≤ x ∧ X.bytes x ≠ none) := by
  have il := rec_lt hs fr
  by_cases hx : h.nextBlk ≤ x
  · obtain ⟨b, w, st, gh, d, is, g⟩ := fresh_none fr hx
    have xi : x ≠ i := by omega
    have hl : ¬ h.live x := fr x hx
    simp only [Heap.live, E.words, E.streams, E.gzheaders, E.dstates, E.istates, E.gzstates,
      if_neg xi, w, st, gh, d, is, g] at hl ⊢
    simp [hx, b]
  · have xl : x < h.nextBlk := by omega
    by_cases xi : x = i
    · subst xi
      exact ⟨fun _ => Or.inl (live_of_gz hs), fun _ => live_of_gz E.recd⟩
    · simp only [Heap.live, E.bytes x xl, E.words, E.streams, E.gzheaders, E.dstates, E.istates, E.gzstates,
        if_neg xi]
      simp [hx]

theorem Ext.frame (E : Ext h X i t) (fr : Fresh h) : Frame h X (fun x => x = i) := by
  refine ⟨E.static.symm, E.allocOk.symm, E.garbage.symm, E.next, E.nalloc, ?_⟩
  intro x hx hn
  have xl : x < h.nextBlk := Fresh.lt fr hx
  exact ⟨E.bytes x xl, E.words x, E.streams x, E.gzheaders x, E.dstates x, E.istates x,
    by rw [E.gzstates, if_neg hn], E.ro x xl hx hn⟩

theorem Ext.fresh' (E : Ext h X i t) (hs : h.gzstates i = some s) (fr : Fresh h) : Fresh X := by
  intro x hx hl
  have hx0 : h.nextBlk ≤ x := Nat.le_trans E.next hx
  rcases (E.live_iff hs fr x).1 hl with l | ⟨_, n⟩
  · exact fr x hx0 l
  · exact n (E.fresh x hx)

theorem Ext.uniq (E : Ext h X i t) (hs : h.gzstates i = some s) (fr : Fresh h)
    (u : Zlib.Gzlib.Spec.Uniq h) : Zlib.Gzlib.Spec.Uniq X := by
  have il := rec_lt hs fr
  intro x
  by_cases hx : h.nextBlk ≤ x
  · obtain ⟨_, w, st, gh, d, is, g⟩ := fresh_none fr hx
    have xi : x ≠ i := by omega
    rw [E.words, E.streams, E.gzheaders, E.dstates, E.istates, E.gzstates, if_neg xi, w, st, gh, d, is, g]
    cases X.bytes x <;> simp [Zlib.Gzlib.Spec.cnt]
  · have xl : x < h.nextBlk := by omega
    have hu := u x
    by_cases xi : x = i
    · subst xi
      rw [E.bytes x xl, E.words, E.streams, E.gzheaders, E.dstates, E.istates, E.gzstates, if_pos rfl]
      rw [hs] at hu
      simpa using hu
    · rw [E.bytes x xl, E.words, E.streams, E.gzheaders, E.dstates, E.istates, E.gzstates, if_neg xi]
      exact hu

theorem Ext.fit (E : Ext h X i t) (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit X := by
  apply fit_of fit E.static E.libc
  · intro x a e
    by_cases hx : h.nextBlk ≤ x
    · exact Or.inr (E.small x a hx e)
    · rw [E.bytes x (by omega)] at e
      exact Or.inl e
  · intro x d e
    rw [E.dstates] at e
    exact Or.inl ⟨d, e, rfl⟩

theorem Ext.globals (E : Ext h X i t) (g : LibraryGlobals h) : LibraryGlobals X := by
  unfold LibraryGlobals at g ⊢
  rw [E.static]
  exact g

theorem Ext.same (E : Ext h X i t) (fr : Fresh h) (x : Nat) (hl : h.live x) (xi : x ≠ i) :
    X.bytes x = h.bytes x ∧ X.ro x = h.ro x :=
  ⟨E.bytes x (Fresh.lt fr hl), E.ro x (Fresh.lt fr hl) hl xi⟩

/-- The stream of the record owns the same blocks as before when its state pointer is unchanged. -/
theorem Ext.streamOwned (E : Ext h X i t) (hs : h.gzstates i = some s) (hst : t.strm.state = s.strm.state)
    (b : Nat) : StreamOwned X (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := by
  have gX : (gzStrm i).get X = some t.strm := by simp [gzStrm, ZStreamRef.get, E.recd]
  have gh : (gzStrm i).get h = some s.strm := by simp [gzStrm, ZStreamRef.get, hs]
  unfold StreamOwned
  rw [gX, gh]
  simp only [Option.some.injEq, exists_eq_left', hst, E.dstates, E.istates]

theorem Ext.base (hs : h.gzstates i = some s) (fr : Fresh h) : Ext h h i s where
  bytes _ _ := rfl
  ro _ _ _ _ := rfl
  words _ := rfl
  streams _ := rfl
  gzheaders _ := rfl
  dstates _ := rfl
  istates _ := rfl
  gzstates x := by
    by_cases e : x = i
    · rw [if_pos e, e, hs]
    · rw [if_neg e]
  static := rfl
  allocOk := rfl
  garbage := rfl
  libc := rfl
  next := Nat.le_refl _
  nalloc := Nat.le_refl _
  fresh _ hx := Fresh.bytes fr hx
  small x a hx e := by rw [Fresh.bytes fr hx] at e; cases e

theorem Ext.setS (E : Ext h X i t) (t' : GzState) : Ext h (Zlib.Gzlib.Spec.setS X i t') i t' where
  bytes := E.bytes
  ro := E.ro
  words := E.words
  streams := E.streams
  gzheaders := E.gzheaders
  dstates := E.dstates
  istates := E.istates
  gzstates x := by
    by_cases e : x = i
    · subst e
      simp
    · rw [if_neg e, Zlib.Gzlib.Proofs.setS_gz_ne X i x t' e, E.gzstates, if_neg e]
  static := E.static
  allocOk := E.allocOk
  garbage := E.garbage
  libc := E.libc
  next := E.next
  nalloc := E.nalloc
  fresh := E.fresh
  small := E.small

theorem Ext.alloc (E : Ext h X i t) (n : Nat) (hn : n < ZlibF.PlatformMemory.byteObjectLimit) :
    Ext h (aHeap X n) i t where
  bytes x hx := by
    have := E.next
    rw [aHeap_bytes, upd_ne _ _ _ _ (by omega)]
    exact E.bytes x hx
  ro x hx hl xi := by
    have := E.next
    rw [aHeap_ro, upd_ne _ _ _ _ (by omega)]
    exact E.ro x hx hl xi
  words := E.words
  streams := E.streams
  gzheaders := E.gzheaders
  dstates := E.dstates
  istates := E.istates
  gzstates := E.gzstates
  static := E.static
  allocOk := E.allocOk
  garbage := E.garbage
  libc := E.libc
  next := Nat.le_trans E.next (Nat.le_succ _)
  nalloc := Nat.le_trans E.nalloc (Nat.le_succ _)
  fresh x hx := by
    rw [aHeap_nextBlk] at hx
    rw [aHeap_bytes, upd_ne _ _ _ _ (by omega)]
    exact E.fresh x (by omega)
  small x a hx e := by
    rw [aHeap_bytes] at e
    by_cases ex : x = X.nextBlk
    · subst ex
      rw [upd_same] at e
      cases e
      simpa using hn
    · rw [upd_ne _ _ _ _ ex] at e
      exact E.small x a hx e

theorem Ext.failed (E : Ext h X i t) : Ext h (fHeap X) i t where
  bytes := E.bytes
  ro := E.ro
  words := E.words
  streams := E.streams
  gzheaders := E.gzheaders
  dstates := E.dstates
  istates := E.istates
  gzstates := E.gzstates
  static := E.static
  allocOk := E.allocOk
  garbage := E.garbage
  libc := E.libc
  next := E.next
  nalloc := Nat.le_trans E.nalloc (Nat.le_succ _)
  fresh := E.fresh
  small := E.small

theorem Ext.drop (E : Ext h X i t) (b : Nat) (hb : h.nextBlk ≤ b) : Ext h (dHeap X b) i t where
  bytes x hx := by
    rw [dHeap_bytes, upd_ne _ _ _ _ (by omega)]
    exact E.bytes x hx
  ro := E.ro
  words := E.words
  streams := E.streams
  gzheaders := E.gzheaders
  dstates := E.dstates
  istates := E.istates
  gzstates := E.gzstates
  static := E.static
  allocOk := E.allocOk
  garbage := E.garbage
  libc := E.libc
  next := E.next
  nalloc := E.nalloc
  fresh x hx := by
    rw [dHeap_bytes]
    by_cases ex : x = b
    · subst ex
      rw [upd_same]
    · rw [upd_ne _ _ _ _ ex]
      exact E.fresh x hx
  small x a hx e := by
    rw [dHeap_bytes] at e
    by_cases ex : x = b
    · subst ex
      rw [upd_same] at e
      cases e
    · rw [upd_ne _ _ _ _ ex] at e
      exact E.small x a hx e

end Ext

/-! ## Failed `deflateInit2_` -/

/-- After a failed `deflateInit2_` every object table is as before, except the record `i`. -/
def FailSlots (H A : Heap) (i : Nat) : Prop :=
  (∀ x, A.bytes x = H.bytes x ∧ A.words x = H.words x ∧ A.streams x = H.streams x ∧
    A.gzheaders x = H.gzheaders x ∧ A.dstates x = H.dstates x ∧ A.istates x = H.istates x ∧
    (x ≠ i → A.gzstates x = H.gzstates x) ∧ (H.live x → x ≠ i → A.ro x = H.ro x)) ∧
  A.static = H.static ∧ A.allocOk = H.allocOk ∧ A.garbage = H.garbage ∧ H.nextBlk ≤ A.nextBlk ∧
    H.nalloc ≤ A.nalloc

theorem failSlots_of_frame {H A : Heap} {i : Nat} {g g' : GzState} (f : Frame H A (fun x => x = i))
    (live : ∀ x, A.live x ↔ H.live x) (uH : Zlib.Gzlib.Spec.Uniq H) (uA : Zlib.Gzlib.Spec.Uniq A)
    (gH : H.gzstates i = some g) (gA : A.gzstates i = some g') : FailSlots H A i := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := f
  refine ⟨fun x => ?_, f1.symm, f2.symm, f3.symm, f4, f5⟩
  by_cases xi : x = i
  · subst xi
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := uniq_gz_only uA gA
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := uniq_gz_only uH gH
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm, a5.trans b5.symm,
      a6.trans b6.symm, fun e => absurd rfl e, fun _ e => absurd rfl e⟩
  · by_cases hl : H.live x
    · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := f6 x hl xi
      exact ⟨e1, e2, e3, e4, e5, e6, fun _ => e7, fun _ _ => e8⟩
    · have nA : ¬ A.live x := fun l => hl ((live x).1 l)
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := not_live_none nA
      obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := not_live_none hl
      exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm, a5.trans b5.symm,
        a6.trans b6.symm, fun _ => a7.trans b7.symm, fun l => absurd l hl⟩

theorem Ext.ofFail {h X A : Heap} {i : Nat} {s t t' : GzState} (E : Ext h X i t)
    (hs : h.gzstates i = some s) (fr : Fresh h) (F : FailSlots X A i) (hA : A.gzstates i = some t')
    (hl : A.libcErrorBorrow = X.libcErrorBorrow) : Ext h A i t' where
  bytes x hx := ((F.1 x).1).trans (E.bytes x hx)
  ro x hx hlx xi := ((F.1 x).2.2.2.2.2.2.2 ((E.live_iff hs fr x).2 (Or.inl hlx)) xi).trans (E.ro x hx hlx xi)
  words x := (F.1 x).2.1.trans (E.words x)
  streams x := (F.1 x).2.2.1.trans (E.streams x)
  gzheaders x := (F.1 x).2.2.2.1.trans (E.gzheaders x)
  dstates x := (F.1 x).2.2.2.2.1.trans (E.dstates x)
  istates x := (F.1 x).2.2.2.2.2.1.trans (E.istates x)
  gzstates x := by
    by_cases e : x = i
    · rw [if_pos e, e, hA]
    · rw [if_neg e, (F.1 x).2.2.2.2.2.2.1 e, E.gzstates, if_neg e]
  static := F.2.1.trans E.static
  allocOk := F.2.2.1.trans E.allocOk
  garbage := F.2.2.2.1.trans E.garbage
  libc := hl.trans E.libc
  next := Nat.le_trans E.next F.2.2.2.2.1
  nalloc := Nat.le_trans E.nalloc F.2.2.2.2.2
  fresh x hx := ((F.1 x).1).trans (E.fresh x (Nat.le_trans F.2.2.2.2.1 hx))
  small x a hx e := E.small x a hx (((F.1 x).1).symm.trans e)

end Zlib.Gzwrite.SafeInit

/-! ## The run of `deflateInit2_` on the stream of a `gz_state` record -/

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open DefaultInit
open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees same_objects_refl)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem gzInit_put_gz (X : Heap) (i : Nat) (v : ZStream) :
    ((ZStreamRef.in_gzstate_strm i).put X v).gzstates i = (X.gzstates i).map (fun s => { s with strm := v }) := by
  simp only [ZStreamRef.put]
  cases e : X.gzstates i with
  | none => simp [e]
  | some s => simp

theorem gzInit_put_gz_ne (X : Heap) {i x : Nat} (v : ZStream) (hx : x ≠ i) :
    ((ZStreamRef.in_gzstate_strm i).put X v).gzstates x = X.gzstates x := by
  simp only [ZStreamRef.put]
  split <;> simp [upd_ne _ _ _ _ hx]

theorem gzInit_put_streams (X : Heap) (i : Nat) (v : ZStream) :
    ((ZStreamRef.in_gzstate_strm i).put X v).streams = X.streams := by
  simp only [ZStreamRef.put]
  split <;> rfl

theorem gzInit_put_libc (X : Heap) (r : ZStreamRef) (v : ZStream) :
    (r.put X v).libcErrorBorrow = X.libcErrorBorrow := by
  cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem gzInit_byteResult_libc (h : Heap) (n : Nat) : (byteResult h n).libcErrorBorrow = h.libcErrorBorrow := by
  unfold byteResult
  split <;> rfl

theorem gzInit_wordResult_libc (h : Heap) (n : Nat) : (wordResult h n).libcErrorBorrow = h.libcErrorBorrow := by
  unfold wordResult
  split <;> rfl

theorem gzInit_freeBytes_libc (h : Heap) (p : BPtr) : (freeBytes h p).libcErrorBorrow = h.libcErrorBorrow := by
  unfold freeBytes
  split <;> rfl

theorem gzInit_freeWords_libc (h : Heap) (p : WPtr) : (freeWords h p).libcErrorBorrow = h.libcErrorBorrow := by
  unfold freeWords
  split <;> rfl

theorem gzInit_rollback_gz (wb mem : Nat) (h g : Heap) :
    (Zlib.Deflate.Proofs.GeneralInit.rollbackBuffers wb mem h g).gzstates = g.gzstates :=
  (rollback_stable wb mem h g).gzstates

theorem gzInit_buffers_gz (wb mem : Nat) (h : Heap) :
    (Zlib.Deflate.Proofs.GeneralInit.buffersHeap h wb mem).gzstates = h.gzstates :=
  (buffers_stable wb mem h).gzstates

/-- `deflateInit2_` on `&state->strm`: the run exists; only the stream field of the record changes;
`avail_in` is kept; a failure keeps every object table except the record and leaves the state
pointer `NULL` or unchanged. -/
theorem gz_strm_init_run {H : Heap} {i : Nat} {g : GzState} {version : BPtr}
    (hg : H.gzstates i = some g) (hf : Fresh H) (hu : Uniq H) (hgl : LibraryGlobals H)
    (ha : DefaultOrNull g.strm) (hv : VersionValue H version (some 49))
    (level method wb mem strategy : Int32) :
    ∃ rc after, C.run (deflateInit2_ (some (.in_gzstate_strm i)) level method wb mem strategy version 112) H =
        .ok (rc, after) ∧
      (∃ z', after.gzstates i = some { g with strm := z' } ∧ z'.avail_in = g.strm.avail_in ∧
        (rc ≠ Z_OK → z'.state = none ∨ z'.state = g.strm.state)) ∧
      after.libcErrorBorrow = H.libcErrorBorrow ∧
      (rc ≠ Z_OK → Zlib.Gzwrite.SafeInit.FailSlots H after i) := by
  have hz : (ZStreamRef.in_gzstate_strm i).get H = some g.strm := by simp [ZStreamRef.get, hg]
  let zp := preparedStream g.strm
  let hp := (ZStreamRef.in_gzstate_strm i).put H zp
  have hshape := shape_put hz zp
  have hfP : Fresh hp := hshape.fresh (by simp [hp]) hf
  have huP : Uniq hp := hshape.uniq hu
  have hzP : (ZStreamRef.in_gzstate_strm i).get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have hgP : hp.gzstates i = some { g with strm := zp } := by simp [hp, gzInit_put_gz, hg]
  have hlP : hp.libcErrorBorrow = H.libcErrorBorrow := gzInit_put_libc _ _ _
  have slotsP : Zlib.Gzwrite.SafeInit.FailSlots H hp i := by
    refine ⟨fun x => ⟨by simp [hp], by simp [hp], by simp [hp, gzInit_put_streams], by simp [hp], by simp [hp],
      by simp [hp], fun hx => by simp [hp, gzInit_put_gz_ne _ _ hx], fun _ _ => by simp [hp]⟩,
      by simp [hp], by simp [hp], by simp [hp], by simp [hp], by simp [hp]⟩
  have entry : C.run (deflateInit2_ (some (.in_gzstate_strm i)) level method wb mem strategy version 112) H =
      (match ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
      | none => pure Z_STREAM_ERROR
      | some p => alloc (some (.in_gzstate_strm i)) (Int32.ofNat p.level) (wrapCode p.wrap) p.wbits p.memLevel
          method strategy) hp := by
    rw [C.run, entry_run hz hv, tail_params]
    rfl
  cases params : ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
  | none =>
    rw [params] at entry
    exact ⟨Z_STREAM_ERROR, hp, entry, ⟨zp, hgP, rfl, fun _ => Or.inr rfl⟩, hlP, fun _ => slotsP⟩
  | some p =>
    rw [params] at entry
    dsimp only at entry
    obtain ⟨m8, l9, w9, w15, m1, m9, mEq, s0, s4, sEq⟩ := params_ranges params
    have meth : method = 8 := Int32.toInt_inj.mp (by rw [m8]; rfl)
    subst meth
    let lev : Int32 := Int32.ofNat p.level
    have levInt : lev.toInt = p.level := Int32.toInt_ofNat_of_lt (by omega)
    by_cases first : H.allocOk H.nalloc = false
    · refine ⟨Z_MEM_ERROR, { hp with nalloc := hp.nalloc + 1 }, ?_, ⟨zp, hgP, rfl, fun _ => Or.inr rfl⟩, hlP,
        fun _ => ⟨slotsP.1, slotsP.2.1, slotsP.2.2.1, slotsP.2.2.2.1, slotsP.2.2.2.2.1, Nat.le_succ_of_le slotsP.2.2.2.2.2⟩⟩
      rw [entry]
      exact alloc_state_fail hzP haP.1 (by simpa [hp] using first) _ _ _ _ _ _
    · have firstT : H.allocOk H.nalloc = true := by cases he : H.allocOk H.nalloc <;> simp_all
      by_cases all : (List.range 5).all (fun j => H.allocOk (H.nalloc + j)) = true
      · have allok : ∀ j, j < 5 → H.allocOk (H.nalloc + j) = true := by
          simpa only [List.all_eq_true, List.mem_range] using all
        have countP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
          intro j hj
          simpa [hp] using allok j hj
        obtain ⟨a1, a2, a3, qa, hsucc, -, -, -, -⟩ := allocate_success (wrapCode p.wrap) p.wbits p.memLevel
          hfP huP hzP haP (by simpa [hp] using globals_trees hgl) countP lev strategy (by omega) (by omega)
          s0 s4 (by cases p.wrap <;> decide) (by cases p.wrap <;> decide) w9 w15 m1 m9
        refine ⟨Z_OK, successHeap (wrapCode p.wrap) p.wbits p.memLevel hp (.in_gzstate_strm i) zp lev strategy
          a1 a2 a3 qa, ?_, ⟨resultStream (wrapCode p.wrap) p.wbits p.memLevel hp (.in_gzstate_strm i) zp lev
          strategy, ?_, rfl, fun e => absurd rfl e⟩, ?_, fun e => absurd rfl e⟩
        · rw [entry]
          exact hsucc
        · simp [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW, gzInit_put_gz, hgP]
        · simp [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW, setD,
            gzInit_put_libc, hp]
      · let ph := publishedHeap hp (.in_gzstate_strm i) zp (wrapCode p.wrap) p.wbits p.memLevel
        have failed : ((bufferPointers ph p.wbits p.memLevel).1 == .null ||
            (bufferPointers ph p.wbits p.memLevel).2.1 == .null ||
            (bufferPointers ph p.wbits p.memLevel).2.2.1 == .null ||
            (bufferPointers ph p.wbits p.memLevel).2.2.2 == .null) = true := by
          apply Classical.byContradiction
          intro hn
          have hb : ((bufferPointers ph p.wbits p.memLevel).1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.2.1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.2.2 == .null) = false := by
            cases he : ((bufferPointers ph p.wbits p.memLevel).1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.2.1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.2.2 == .null) <;> simp_all
          obtain ⟨h0, h1, h2, h3⟩ := (buffers_failed_iff p.wbits p.memLevel ph).mp hb
          apply all
          rw [List.all_eq_true]
          intro j hj
          have hj5 := List.mem_range.mp hj
          have hn : ph.nalloc = H.nalloc + 1 := by simp [ph, publishedHeap, stateHeap, hp]
          have ao : ph.allocOk = H.allocOk := by simp [ph, publishedHeap, stateHeap, hp]
          rw [ao, hn] at h0 h1 h2 h3
          have cases5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
          rcases cases5 with h | h | h | h | h <;> subst j <;>
            simpa only [Nat.add_assoc, Nat.add_zero] using (by assumption)
        obtain ⟨m, hm⟩ := finish_failure (wrapCode p.wrap) p.wbits p.memLevel hzP haP lev strategy 8 failed
        let after := Zlib.Deflate.Proofs.GeneralInit.failureHeap (wrapCode p.wrap) p.wbits p.memLevel hp
          (.in_gzstate_strm i) zp m
        have gA : after.gzstates i = some { g with strm :=
            { Zlib.Deflate.Proofs.GeneralInit.failureStream hp zp m with state := none } } := by
          simp only [after]
          rw [Zlib.Deflate.Proofs.GeneralInit.failure_heap_eq]
          simp only [clearDHeap]
          rw [gzInit_put_gz, gzInit_rollback_gz]
          simp [Zlib.Deflate.Proofs.GeneralInit.failureMsgHeap, gzInit_put_gz, gzInit_buffers_gz, publishedHeap,
            stateHeap, hgP]
        have lA : after.libcErrorBorrow = H.libcErrorBorrow := by
          simp only [after]
          rw [Zlib.Deflate.Proofs.GeneralInit.failure_heap_eq]
          simp [clearDHeap, gzInit_put_libc, Zlib.Deflate.Proofs.GeneralInit.rollbackBuffers,
            gzInit_freeBytes_libc, gzInit_freeWords_libc, Zlib.Deflate.Proofs.GeneralInit.failureMsgHeap, setD,
            Zlib.Deflate.Proofs.GeneralInit.buffersHeap, Zlib.Deflate.Proofs.GeneralInit.headHeap,
            Zlib.Deflate.Proofs.GeneralInit.prevHeap, Zlib.Deflate.Proofs.GeneralInit.windowHeap,
            gzInit_byteResult_libc, gzInit_wordResult_libc, publishedHeap, stateHeap, hp]
        have shp := failure_shape (wrapCode p.wrap) p.wbits p.memLevel hzP hfP m
        have frameA : Frame H after (StreamRoot (.in_gzstate_strm i)) :=
          frame_trans (.in_gzstate_strm i) (frame_put (.in_gzstate_strm i) zp hf)
            (failure_frame (wrapCode p.wrap) p.wbits p.memLevel (.in_gzstate_strm i) zp m hfP)
        have liveA : ∀ x, after.live x ↔ H.live x := fun x => (shp.live x).trans (hshape.live x)
        refine ⟨Z_MEM_ERROR, after, ?_, ⟨_, gA, rfl, fun _ => Or.inl rfl⟩, lA, fun _ =>
          Zlib.Gzwrite.SafeInit.failSlots_of_frame frameA liveA hu (shp.uniq huP) hg gA⟩
        rw [entry, alloc_to_finish hfP hzP haP.1 (by simpa [hp] using firstT)]
        exact hm

end Zlib.Deflate.Proofs.GeneralInit

namespace Zlib.Gzwrite.SafeInit
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

private theorem g_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

private theorem g_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

private theorem g_pure_app {α : Type} (a : α) (fs : Fs) (h : Heap) :
    (pure a : G α) fs h = .ok ((a, fs), h) := rfl

/-! ## Literals -/

set_option maxRecDepth 20000 in
theorem oom_cstring (H : Heap) {k : Nat} (hk : strIndex "out of memory" = some k) :
    ∃ t, CString H (.ref (.str k) 0) t := by
  have hb : strBytes "out of memory" =
      #[111, 117, 116, 32, 111, 102, 32, 109, 101, 109, 111, 114, 121, 0] := by
    decide +kernel
  have hg : Space.get H (BRef.str k) =
      some #[111, 117, 116, 32, 111, 102, 32, 109, 101, 109, 111, 114, 121, 0] := by
    have he := strLitRef_get (h := H) hk
    rw [hb] at he
    exact he
  exact ⟨[111, 117, 116, 32, 111, 102, 32, 109, 101, 109, 111, 114, 121],
    Or.inr ⟨.str k, 0, _, rfl, hg, by decide, by decide⟩, by decide, by decide⟩

theorem version_index : strIndex ZLIB_VERSION = some 57 := by decide +kernel

set_option maxRecDepth 100000 in
theorem version_value (H : Heap) : VersionValue H (.ref (.str 57) 0) (some 49) := by
  have hg : Space.get H (BRef.str 57) = some (strBytes ZLIB_VERSION) := strLitRef_get version_index
  exact Or.inr ⟨49, rfl, Or.inr ⟨.str 57, 0, strBytes ZLIB_VERSION, rfl, hg, by decide, by decide⟩⟩

/-! ## The ledger and the record write -/

/-- The ledger of a `gz_init` path, with no grab: a block owned after was owned before, or is fresh
(`h.nextBlk ≤ b`), hence not live before. -/
theorem ledger {h F : Heap} {i : Nat} {s sf : GzState}
    (own : ∀ b, GzOwned h i s b → GzOwned F i sf b) (grow : ∀ b, h.live b → F.live b)
    (new : ∀ b, F.live b → h.live b ∨ GzOwned F i sf b) (ownLive : ∀ b, GzOwned F i sf b → F.live b)
    (fr : Fresh h) (fresh : ∀ b, GzOwned F i sf b → GzOwned h i s b ∨ h.nextBlk ≤ b) :
    LiveChange h F (fun b => GzOwned F i sf b ∧ ¬ h.live b)
      (fun b => GzOwned h i s b ∧ ¬ GzOwned F i sf b) ∧
    (∀ b, GzOwned F i sf b → GzOwned h i s b ∨ ¬ h.live b) := by
  refine ⟨?_, fun b o => (fresh b o).imp_right fun hb hl => absurd (Fresh.lt fr hl) (by omega)⟩
  intro b
  constructor
  · intro hl
    by_cases hh : h.live b
    · exact Or.inl ⟨hh, fun hn => hn.2 (own b hn.1)⟩
    · rcases new b hl with l | o
      · exact absurd l hh
      · exact Or.inr ⟨o, hh⟩
  · rintro (⟨hh, _⟩ | ⟨o, _⟩)
    · exact grow b hh
    · exact ownLive b o

theorem frame_setS (H : Heap) (i : Nat) (t : GzState) :
    Frame H (Zlib.Gzlib.Spec.setS H i t) (fun x => x = i) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun x _ hn => ?_⟩
  simp [Zlib.Gzlib.Spec.setS, upd_ne _ _ _ _ hn]

theorem streamOwned_deflate {F : Heap} {r : ZStreamRef} {z : ZStream} {k : Nat} {d : DeflateState}
    (hz : r.get F = some z) (hst : z.state = some (.deflate k)) (hd : F.dstates k = some d) (b : Nat) :
    StreamOwned F r b ↔ DeflateOwned k d b := by
  unfold StreamOwned
  rw [hz]
  constructor
  · rintro ⟨z0, e, (⟨k', s', hs', _, _⟩ | ⟨k', s', hs', hd', ho⟩)⟩
    · cases e
      rw [hst] at hs'
      cases hs'
    · cases e
      rw [hst] at hs'
      cases hs'
      rw [hd] at hd'
      cases hd'
      exact ho
  · intro ho
    exact ⟨z, rfl, Or.inr ⟨k, d, hst, hd, ho⟩⟩

theorem streamOwned_none {F : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get F = some z) (hst : z.state = none) (b : Nat) : ¬ StreamOwned F r b := by
  unfold StreamOwned
  rw [hz]
  rintro ⟨z0, e, (⟨k', s', hs', _, _⟩ | ⟨k', s', hs', _, _⟩)⟩
  · cases e
    rw [hst] at hs'
    cases hs'
  · cases e
    rw [hst] at hs'
    cases hs'

theorem write_ne_read : ¬ (GZ_WRITE = GZ_READ) := by decide

/-! ## The invariant on the failure paths (no buffer kept) -/

theorem inv_size0 {h H : Heap} {i : Nat} {s : GzState} {pin pout : BPtr} {z : ZStream}
    (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0)
    (ht : H.gzstates i = some { s with «in» := pin, out := pout, strm := z })
    (hav : z.avail_in = 0)
    (fresh : Fresh H) (uniq : Zlib.Gzlib.Spec.Uniq H) (glob : LibraryGlobals H)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit H)
    (same : ∀ x, h.live x → x ≠ i → H.bytes x = h.bytes x ∧ H.ro x = h.ro x)
    (live : ∀ x, h.live x → H.live x)
    (hst : z.state = none) :
    GzInv H i { s with «in» := pin, out := pout, strm := z } := by
  have cm := inv.common
  have wr := inv.writer hm
  have nso : ∀ b, ¬ StreamOwned H (gzStrm i) b :=
    streamOwned_none (by simp [gzStrm, ZStreamRef.get, ht]) hst
  obtain ⟨pb, hpb, lpb, npb⟩ := path_blk cm
  have hown : ∀ b, GzOwned H i { s with «in» := pin, out := pout, strm := z } b ↔ GzOwned h i s b := by
    intro b
    rw [owned0 (s := { s with «in» := pin, out := pout, strm := z }) hsz, owned0 hsz]
  have hptrs : ownedPtrs { s with «in» := pin, out := pout, strm := z } = ownedPtrs s := by
    simp [ownedPtrs, hsz]
  refine ⟨⟨ht, cm.mode, fresh, uniq, glob, fit, ?_, ?_, cm.memerr, cm.want, Or.inl hsz, ?_, ?_, cm.pos, ?_,
    cm.nullHave, nso i⟩, fun hr => absurd (hm.symm.trans hr) write_ne_read, fun _ => ⟨wr.have0, wr.direct, wr.reset,
    fun _ => hst, fun h0 => absurd hsz h0, Or.inl hav, fun _ h0 => absurd hsz h0, fun _ h0 => absurd hsz h0,
    fun _ => hst⟩⟩
  · obtain ⟨p, c, m⟩ := cm.path
    have e := same pb lpb npb
    exact ⟨p, cstring_transport hpb e.1 c, malloc_transport hpb e.1 e.2 m⟩
  · rcases cm.msg with hn | ⟨q, c, m⟩
    · exact Or.inl hn
    · rcases msg_blk cm with hn | ⟨mb, hmb, lmb, nmb⟩
      · exact Or.inl hn
      · have e := same mb lmb nmb
        exact Or.inr ⟨q, cstring_transport hmb e.1 c, malloc_transport hmb e.1 e.2 m⟩
  · rw [hptrs]
    exact ⟨cm.distinct.1, fun p hp b hb => ⟨(cm.distinct.2 p hp b hb).1, nso b⟩⟩
  · intro b hb
    have ho := (hown b).1 hb
    rcases (owned0 hsz b).1 ho with e | e | e
    · subst e
      exact live_of_gz ht
    · exact live b (cm.live b ho)
    · exact live b (cm.live b ho)
  · rcases cm.next with hn | ⟨b, off, a, he, hbi, hnm, ho, hb, hle⟩
    · exact Or.inl hn
    · exact Or.inr ⟨b, off, a, he, hbi, hnm, (hown b).2 ho, by rw [(same b (cm.live b ho) hbi).1]; exact hb, hle⟩

/-! ## The `gz_error` tail of the failure paths -/

theorem err_tail {h H : Heap} {i k : Nat} {s : GzState} {pin pout : BPtr} {z : ZStream} (fs : Fs)
    (hfs : FileSystem fs) (hk : strIndex "out of memory" = some k)
    (inv : GzInv h i s) (hsz : s.size = 0)
    (invH : GzInv H i { s with «in» := pin, out := pout, strm := z })
    (frame : Frame h H (fun x => x = i)) (live : ∀ x, H.live x ↔ h.live x) :
    ∃ after, Zlib.Gzlib.gz_error (gzSt i) Z_MEM_ERROR (.ref (.str k) 0) H = .ok ((), after) ∧
      GzPost h i s [] fs after GzInv := by
  have cm := inv.common
  obtain ⟨t, ct⟩ := oom_cstring H hk
  obtain ⟨after, s', run, invA, eq, -, frameE, liveE, newMsg⟩ :=
    GzInv.gz_error invH Z_MEM_ERROR (.ref (.str k) 0) (Or.inr ⟨t, ct, fun b hb => by simp [ByteRoot] at hb⟩)
  have hmode : s'.mode = s.mode := by
    have := congrArg GzState.mode eq
    simpa using this
  have hfd : s'.fd = s.fd := by
    have := congrArg GzState.fd eq
    simpa using this
  have hpath : s'.path = s.path := by
    have := congrArg GzState.path eq
    simpa using this
  have hsz' : s'.size = 0 := by
    have := congrArg GzState.size eq
    simp only at this
    rw [this, hsz]
  refine ⟨after, run, hfs, s', invA, hmode, hfd, ?_, ?_, ?_⟩
  · refine ⟨?_, fun region hr => by simp at hr⟩
    show Frame h after (GzOwned h i s)
    refine frame_mono (frame_trans frame frameE) (fun x hx => ?_)
    rcases hx with e | e | e
    · exact (owned0 hsz x).2 (Or.inl e)
    · exact (owned0 hsz x).2 (Or.inl e)
    · exact (owned0 hsz x).2 (Or.inr (Or.inr (msg_of_blkOf cm e)))
  · intro b
    have own1 : GzOwned after i s' b ↔ b = i ∨ s.path = .ref (.blk b) 0 ∨ s'.msg = .ref (.blk b) 0 := by
      rw [owned0 hsz' b, hpath]
    constructor
    · intro ha
      by_cases ho : GzOwned after i s' b
      · by_cases hl : h.live b
        · exact Or.inl ⟨hl, fun hn => hn.2 ho⟩
        · exact Or.inr ⟨ho, hl⟩
      · left
        rcases (liveE b).1 ha with ⟨hH, hnm⟩ | ⟨hnew, _⟩
        · refine ⟨(live b).1 hH, fun hn => ?_⟩
          rcases (owned0 hsz b).1 hn.1 with e | e | e
          · exact ho (own1.2 (Or.inl e))
          · exact ho (own1.2 (Or.inr (Or.inl e)))
          · exact hnm (show blkOf s.msg = some b by rw [e]; rfl)
        · exact absurd (own1.2 (Or.inr (Or.inr (msg_of_blkOf invA.common hnew)))) ho
    · rintro (⟨hl, hn⟩ | ⟨ho, _⟩)
      · by_cases ho : GzOwned after i s' b
        · exact invA.common.live b ho
        · apply (liveE b).2
          exact Or.inl ⟨(live b).2 hl, fun e =>
            hn ⟨(owned0 hsz b).2 (Or.inr (Or.inr (msg_of_blkOf cm e))), ho⟩⟩
      · exact invA.common.live b ho
  · intro b ho
    rcases (owned0 hsz' b).1 ho with e | e | e
    · exact Or.inl ((owned0 hsz b).2 (Or.inl e))
    · exact Or.inl ((owned0 hsz b).2 (Or.inr (Or.inl (by rw [← hpath]; exact e))))
    · exact Or.inr fun hl => newMsg b (by rw [e]; rfl) ((live b).2 hl)

/-! ## The failure tails with an extended heap -/

theorem inv_ext {h H : Heap} {i : Nat} {s : GzState} {pin pout : BPtr} {z : ZStream}
    (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0)
    (E : Ext h H i { s with «in» := pin, out := pout, strm := z }) (hav : z.avail_in = 0)
    (hst : z.state = none) : GzInv H i { s with «in» := pin, out := pout, strm := z } := by
  have hs := inv.common.record
  have fr := inv.common.fresh
  exact inv_size0 inv hm hsz E.recd hav (E.fresh' hs fr) (E.uniq hs fr inv.common.uniq)
    (E.globals inv.common.globals) (E.fit inv.common.fit) (fun x hl xi => E.same fr x hl xi)
    (fun x hl => (E.live_iff hs fr x).2 (Or.inl hl)) hst

theorem err_run {h H A : Heap} {i k : Nat} {s : GzState} {pin pout : BPtr} {z : ZStream} {u : Unit} (fs : Fs)
    (run : Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR (.ref (.str k) 0) H = .ok (u, A))
    (hfs : FileSystem fs) (hk : strIndex "out of memory" = some k) (inv : GzInv h i s) (hm : s.mode = GZ_WRITE)
    (hsz : s.size = 0) (E : Ext h H i { s with «in» := pin, out := pout, strm := z }) (hav : z.avail_in = 0)
    (hst : z.state = none) (free : ∀ x, h.nextBlk ≤ x → H.bytes x = none) :
    GzPost h i s [] fs A GzInv := by
  have hs := inv.common.record
  have fr := inv.common.fresh
  have live : ∀ x, H.live x ↔ h.live x := fun x =>
    (E.live_iff hs fr x).trans ⟨fun o => o.elim id (fun ⟨hx, n⟩ => absurd (free x hx) n), Or.inl⟩
  obtain ⟨A', run', post⟩ := err_tail fs hfs hk inv hsz (inv_ext inv hm hsz E hav hst) (E.frame fr) live
  have e := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  rw [e.2]
  exact post

theorem err_noerr {h H : Heap} {i k : Nat} {s : GzState} {pin pout : BPtr} {z : ZStream} {e : Fault} (fs : Fs)
    (run : Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR (.ref (.str k) 0) H = .error e)
    (hfs : FileSystem fs) (hk : strIndex "out of memory" = some k) (inv : GzInv h i s) (hm : s.mode = GZ_WRITE)
    (hsz : s.size = 0) (E : Ext h H i { s with «in» := pin, out := pout, strm := z }) (hav : z.avail_in = 0)
    (hst : z.state = none) (free : ∀ x, h.nextBlk ≤ x → H.bytes x = none) : False := by
  have hs := inv.common.record
  have fr := inv.common.fresh
  have live : ∀ x, H.live x ↔ h.live x := fun x =>
    (E.live_iff hs fr x).trans ⟨fun o => o.elim id (fun ⟨hx, n⟩ => absurd (free x hx) n), Or.inl⟩
  obtain ⟨A', run', -⟩ := err_tail fs hfs hk inv hsz (inv_ext inv hm hsz E hav hst) (E.frame fr) live
  have e := run.symm.trans run'
  cases e

/-! ## The direct writer: `in` only -/

theorem owned_mono {h X : Heap} {i : Nat} {s t : GzState} (hsz : s.size = 0) (hp : t.path = s.path)
    (hmsg : t.msg = s.msg) {b : Nat} (o : GzOwned h i s b) : GzOwned X i t b := by
  rcases (owned0 hsz b).1 o with e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl (hp.trans e))
  · exact Or.inr (Or.inr (Or.inl (hmsg.trans e)))

/-- The record of a direct writer after `gz_init`. -/
def dRec (h : Heap) (s : GzState) : GzState :=
  { s with «in» := .ref (.blk h.nextBlk) 0, strm := { s.strm with next_in := .null }, size := s.want }

theorem size_bound {s : GzState} (hW : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31) :
    2 * s.want.toNat < ZlibF.PlatformMemory.byteObjectLimit := by
  unfold ZlibF.PlatformMemory.byteObjectLimit
  have : (2 : Nat) ^ 31 = 2147483648 := by decide
  have : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  omega

theorem direct_final {h : Heap} {i : Nat} {s : GzState} {n1 : Nat} (fs : Fs) (hfs : FileSystem fs)
    (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0) (hd : ¬ s.direct = 0)
    (hn1 : n1 = 2 * s.want.toNat) :
    GzPost h i s [] fs (Zlib.Gzlib.Spec.setS (aHeap h n1) i (dRec h s)) GzInv := by
  have cm := inv.common
  have wr := inv.writer hm
  have hs := cm.record
  have fr := cm.fresh
  have il := rec_lt hs fr
  have hW := cm.want
  have hW0 : s.want ≠ 0 := fun e => by rw [e] at hW; simp at hW
  have hlim : n1 < ZlibF.PlatformMemory.byteObjectLimit := by rw [hn1]; exact size_bound hW
  have hav0 : s.strm.avail_in = 0 := avail_zero wr hsz
  have E : Ext h (Zlib.Gzlib.Spec.setS (aHeap h n1) i (dRec h s)) i (dRec h s) :=
    Ext.setS (Ext.alloc (Ext.base hs fr) n1 hlim) (dRec h s)
  have bnb : (Zlib.Gzlib.Spec.setS (aHeap h n1) i (dRec h s)).bytes h.nextBlk =
      some (Array.ofFn (n := n1) fun j => Junk.of (h.garbage h.nalloc j.val)) := by
    simp [Zlib.Gzlib.Spec.setS, aHeap]
  have ronb : (Zlib.Gzlib.Spec.setS (aHeap h n1) i (dRec h s)).ro h.nextBlk = false := by
    simp [Zlib.Gzlib.Spec.setS, aHeap]
  have live : ∀ x, (Zlib.Gzlib.Spec.setS (aHeap h n1) i (dRec h s)).live x ↔ h.live x ∨ x = h.nextBlk := by
    intro x
    rw [E.live_iff hs fr x]
    constructor
    · rintro (l | ⟨hx, n⟩)
      · exact Or.inl l
      · right
        by_cases e : x = h.nextBlk
        · exact e
        · exact absurd (E.fresh x (show h.nextBlk + 1 ≤ x by omega)) n
    · rintro (l | e)
      · exact Or.inl l
      · subst e
        exact Or.inr ⟨Nat.le_refl _, by rw [bnb]; simp⟩
  have so : ∀ b, ¬ StreamOwned (Zlib.Gzlib.Spec.setS (aHeap h n1) i (dRec h s)) (gzStrm i) b :=
    streamOwned_none (by simp [gzStrm, ZStreamRef.get, E.recd]) (show (dRec h s).strm.state = none from wr.transparent hd)
  obtain ⟨pb, hpb, lpb, npb⟩ := path_blk cm
  have mode1 : ¬ ((dRec h s).mode = GZ_READ ∨ (dRec h s).direct = 0) :=
    fun o => o.elim (fun e => write_ne_read (hm.symm.trans e)) hd
  have invX : GzInv (Zlib.Gzlib.Spec.setS (aHeap h n1) i (dRec h s)) i (dRec h s) := by
    refine ⟨⟨E.recd, Or.inr hm, E.fresh' hs fr, E.uniq hs fr cm.uniq, E.globals cm.globals, E.fit cm.fit,
      ?_, ?_, cm.memerr, cm.want, Or.inr rfl, ?_, ?_, cm.pos, ?_, cm.nullHave, so i⟩,
      fun hr => absurd (hm.symm.trans hr) write_ne_read, fun _ => ⟨wr.have0, wr.direct, wr.reset,
      fun h0 => absurd h0 hW0, fun _ => ⟨⟨h.nextBlk, _, rfl, bnb, ronb, by simp [hn1, dRec]⟩,
        fun h0 => absurd h0 hd⟩,
      Or.inl hav0, fun h0 => absurd h0 hd,
      fun h0 => absurd h0 hd, fun _ => wr.transparent hd⟩⟩
    · obtain ⟨p, c, m⟩ := cm.path
      have e := E.same fr pb lpb npb
      exact ⟨p, cstring_transport hpb e.1 c, malloc_transport hpb e.1 e.2 m⟩
    · rcases cm.msg with hn | ⟨q, c, m⟩
      · exact Or.inl hn
      · rcases msg_blk cm with hn | ⟨mb, hmb, lmb, nmb⟩
        · exact Or.inl hn
        · have e := E.same fr mb lmb nmb
          exact Or.inr ⟨q, cstring_transport hmb e.1 c, malloc_transport hmb e.1 e.2 m⟩
    · have hp : ownedPtrs (dRec h s) = [s.path, s.msg, .ref (.blk h.nextBlk) 0] := by
        simp [ownedPtrs, dRec, hW0, hd, hm, write_ne_read]
      rw [hp]
      refine ⟨?_, ?_⟩
      · have lt1 := Fresh.lt fr lpb
        rcases msg_blk cm with hn | ⟨mb, hmb, lmb, nmb⟩
        · rw [hpb, hn]
          change [pb, h.nextBlk].Nodup
          exact nodup2 (by omega)
        · have old := cm.distinct.1
          simp [ownedPtrs, hsz, hpb, hmb, blkOf] at old
          have lt2 := Fresh.lt fr lmb
          simp [hpb, hmb, blkOf]
          omega
      · intro p hp' b hb
        refine ⟨?_, so b⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl
        · exact (cm.distinct.2 s.path (by simp [ownedPtrs]) b hb).1
        · exact (cm.distinct.2 s.msg (by simp [ownedPtrs]) b hb).1
        · simp [blkOf] at hb
          omega
    · intro b o
      rcases o with e | e | e | ⟨_, e | ⟨m, _⟩⟩
      · subst e
        exact live_of_gz E.recd
      · exact (live b).2 (Or.inl (cm.live b ((owned0 hsz b).2 (Or.inr (Or.inl e)))))
      · exact (live b).2 (Or.inl (cm.live b ((owned0 hsz b).2 (Or.inr (Or.inr e)))))
      · simp [dRec] at e
        exact (live b).2 (Or.inr e.symm)
      · exact absurd m mode1
    · rcases cm.next with hn | ⟨b, off, a, he, hbi, hnm, ho, hb, hle⟩
      · exact Or.inl hn
      · refine Or.inr ⟨b, off, a, he, hbi, hnm, owned_mono (t := dRec h s) hsz rfl rfl ho, ?_, hle⟩
        rw [(E.same fr b (cm.live b ho) hbi).1]
        exact hb
  refine ⟨hfs, dRec h s, invX, rfl, rfl,
    ⟨frame_mono (E.frame fr) (fun x e => (owned0 hsz x).2 (Or.inl e)), fun _ hr => by simp at hr⟩,
    ledger (fun b o => owned_mono (X := Zlib.Gzlib.Spec.setS (aHeap h n1) i (dRec h s)) (t := dRec h s) hsz rfl rfl o)
      (fun b l => (live b).2 (Or.inl l)) (fun b l => ?_) invX.common.live fr (fun b o => ?_)⟩
  · rcases (live b).1 l with l' | e
    · exact Or.inl l'
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hW0, Or.inl (by rw [e]; rfl)⟩)))
  · -- no grab: the only new owned block is `in`, at `h.nextBlk`
    rcases o with e | e | e | ⟨_, e | ⟨m, _⟩⟩
    · exact Or.inl ((owned0 hsz b).2 (Or.inl e))
    · exact Or.inl ((owned0 hsz b).2 (Or.inr (Or.inl e)))
    · exact Or.inl ((owned0 hsz b).2 (Or.inr (Or.inr e)))
    · simp [dRec] at e
      exact Or.inr (by omega)
    · exact absurd m mode1

/-! ## The compressing writer: `in`, `out` and the deflate state -/

/-- The record after `in` is allocated. -/
def s1 (h : Heap) (s : GzState) : GzState := { s with «in» := .ref (.blk h.nextBlk) 0 }

/-- The stream after `strm->zalloc = strm->zfree = strm->opaque = NULL`. -/
def zs3 (s : GzState) : ZStream := { s.strm with zalloc := .null, zfree := .null, «opaque» := .null }

/-- The record when `deflateInit2_` is called. -/
def s3 (h : Heap) (s : GzState) : GzState :=
  { s with «in» := .ref (.blk h.nextBlk) 0, out := .ref (.blk (h.nextBlk + 1)) 0, strm := zs3 s }

/-- The heap when `deflateInit2_` is called. -/
def heap3 (h : Heap) (i : Nat) (s : GzState) : Heap :=
  Zlib.Gzlib.Spec.setS (aHeap (Zlib.Gzlib.Spec.setS (aHeap h (s.want.toNat <<< 1 % 4294967296)) i (s1 h s))
    s.want.toNat) i (s3 h s)

/-- The heap when `out` cannot be allocated, after `in` is freed. -/
def heapOF (h : Heap) (i : Nat) (s : GzState) : Heap :=
  dHeap (Zlib.Gzlib.Spec.setS (fHeap (Zlib.Gzlib.Spec.setS (aHeap h (s.want.toNat <<< 1 % 4294967296)) i (s1 h s)))
    i { s with «in» := .ref (.blk h.nextBlk) 0, out := .null }) h.nextBlk

/-- The record after a successful `gz_init` of a compressing writer. -/
def sf (h : Heap) (s : GzState) (z' : ZStream) : GzState :=
  { s with
    «in» := .ref (.blk h.nextBlk) 0, out := .ref (.blk (h.nextBlk + 1)) 0,
    strm := { z' with next_in := .null, avail_out := s.want, next_out := .ref (.blk (h.nextBlk + 1)) 0 },
    size := s.want, x := { s.x with next := .ref (.blk (h.nextBlk + 1)) 0 } }

/-- The record after `deflateInit2_` returned, with the stream it left. -/
def s3z (h : Heap) (s : GzState) (z' : ZStream) : GzState :=
  { s with «in» := .ref (.blk h.nextBlk) 0, out := .ref (.blk (h.nextBlk + 1)) 0, strm := z' }

section Heap3
variable {h : Heap} {i : Nat} {s : GzState}

theorem shift_eq (hW : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31) :
    s.want.toNat <<< 1 % 4294967296 = 2 * s.want.toNat := by
  rw [Nat.shiftLeft_eq, Nat.pow_one]
  have : (2 : Nat) ^ 31 = 2147483648 := by decide
  omega

theorem heap3_ext (hs : h.gzstates i = some s) (fr : Fresh h) (hW : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31) :
    Ext h (heap3 h i s) i (s3 h s) :=
  Ext.setS (Ext.alloc (Ext.setS (Ext.alloc (Ext.base hs fr) _ (by rw [shift_eq hW]; exact size_bound hW))
    (s1 h s)) _ (by have := size_bound hW; omega)) (s3 h s)

theorem heap3_next : (heap3 h i s).nextBlk = h.nextBlk + 2 := rfl

theorem heap3_b0 (hW : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31) :
    ∃ a, (heap3 h i s).bytes h.nextBlk = some a ∧ a.size = 2 * s.want.toNat := by
  have hnn : h.nextBlk ≠ h.nextBlk + 1 := by omega
  simp [heap3, Zlib.Gzlib.Spec.setS, aHeap, hnn, shift_eq hW]

theorem heap3_b1 : ∃ a, (heap3 h i s).bytes (h.nextBlk + 1) = some a ∧ a.size = s.want.toNat := by
  simp [heap3, Zlib.Gzlib.Spec.setS, aHeap]

theorem heap3_r0 : (heap3 h i s).ro h.nextBlk = false := by
  have hnn : h.nextBlk ≠ h.nextBlk + 1 := by omega
  simp [heap3, Zlib.Gzlib.Spec.setS, aHeap, hnn]

theorem heap3_r1 : (heap3 h i s).ro (h.nextBlk + 1) = false := by
  simp [heap3, Zlib.Gzlib.Spec.setS, aHeap]

theorem heap3_rec : (heap3 h i s).gzstates i = some (s3 h s) := by
  simp [heap3]

theorem heap3_live (hs : h.gzstates i = some s) (fr : Fresh h) (hW : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31)
    (x : Nat) : (heap3 h i s).live x ↔ h.live x ∨ x = h.nextBlk ∨ x = h.nextBlk + 1 := by
  have E3 := heap3_ext hs fr hW
  rw [E3.live_iff hs fr x]
  constructor
  · rintro (l | ⟨hx, n⟩)
    · exact Or.inl l
    · right
      by_cases e0 : x = h.nextBlk
      · exact Or.inl e0
      · by_cases e1 : x = h.nextBlk + 1
        · exact Or.inr e1
        · exact absurd (E3.fresh x (by rw [heap3_next]; omega)) n
  · rintro (l | e | e)
    · exact Or.inl l
    · subst e
      obtain ⟨a, ha, _⟩ := heap3_b0 (i := i) hW
      exact Or.inr ⟨Nat.le_refl _, by rw [ha]; simp⟩
    · subst e
      obtain ⟨a, ha, _⟩ := heap3_b1 (h := h) (i := i) (s := s)
      exact Or.inr ⟨Nat.le_succ _, by rw [ha]; simp⟩

end Heap3

/-- `deflateInit2_` on the record's stream: the facts the rest of `gz_init` needs. -/
theorem init_facts {H A : Heap} {i : Nat} {g : GzState} {rc level strategy : Int32}
    (run : Zlib.Deflate.deflateInit2_ (some (.in_gzstate_strm i)) level Z_DEFLATED (MAX_WBITS + 16) DEF_MEM_LEVEL
      strategy (.ref (.str 57) 0) 112 H = .ok (rc, A))
    (hg : H.gzstates i = some g) (fr : Fresh H) (u : Zlib.Gzlib.Spec.Uniq H) (gl : LibraryGlobals H)
    (ha : DefaultOrNull g.strm) :
    (∃ z', A.gzstates i = some { g with strm := z' } ∧ z'.avail_in = g.strm.avail_in ∧
        (rc ≠ Z_OK → z'.state = none ∨ z'.state = g.strm.state)) ∧
      A.libcErrorBorrow = H.libcErrorBorrow ∧
      (rc ≠ Z_OK → FailSlots H A i) ∧
      (rc = Z_OK → ∃ p, DeflateInitial H A (gzStrm i) p) := by
  obtain ⟨rc', A', run', rec', libc', fail'⟩ := Zlib.Deflate.Proofs.GeneralInit.gz_strm_init_run hg fr u gl ha
    (version_value H) level Z_DEFLATED (MAX_WBITS + 16) DEF_MEM_LEVEL strategy
  unfold C.run at run'
  have e := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  subst e1 e2
  refine ⟨rec', libc', fail', fun hok => ?_⟩
  subst hok
  obtain ⟨rc2, A2, run2, post⟩ := Zlib.Deflate.Proofs.GeneralInit.init2_main level Z_DEFLATED (MAX_WBITS + 16)
    DEF_MEM_LEVEL strategy H (gzStrm i) g.strm (.ref (.str 57) 0) fr u gl
    (by simp [gzStrm, ZStreamRef.get, hg]) ha (version_value H)
  unfold C.run at run2
  have e2 := run.symm.trans run2
  simp only [Except.ok.injEq, Prod.mk.injEq] at e2
  obtain ⟨f1, f2⟩ := e2
  subst f1 f2
  revert post
  split
  · intro post
    exact absurd post.1 (by decide)
  · intro post
    split at post
    · exact absurd post.1 (by decide)
    · obtain ⟨-, post⟩ := post
      split at post
      · exact ⟨_, post.2⟩
      · exact absurd post.1 (by decide)

theorem init_noerr {H : Heap} {i : Nat} {g : GzState} {e : Fault} {level strategy : Int32}
    (run : Zlib.Deflate.deflateInit2_ (some (.in_gzstate_strm i)) level Z_DEFLATED (MAX_WBITS + 16) DEF_MEM_LEVEL
      strategy (.ref (.str 57) 0) 112 H = .error e)
    (hg : H.gzstates i = some g) (fr : Fresh H) (u : Zlib.Gzlib.Spec.Uniq H) (gl : LibraryGlobals H)
    (ha : DefaultOrNull g.strm) : False := by
  obtain ⟨rc', A', run', -⟩ := Zlib.Deflate.Proofs.GeneralInit.gz_strm_init_run hg fr u gl ha
    (version_value H) level Z_DEFLATED (MAX_WBITS + 16) DEF_MEM_LEVEL strategy
  unfold C.run at run'
  have e' := run.symm.trans run'
  cases e'

theorem lim_bound {n : Nat} (hn : n ≤ 131072) : n < ZlibF.PlatformMemory.byteObjectLimit := by
  unfold ZlibF.PlatformMemory.byteObjectLimit
  have : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  omega

/-- The success path of a compressing writer. -/
theorem deflate_final {h A : Heap} {i : Nat} {s : GzState} {z' : ZStream} {p : ZlibF.Spec.Api.DeflParams}
    {r : GzState} (fs : Fs) (hfs : FileSystem fs)
    (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0) (hd : s.direct = 0)
    (run3 : Zlib.Deflate.deflateInit2_ (some (.in_gzstate_strm i)) s.level Z_DEFLATED (MAX_WBITS + 16) DEF_MEM_LEVEL
      s.strategy (.ref (.str 57) 0) 112 (heap3 h i s) = .ok (Z_OK, A))
    (init3 : DeflateInitial (heap3 h i s) A (gzStrm i) p)
    (recA : A.gzstates i = some (s3z h s z')) (avA : z'.avail_in = s.strm.avail_in)
    (libcA : A.libcErrorBorrow = (heap3 h i s).libcErrorBorrow) (hr : r = sf h s z') :
    GzPost h i s [] fs (Zlib.Gzlib.Spec.setS A i r) GzInv := by
  subst hr
  have cm := inv.common
  have wr := inv.writer hm
  have hs := cm.record
  have fr := cm.fresh
  have il := rec_lt hs fr
  have hW := cm.want
  have hW0 : s.want ≠ 0 := fun e => by rw [e] at hW; simp at hW
  have hav := avail_zero wr hsz
  have E3 := heap3_ext hs fr hW
  have live3' := heap3_live hs fr hW
  obtain ⟨zA, sd, good, -, -, -, -, -, -, -, -, -, -, -, hgz, -, -, -, frame3, live3, owned3⟩ := init3
  have getA : (gzStrm i).get A = some z' := by simp [gzStrm, ZStreamRef.get, recA, s3z]
  have hzA : zA = z' := by
    have := good.live.hz
    rw [getA] at this
    exact (Option.some.inj this).symm
  subst hzA
  have zst : zA.state = some (.deflate (heap3 h i s).nextBlk) := good.live.zst
  have dsA : A.dstates (heap3 h i s).nextBlk = some sd := good.live.hs
  have uA : Zlib.Gzlib.Spec.Uniq A := good.uniq
  have ownedD : ∀ x, DeflateOwned (heap3 h i s).nextBlk sd x ↔ h.nextBlk + 2 ≤ x ∧ x < h.nextBlk + 7 := by
    intro x
    (rw [owned3 x, heap3_next]) <;> omega
  have liveA : ∀ x, A.live x ↔ (heap3 h i s).live x ∨ (h.nextBlk + 2 ≤ x ∧ x < h.nextBlk + 7) := by
    intro x
    rw [live3 x, ← ownedD x]
    simp only [not_false_eq_true, and_true]
  have oldA : ∀ x, h.live x → x ≠ i →
      A.bytes x = h.bytes x ∧ A.ro x = h.ro x ∧ A.dstates x = h.dstates x := by
    intro x hl xi
    have l3 : (heap3 h i s).live x := (live3' x).2 (Or.inl hl)
    obtain ⟨e1, -, -, -, e5, -, -, e8⟩ := frame3.2.2.2.2.2 x l3 xi
    have xl := Fresh.lt fr hl
    exact ⟨e1.trans (E3.bytes x xl), e8.trans (E3.ro x xl hl xi), e5.trans (E3.dstates x)⟩
  have newA : ∀ x, (x = h.nextBlk ∨ x = h.nextBlk + 1) →
      A.bytes x = (heap3 h i s).bytes x ∧ A.ro x = (heap3 h i s).ro x := by
    intro x hx
    have l3 : (heap3 h i s).live x := (live3' x).2 (Or.inr hx)
    have xi : x ≠ i := by omega
    obtain ⟨e1, -, -, -, -, -, -, e8⟩ := frame3.2.2.2.2.2 x l3 xi
    exact ⟨e1, e8⟩
  obtain ⟨w, pq, q, bb, blocks⟩ := good.inv.blocks
  have wsz : 2 ^ sd.w_bits.toNat ≤ 32768 := by
    have := Nat.pow_le_pow_right (show 2 > 0 by decide) good.inv.wbits_hi
    simpa using this
  have hsz16 : 2 ^ sd.hash_bits.toNat ≤ 65536 := by
    have := Nat.pow_le_pow_right (show 2 > 0 by decide) good.inv.hbits_hi
    simpa using this
  have glF0 : LibraryGlobals A := by
    unfold LibraryGlobals
    rw [← frame3.1, E3.static]
    exact cm.globals
  generalize hF : Zlib.Gzlib.Spec.setS A i (sf h s zA) = F
  have Fgz : F.gzstates i = some (sf h s zA) := by rw [← hF]; exact Zlib.Gzlib.Proofs.setS_gz_same A i _
  have Fbytes : F.bytes = A.bytes := by rw [← hF]; rfl
  have Fro : F.ro = A.ro := by rw [← hF]; rfl
  have Fdst : F.dstates = A.dstates := by rw [← hF]; rfl
  have Fstatic : F.static = A.static := by rw [← hF]; rfl
  have Flibc : F.libcErrorBorrow = A.libcErrorBorrow := by rw [← hF]; rfl
  have Fnext : F.nextBlk = A.nextBlk := by rw [← hF]; rfl
  have shapeF : Zlib.Gzlib.Spec.Shape A F := by rw [← hF]; exact Zlib.Gzlib.Proofs.shape_setS recA _
  have liveF : ∀ x, F.live x ↔ A.live x := fun x => Zlib.Gzlib.Proofs.Shape.live shapeF x
  have growF : ∀ x, (heap3 h i s).live x → F.live x := fun x l => (liveF x).2 ((liveA x).2 (Or.inl l))
  have getF : (gzStrm i).get F = some (sf h s zA).strm := by simp [gzStrm, ZStreamRef.get, Fgz]
  have dsF : F.dstates (heap3 h i s).nextBlk = some sd := by rw [Fdst]; exact dsA
  have soF : ∀ b, StreamOwned F (gzStrm i) b ↔ h.nextBlk + 2 ≤ b ∧ b < h.nextBlk + 7 := fun b =>
    (streamOwned_deflate getF zst dsF b).trans (ownedD b)
  have oldF : ∀ x, h.live x → x ≠ i → F.bytes x = h.bytes x ∧ F.ro x = h.ro x := by
    intro x hl xi
    rw [Fbytes, Fro]
    exact ⟨(oldA x hl xi).1, (oldA x hl xi).2.1⟩
  obtain ⟨a0, hb0, hs0⟩ := heap3_b0 (i := i) hW
  obtain ⟨a1, hb1, hs1⟩ := heap3_b1 (h := h) (i := i) (s := s)
  have Fb0 : F.bytes h.nextBlk = some a0 := by rw [Fbytes, (newA _ (Or.inl rfl)).1, hb0]
  have Fb1 : F.bytes (h.nextBlk + 1) = some a1 := by rw [Fbytes, (newA _ (Or.inr rfl)).1, hb1]
  have Fr0 : F.ro h.nextBlk = false := by rw [Fro, (newA _ (Or.inl rfl)).2, heap3_r0]
  have Fr1 : F.ro (h.nextBlk + 1) = false := by rw [Fro, (newA _ (Or.inr rfl)).2, heap3_r1]
  have mode0 : (sf h s zA).mode = GZ_READ ∨ (sf h s zA).direct = 0 := Or.inr hd
  have freshF : Fresh F := Zlib.Gzlib.Proofs.Shape.fresh shapeF Fnext good.fresh
  have uniqF : Zlib.Gzlib.Spec.Uniq F := Zlib.Gzlib.Proofs.Shape.uniq shapeF good.uniq
  have glF : LibraryGlobals F := by
    unfold LibraryGlobals at glF0 ⊢
    rw [Fstatic]
    exact glF0
  have rb : Rebuffer A F (gzStrm i) := by
    refine ⟨freshF, uniqF, glF, ?_, zA, (sf h s zA).strm, getA, getF, rfl⟩
    rw [← hF]
    refine frame_mono (frame_setS A i _) (fun x e o => ?_)
    have := (ownedD x).1 ((streamOwned_deflate getA zst dsA x).1 o)
    omega
  obtain ⟨pb, hpb, lpb, npb⟩ := path_blk cm
  have invF : GzInv F i (sf h s zA) := by
    refine ⟨⟨Fgz, Or.inr hm, freshF, uniqF, glF, ?_, ?_, ?_, cm.memerr, cm.want, Or.inr rfl, ?_, ?_, cm.pos,
      ?_, fun _ => wr.have0, fun o => by have := (soF i).1 o; omega⟩, fun hr => absurd (hm.symm.trans hr) write_ne_read, fun _ => ⟨wr.have0, Or.inl hd,
      wr.reset, fun h0 => absurd h0 hW0, fun _ => ⟨⟨h.nextBlk, a0, rfl, Fb0, Fr0, hs0⟩,
        fun _ => ⟨h.nextBlk + 1, a1, rfl, Fb1, Fr1, hs1⟩⟩,
      Or.inl (show zA.avail_in = 0 from avA.trans hav), fun _ _ => ⟨0, 0, ?_, ?_, ?_, Nat.le_refl _, Nat.zero_le _⟩,
      fun _ _ => ⟨?_, _, _, sd, getF, zst, dsF, hgz⟩, fun h0 => absurd hd h0⟩⟩
    · apply fit_of cm.fit (Fstatic.trans (frame3.1.symm.trans E3.static)) (Flibc.trans (libcA.trans E3.libc))
      · intro x arr e
        rw [Fbytes] at e
        rcases (liveA x).1 (live_of_bytes e) with l3 | ⟨lo, hi⟩
        · rcases (live3' x).1 l3 with lh | e0 | e1
          · by_cases xi : x = i
            · subst xi
              rw [(uniq_gz_only uA recA).1] at e
              cases e
            · exact Or.inl ((oldA x lh xi).1 ▸ e)
          · subst e0
            rw [(newA _ (Or.inl rfl)).1, hb0] at e
            cases e
            right
            rw [hs0]
            exact size_bound hW
          · subst e1
            rw [(newA _ (Or.inr rfl)).1, hb1] at e
            cases e
            right
            rw [hs1]
            have := size_bound hW
            omega
        · rcases (ownedD x).2 ⟨lo, hi⟩ with e0 | e0 | e0 | e0 | e0
          · rw [(uniq_dstates_only uA (by rw [e0]; exact dsA)).1] at e
            cases e
          · rw [blocks.win] at e0
            cases e0
            obtain ⟨a, ha, hsa⟩ := blocks.wa
            rw [ha] at e
            cases e
            right
            rw [hsa, good.inv.wsize]
            exact lim_bound (by omega)
          · rw [blocks.prev] at e0
            cases e0
            obtain ⟨a, ha, _⟩ := blocks.pa
            rw [(uniq_words_only uA ha).1] at e
            cases e
          · rw [blocks.head] at e0
            cases e0
            obtain ⟨a, ha, _⟩ := blocks.qa
            rw [(uniq_words_only uA ha).1] at e
            cases e
          · rw [blocks.pbuf] at e0
            cases e0
            obtain ⟨a, ha, hsa⟩ := blocks.ba
            rw [ha] at e
            cases e
            right
            have l2 := good.inv.lit
            have hh := good.inv.hsize
            rw [hsa]
            exact lim_bound (by omega)
      · intro x d e
        rw [Fdst] at e
        rcases (liveA x).1 (live_of_dstates e) with l3 | ⟨lo, hi⟩
        · rcases (live3' x).1 l3 with lh | e0 | e1
          · by_cases xi : x = i
            · subst xi
              rw [(uniq_gz_only uA recA).2.2.2.2.1] at e
              cases e
            · exact Or.inl ⟨d, (oldA x lh xi).2.2.symm.trans e, rfl⟩
          · subst e0
            have hb := (newA _ (Or.inl rfl)).1.trans hb0
            rw [(uniq_bytes_only uA hb).1] at e
            cases e
          · subst e1
            have hb := (newA _ (Or.inr rfl)).1.trans hb1
            rw [(uniq_bytes_only uA hb).1] at e
            cases e
        · rcases (ownedD x).2 ⟨lo, hi⟩ with e0 | e0 | e0 | e0 | e0
          · subst e0
            rw [dsA] at e
            cases e
            right
            rw [good.inv.wf.2.2.2.2.2]
            exact lim_bound (by omega)
          · rw [blocks.win] at e0
            cases e0
            obtain ⟨a, ha, _⟩ := blocks.wa
            rw [(uniq_bytes_only uA ha).1] at e
            cases e
          · rw [blocks.prev] at e0
            cases e0
            obtain ⟨a, ha, _⟩ := blocks.pa
            rw [(uniq_words_only uA ha).2] at e
            cases e
          · rw [blocks.head] at e0
            cases e0
            obtain ⟨a, ha, _⟩ := blocks.qa
            rw [(uniq_words_only uA ha).2] at e
            cases e
          · rw [blocks.pbuf] at e0
            cases e0
            obtain ⟨a, ha, _⟩ := blocks.ba
            rw [(uniq_bytes_only uA ha).1] at e
            cases e
    · obtain ⟨q, c, m⟩ := cm.path
      have e := oldF pb lpb npb
      exact ⟨q, cstring_transport hpb e.1 c, malloc_transport hpb e.1 e.2 m⟩
    · rcases cm.msg with hn | ⟨q, c, m⟩
      · exact Or.inl hn
      · rcases msg_blk cm with hn | ⟨mb, hmb, lmb, nmb⟩
        · exact Or.inl hn
        · have e := oldF mb lmb nmb
          exact Or.inr ⟨q, cstring_transport hmb e.1 c, malloc_transport hmb e.1 e.2 m⟩
    · have hp : ownedPtrs (sf h s zA) =
          [s.path, s.msg, .ref (.blk h.nextBlk) 0, .ref (.blk (h.nextBlk + 1)) 0] := by
        simp [ownedPtrs, sf, s3, hW0, hd]
      rw [hp]
      refine ⟨?_, ?_⟩
      · have lt1 := Fresh.lt fr lpb
        rcases msg_blk cm with hn | ⟨mb, hmb, lmb, nmb⟩
        · rw [hpb, hn]
          change [pb, h.nextBlk, h.nextBlk + 1].Nodup
          exact nodup3 (by omega) (by omega) (by omega)
        · have old := cm.distinct.1
          simp [ownedPtrs, hsz, hpb, hmb, blkOf] at old
          have lt2 := Fresh.lt fr lmb
          simp [hpb, hmb, blkOf]
          omega
      · intro p hp' b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        have key : b < h.nextBlk + 2 ∧ b ≠ i := by
          rcases hp' with rfl | rfl | rfl | rfl
          · rw [hpb] at hb
            cases hb
            have := Fresh.lt fr lpb
            exact ⟨by omega, npb⟩
          · rcases msg_blk cm with hn | ⟨mb, hmb, lmb, nmb⟩
            · rw [hn] at hb
              cases hb
            · rw [hmb] at hb
              cases hb
              have := Fresh.lt fr lmb
              exact ⟨by omega, nmb⟩
          · cases hb
            exact ⟨by omega, by omega⟩
          · cases hb
            exact ⟨by omega, by omega⟩
        exact ⟨key.2, fun o => by have := (soF b).1 o; omega⟩
    · intro b o
      rcases o with e | e | e | ⟨_, e | ⟨_, e | e⟩⟩
      · subst e
        exact live_of_gz Fgz
      · exact growF b ((live3' b).2 (Or.inl (cm.live b ((owned0 hsz b).2 (Or.inr (Or.inl e))))))
      · exact growF b ((live3' b).2 (Or.inl (cm.live b ((owned0 hsz b).2 (Or.inr (Or.inr e))))))
      · simp [sf, s3] at e
        exact growF b ((live3' b).2 (Or.inr (Or.inl e.symm)))
      · simp [sf, s3] at e
        exact growF b ((live3' b).2 (Or.inr (Or.inr e.symm)))
      · exact (liveF b).2 ((liveA b).2 (Or.inr ((soF b).1 e)))
    · have hnm : blkOf (sf h s zA).msg ≠ some (h.nextBlk + 1) := by
        intro e
        have := Fresh.lt fr (cm.live _ ((owned0 hsz _).2 (Or.inr (Or.inr (msg_of_blkOf cm e)))))
        omega
      exact Or.inr ⟨h.nextBlk + 1, 0, a1, rfl, by omega, hnm,
        Or.inr (Or.inr (Or.inr ⟨hW0, Or.inr ⟨mode0, Or.inl rfl⟩⟩)), Fb1, by simp [sf, wr.have0]⟩
    · simp [sf, s3, padv]
    · simp [sf]
    · simp [sf, s3, padv]
    · have run3' : C.run (Zlib.Deflate.deflateInit2_ (some (gzStrm i)) s.level Z_DEFLATED (MAX_WBITS + 16)
          DEF_MEM_LEVEL s.strategy (.ref (.str 57) 0) 112) (heap3 h i s) = .ok (Z_OK, A) := by
        unfold C.run
        exact run3
      exact .rebuffer (.deflateInit (E3.fresh' hs fr) (E3.uniq hs fr cm.uniq) (E3.globals cm.globals)
        (by simp [gzStrm, ZStreamRef.get, heap3_rec, s3] : (gzStrm i).get (heap3 h i s) = some (zs3 s))
        ⟨Or.inl rfl, Or.inl rfl⟩ (version_value _) run3') rb (fun e => by cases e)
  refine ⟨hfs, sf h s zA, invF, rfl, rfl, ⟨?_, fun _ hr => by simp at hr⟩,
    ledger (fun b o => owned_mono (X := F) (t := sf h s zA) hsz rfl rfl o)
      (fun b l => growF b ((live3' b).2 (Or.inl l))) (fun b l => ?_) invF.common.live fr (fun b o => ?_)⟩
  · show Frame h F (GzOwned h i s)
    have f2 : Frame A F (fun x => x = i) := by rw [← hF]; exact frame_setS A i _
    refine frame_mono (frame_trans (E3.frame fr) (frame_trans frame3 f2)) (fun x hx => ?_)
    rcases hx with e | e | e
    · exact (owned0 hsz x).2 (Or.inl e)
    · exact (owned0 hsz x).2 (Or.inl e)
    · exact (owned0 hsz x).2 (Or.inl e)
  · rcases (liveA b).1 ((liveF b).1 l) with l3 | hr
    · rcases (live3' b).1 l3 with lh | e | e
      · exact Or.inl lh
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hW0, Or.inl (by rw [e]; rfl)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hW0, Or.inr ⟨mode0, Or.inl (by rw [e]; rfl)⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hW0, Or.inr ⟨mode0, Or.inr ((soF b).2 hr)⟩⟩)))
  · -- no grab: the new owned blocks are `in`, `out` and the deflate state, all at or above `h.nextBlk`
    rcases o with e | e | e | ⟨_, e | ⟨_, e | e⟩⟩
    · exact Or.inl ((owned0 hsz b).2 (Or.inl e))
    · exact Or.inl ((owned0 hsz b).2 (Or.inr (Or.inl e)))
    · exact Or.inl ((owned0 hsz b).2 (Or.inr (Or.inr e)))
    · simp [sf] at e
      exact Or.inr (by omega)
    · simp [sf] at e
      exact Or.inr (by omega)
    · exact Or.inr (by have := ((soF b).1 e).1; omega)

/-- The failure path after a failed `deflateInit2_`: `out` and `in` freed, then `gz_error`. -/
theorem fail_tail {h A : Heap} {i k : Nat} {s : GzState} {z' : ZStream} (fs : Fs)
    (hfs : FileSystem fs) (hk : strIndex "out of memory" = some k)
    (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0)
    (F : FailSlots (heap3 h i s) A i) (recA : A.gzstates i = some (s3z h s z'))
    (avA : z'.avail_in = s.strm.avail_in) (stA : z'.state = none ∨ z'.state = s.strm.state)
    (libcA : A.libcErrorBorrow = (heap3 h i s).libcErrorBorrow) :
    (∀ u B, Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR (.ref (.str k) 0)
      (dHeap (dHeap A (h.nextBlk + 1)) h.nextBlk) = .ok (u, B) → GzPost h i s [] fs B GzInv) ∧
    (∀ e, Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR (.ref (.str k) 0)
      (dHeap (dHeap A (h.nextBlk + 1)) h.nextBlk) ≠ .error e) := by
  have cm := inv.common
  have hs := cm.record
  have fr := cm.fresh
  have hW := cm.want
  have E3 := heap3_ext hs fr hW
  have EA : Ext h A i (s3z h s z') := Ext.ofFail E3 hs fr F recA libcA
  have E : Ext h (dHeap (dHeap A (h.nextBlk + 1)) h.nextBlk) i
      { s with «in» := .ref (.blk h.nextBlk) 0, out := .ref (.blk (h.nextBlk + 1)) 0, strm := z' } :=
    Ext.drop (Ext.drop EA _ (Nat.le_succ _)) _ (Nat.le_refl _)
  have nso : z'.state = none := stA.elim id (fun e => e.trans ((inv.writer hm).unalloc hsz))
  have free : ∀ x, h.nextBlk ≤ x → (dHeap (dHeap A (h.nextBlk + 1)) h.nextBlk).bytes x = none := by
    intro x hx
    rw [dHeap_bytes, dHeap_bytes]
    by_cases e0 : x = h.nextBlk
    · subst e0
      rw [upd_same]
    · rw [upd_ne _ _ _ _ e0]
      by_cases e1 : x = h.nextBlk + 1
      · subst e1
        rw [upd_same]
      · rw [upd_ne _ _ _ _ e1, (F.1 x).1]
        exact E3.fresh x (by rw [heap3_next]; omega)
  have hav : z'.avail_in = 0 := avA.trans (avail_zero (inv.writer hm) hsz)
  exact ⟨fun u B run => err_run fs run hfs hk inv hm hsz E hav nso free,
    fun e run => err_noerr fs run hfs hk inv hm hsz E hav nso free⟩

/-- The failure path when `out` cannot be allocated. -/
theorem outfail_tail {h : Heap} {i k : Nat} {s : GzState} (fs : Fs)
    (hfs : FileSystem fs) (hk : strIndex "out of memory" = some k)
    (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0) :
    (∀ u B, Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR (.ref (.str k) 0) (heapOF h i s) = .ok (u, B) →
      GzPost h i s [] fs B GzInv) ∧
    (∀ e, Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR (.ref (.str k) 0) (heapOF h i s) ≠ .error e) := by
  have cm := inv.common
  have hs := cm.record
  have fr := cm.fresh
  have hW := cm.want
  have E' := Ext.setS (Ext.failed (Ext.setS (Ext.alloc (Ext.base hs fr) (s.want.toNat <<< 1 % 4294967296)
    (by rw [shift_eq hW]; exact size_bound hW)) (s1 h s))) { s with «in» := .ref (.blk h.nextBlk) 0, out := .null }
  have E := Ext.drop E' h.nextBlk (Nat.le_refl _)
  have nso : s.strm.state = none := (inv.writer hm).unalloc hsz
  have free : ∀ x, h.nextBlk ≤ x → (heapOF h i s).bytes x = none := by
    intro x hx
    unfold heapOF
    rw [dHeap_bytes]
    by_cases e : x = h.nextBlk
    · subst e
      rw [upd_same]
    · rw [upd_ne _ _ _ _ e]
      exact E'.fresh x (show h.nextBlk + 1 ≤ x by omega)
  have hav := avail_zero (inv.writer hm) hsz
  exact ⟨fun u B run => err_run fs run hfs hk inv hm hsz E hav nso free,
    fun e run => err_noerr fs run hfs hk inv hm hsz E hav nso free⟩

macro "gzsimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, g_bind_app, g_pure_app, g_lift_app,
    Zlib.Gzlib.Proofs.ldS_eq, Zlib.Gzlib.Proofs.updS_eq, Zlib.Gzlib.Proofs.updX_eq, Zlib.Gzlib.Proofs.ldZ_eq,
    Zlib.Gzlib.Proofs.updZ_eq, gzSt, allocB_eq, freeB_eq, aHeap_gz, aHeap_allocOk, aHeap_nalloc, aHeap_nextBlk,
    aHeap_bytes, aHeap_ro, fHeap_gz, fHeap_allocOk, fHeap_nalloc, fHeap_nextBlk, fHeap_bytes, fHeap_ro, dHeap_gz,
    dHeap_bytes, dHeap_ro, dHeap_nextBlk, slot_setS, slot_aHeap, Zlib.GzFs.strLit, $ts,*])

theorem gz_init_run (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0) :
    ∃ v after, Zlib.Gzwrite.gz_init (gzSt i) fs h = .ok ((v, fs), after) ∧ (v = 0 ∨ v = -1) ∧
      GzPost h i s [] fs after GzInv := by
  have cm := inv.common
  have wr := inv.writer hm
  have hs := cm.record
  have fr := cm.fresh
  have il := rec_lt hs fr
  obtain ⟨k, hk⟩ := strIndex_of_mem (s := "out of memory") (by decide +kernel)
  have hW := cm.want
  have E0 := Ext.base hs fr
  have hav := avail_zero wr hsz
  have hi1 : h.nextBlk + 1 ≠ i := by omega
  have hi0 : h.nextBlk ≠ i := by omega
  have hnn : h.nextBlk + 1 ≠ h.nextBlk := by omega
  have hS0 : h.slotUsed h.nextBlk = false := Fresh.slotUsed_next fr
  have hS1 : h.slotUsed (h.nextBlk + 1) = false := Heap.slotUsed_eq_false.mpr (fr _ (by omega))
  have hn1 : s.want.toNat <<< 1 % 4294967296 = 2 * s.want.toNat := by
    rw [Nat.shiftLeft_eq, Nat.pow_one]
    have : (2 : Nat) ^ 31 = 2147483648 := by decide
    omega
  unfold Zlib.Gzwrite.gz_init
  by_cases hok : h.allocOk h.nalloc = true
  · by_cases hd : s.direct = 0
    · by_cases hok2 : h.allocOk (h.nalloc + 1) = true
      · gzsimp [hs, hok, eq_true hd, hok2, hi1, hi0, hnn, hS0, hS1, strLitRef_of_index hk,
          strLitRef_of_index version_index]
        have E3 := heap3_ext hs fr hW
        split
        next a fs1 h1 heq =>
          split at heq
          next _ rc A hrun =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            obtain ⟨⟨e1, e2⟩, e3⟩ := heq
            subst e1 e2 e3
            have hrun' : Zlib.Deflate.deflateInit2_ (some (.in_gzstate_strm i)) s.level Z_DEFLATED (MAX_WBITS + 16)
                DEF_MEM_LEVEL s.strategy (.ref (.str 57) 0) 112 (heap3 h i s) = .ok (rc, A) := hrun
            obtain ⟨⟨z', recA, avA, stA⟩, libcA, failA, okA⟩ := init_facts hrun' heap3_rec (E3.fresh' hs fr)
              (E3.uniq hs fr cm.uniq) (E3.globals cm.globals) ⟨Or.inl rfl, Or.inl rfl⟩
            have recA' : A.gzstates i = some
                { s with
                  «in» := .ref (.blk h.nextBlk) 0, out := .ref (.blk (h.nextBlk + 1)) 0, strm := z' } := recA
            by_cases hrc : rc = Z_OK
            · subst hrc
              obtain ⟨p, initA⟩ := okA rfl
              gzsimp [recA', eq_true hd]
              exact ⟨0, _, ⟨rfl, rfl⟩, Or.inl rfl,
                deflate_final fs hfs inv hm hsz hd hrun' initA recA avA libcA (by simp [sf, s3, zs3])⟩
            · have F := failA hrc
              have l0 : (heap3 h i s).live h.nextBlk := (heap3_live hs fr hW _).2 (Or.inr (Or.inl rfl))
              have l1 : (heap3 h i s).live (h.nextBlk + 1) := (heap3_live hs fr hW _).2 (Or.inr (Or.inr rfl))
              obtain ⟨a0, hb0, -⟩ := heap3_b0 (i := i) hW
              obtain ⟨a1, hb1, -⟩ := heap3_b1 (h := h) (i := i) (s := s)
              have hA0 : A.bytes h.nextBlk = some a0 := ((F.1 _).1).trans hb0
              have hA1 : A.bytes (h.nextBlk + 1) = some a1 := ((F.1 _).1).trans hb1
              have hR0 : A.ro h.nextBlk = false := ((F.1 _).2.2.2.2.2.2.2 l0 hi0).trans heap3_r0
              have hR1 : A.ro (h.nextBlk + 1) = false := ((F.1 _).2.2.2.2.2.2.2 l1 hi1).trans heap3_r1
              have hnn' : h.nextBlk ≠ h.nextBlk + 1 := by omega
              have T := fail_tail fs hfs hk inv hm hsz F recA avA (stA hrc) libcA
              gzsimp [recA', eq_false hrc, hA0, hA1, hR0, hR1, hnn', strLitRef_of_index hk]
              split
              next a fs1 h1 heq =>
                split at heq
                next _ u B hrun2 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at heq
                  obtain ⟨⟨-, e2⟩, e3⟩ := heq
                  subst e2 e3
                  exact ⟨-1, B, rfl, Or.inr rfl, T.1 u B hrun2⟩
                next _ e hrun2 => cases heq
              next e heq =>
                split at heq
                next _ u B hrun2 => cases heq
                next _ e' hrun2 => exact absurd hrun2 (T.2 e')
          next _ e hrun => cases heq
        next e heq =>
          split at heq
          next _ rc A hrun => cases heq
          next _ e' hrun =>
            exact (init_noerr (g := s3 h s) hrun heap3_rec (E3.fresh' hs fr) (E3.uniq hs fr cm.uniq)
              (E3.globals cm.globals) ⟨Or.inl rfl, Or.inl rfl⟩).elim
      · gzsimp [hs, hok, eq_true hd, hok2, hi1, hi0, hnn, hS0, hS1, strLitRef_of_index hk,
          strLitRef_of_index version_index]
        have T := outfail_tail fs hfs hk inv hm hsz
        split
        next a fs1 h1 heq =>
          split at heq
          next _ u B hrun2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            obtain ⟨⟨-, e2⟩, e3⟩ := heq
            subst e2 e3
            exact ⟨-1, B, rfl, Or.inr rfl, T.1 u B hrun2⟩
          next _ e hrun2 => cases heq
        next e heq =>
          split at heq
          next _ u B hrun2 => cases heq
          next _ e' hrun2 => exact absurd hrun2 (T.2 e')
    · gzsimp [hs, hok, eq_false hd, hi1, hi0, hnn, hS0, hS1, strLitRef_of_index hk,
        strLitRef_of_index version_index]
      exact ⟨0, _, ⟨rfl, rfl⟩, Or.inl rfl, direct_final fs hfs inv hm hsz hd hn1⟩
  · gzsimp [hs, hok, hi1, hi0, hnn, hS0, hS1, strLitRef_of_index hk, strLitRef_of_index version_index]
    have E := Ext.setS (Ext.failed E0) ({ s with «in» := .null } : GzState)
    have nso : s.strm.state = none := wr.unalloc hsz
    have free := fun x (hx : h.nextBlk ≤ x) => E.fresh x hx
    split
    next a fs1 h1 heq =>
      split at heq
      next _ u A run =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at heq
        obtain ⟨⟨e1, e2⟩, e3⟩ := heq
        subst e2 e3
        exact ⟨-1, A, rfl, Or.inr rfl, err_run fs run hfs hk inv hm hsz E hav nso free⟩
      next _ e run => cases heq
    next e heq =>
      split at heq
      next _ u A run => cases heq
      next _ e' run => exact (err_noerr fs run hfs hk inv hm hsz E hav nso free).elim

/-- **`gz_init` is safe** (the statement of `gz_init_safe` in `gz.skeleton-write`). -/
theorem gz_init_safe' (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0) :
    RunSafe (Zlib.Gzwrite.gz_init (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  obtain ⟨v, after, run, hv, post⟩ := gz_init_run i h fs s inv hfs hm hsz
  refine ⟨fun e he => ?_, fun _ => ⟨v, fs, after, run⟩, fun a fs' after' he => ?_⟩
  · rw [run] at he
    cases he
  · rw [run] at he
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨e1, e2⟩, e3⟩ := he
    subst e1 e2 e3
    exact ⟨hv, fun _ => Iff.rfl, post⟩

end Zlib.Gzwrite.SafeInit

#print axioms Zlib.Gzwrite.SafeInit.gz_init_safe'
