import ZlibF.Proof.«public-uncompress-wrappers»

/-!
# uncompr.c: `uncompress2`

`uncompress2` copies both lengths into two automatic cells, calls `uncompress2_z`
on them, copies the results back and frees the cells.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Inflate.Spec Zlib.Uncompr
set_option autoImplicit false

theorem Agree.write_out {keep : Nat → Prop} {X X' : Heap} (a : Agree keep X X') {p : BPtr} {xs : List UInt8}
    (out : ∀ r i, p = .ref r i → ∀ c, BRef.block r = some c → ¬ keep c) : Agree keep X (writeOut X' p xs) := by
  obtain ⟨gS, gA, gG, -, -, gB⟩ := writeOut_globals X' p xs
  refine ⟨fun b kb => (a.blocks b kb).trans (writeOut_same_other b (fun r i hp hb => ?_)), ?_, ?_, ?_, ?_⟩
  · exact out r i hp _ hb kb
  · rw [gS]; exact a.static
  · rw [gA]; exact a.allocOk
  · rw [gG]; exact a.garbage
  · rw [gB]; exact a.borrow

theorem Agree.store_in {keep : Nat → Prop} {X X' X₁ : Heap} (a : Agree keep X X') {p : BPtr} {xs : List UInt8}
    (st : Store X' p xs X₁) (inK : ∀ r i, p = .ref r i → ∀ c, BRef.block r = some c → keep c) :
    Store X p xs (writeOut X p xs) := by
  rcases st with ⟨rfl, -⟩ | ⟨r, i, arr, rfl, g, ro, fit, -⟩
  · rw [writeOut_nil]; exact Or.inl ⟨rfl, rfl⟩
  · have e := a.get (inK r i rfl)
    exact store_writeOut (Or.inr ⟨r, i, arr, rfl, by rw [← e.1]; exact g, by rw [← e.2]; exact ro, fit⟩)

/-- Freeing two cells: the final comparison carries over. -/
theorem same_without_two {k : Nat} {X X' Y' : Heap} (s : SameObjectsUpToTableShape X' Y')
    (a : Agree (fun b => b ≠ k ∧ b ≠ k + 1) X X') (xk : ¬ X.live k) (xk1 : ¬ X.live (k + 1))
    (x'k : ∀ c, c = k ∨ c = k + 1 → X'.words c = none ∧ X'.streams c = none ∧ X'.gzheaders c = none ∧
      X'.dstates c = none ∧ X'.istates c = none ∧ X'.gzstates c = none)
    (nb : X.nextBlk ≤ X'.nextBlk) (na : X.nalloc ≤ X'.nalloc) :
    SameObjectsUpToTableShape X
      { ({ Y' with bytes := upd Y'.bytes k none } : Heap) with
        bytes := upd (upd Y'.bytes k none) (k + 1) none } := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := s
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at xk xk1
  have none_at : ∀ c, c = k ∨ c = k + 1 → X.bytes c = none ∧ X.words c = none ∧ X.streams c = none ∧
      X.gzheaders c = none ∧ X.dstates c = none ∧ X.istates c = none ∧ X.gzstates c = none := by
    rintro c (rfl | rfl)
    · exact xk
    · exact xk1
  have other : ∀ b, ¬ (b = k ∨ b = k + 1) → SameAt X X' b := fun b nb =>
    a.blocks b ⟨fun e => nb (Or.inl e), fun e => nb (Or.inr e)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    simp only [upd_apply]
    by_cases e1 : b = k + 1
    · rw [if_pos e1]; exact ((none_at b (Or.inr e1)).1).symm
    by_cases e0 : b = k
    · rw [if_neg e1, if_pos e0]; exact ((none_at b (Or.inl e0)).1).symm
    rw [if_neg e1, if_neg e0, s1 b]; exact (other b (by omega)).1
  · intro b
    by_cases c : b = k ∨ b = k + 1
    · rw [s2 b, (x'k b c).1, (none_at b c).2.1]
    · rw [s2 b]; exact (other b c).2.1
  · intro b live
    have c : ¬ (b = k ∨ b = k + 1) := by
      rintro c
      have := none_at b c
      simp [Heap.live, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1,
        this.2.2.2.2.2.2] at live
    have sb := other b c
    have l' : X'.live b := by
      obtain ⟨t1, t2, t3, t4, t5, t6, t7, -⟩ := sb
      simp only [Heap.live] at live ⊢
      rw [t1, t2, t3, t4, t5, t6, t7]; exact live
    show Y'.ro b = X.ro b
    rw [s3 b l']
    exact sb.2.2.2.2.2.2.2
  · intro b
    by_cases c : b = k ∨ b = k + 1
    · show Y'.streams b = X.streams b; rw [s4 b, (x'k b c).2.1, (none_at b c).2.2.1]
    · show Y'.streams b = X.streams b; rw [s4 b]; exact (other b c).2.2.1
  · intro b
    by_cases c : b = k ∨ b = k + 1
    · show Y'.gzheaders b = X.gzheaders b; rw [s5 b, (x'k b c).2.2.1, (none_at b c).2.2.2.1]
    · show Y'.gzheaders b = X.gzheaders b; rw [s5 b]; exact (other b c).2.2.2.1
  · intro b
    by_cases c : b = k ∨ b = k + 1
    · show Y'.dstates b = X.dstates b; rw [s6 b, (x'k b c).2.2.2.1, (none_at b c).2.2.2.2.1]
    · show Y'.dstates b = X.dstates b; rw [s6 b]; exact (other b c).2.2.2.2.1
  · intro b
    by_cases c : b = k ∨ b = k + 1
    · show Y'.istates b = X.istates b; rw [s7 b, (x'k b c).2.2.2.2.1, (none_at b c).2.2.2.2.2.1]
    · show Y'.istates b = X.istates b; rw [s7 b]; exact (other b c).2.2.2.2.2.1
  · intro b
    by_cases c : b = k ∨ b = k + 1
    · show Y'.gzstates b = X.gzstates b; rw [s8 b, (x'k b c).2.2.2.2.2, (none_at b c).2.2.2.2.2.2]
    · show Y'.gzstates b = X.gzstates b; rw [s8 b]; exact (other b c).2.2.2.2.2.2.1
  · show Y'.static = X.static; rw [s9]; exact a.static
  · show Y'.allocOk = X.allocOk; rw [s10]; exact a.allocOk
  · show Y'.garbage = X.garbage; rw [s11]; exact a.garbage
  · exact Nat.le_trans nb s12
  · exact Nat.le_trans na s13

theorem cellRaw_live (h : Heap) (b : Nat) : (cellRaw h).live b ↔ h.live b ∨ b = h.nextBlk := by
  simp only [cellRaw, Heap.live, upd_apply]
  by_cases e : b = h.nextBlk
  · subst e; simp
  · simp [e]

theorem cellRaw_fresh {h : Heap} (fresh : Fresh h) : Fresh (cellRaw h) := by
  intro b hb live
  rw [cellRaw_live] at live
  simp only [cellRaw] at hb
  rcases live with l | l
  · exact fresh b (by omega) l
  · omega

theorem cellRaw_kept {h : Heap} (fresh : Fresh h) : ByteViewsKept h (cellRaw h) where
  bytes b hb := by
    have ne : b ≠ h.nextBlk := fun e => fresh b (by omega) (Or.inl hb)
    simp [cellRaw, upd_ne _ _ _ _ ne]
  dstates := rfl
  static := rfl
  borrow := rfl

/-- The array of a fresh cell after a store. -/
theorem cell_array (h : Heap) (v : UInt64) :
    store64Array (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)) 0 v = (lengthBytes v).toArray := by
  rw [store64Array_eq _ _ _ (by simp)]
  simp

/-- The heap after the two cells of `uncompress2` are made and filled. -/
def cells2 (h : Heap) (cap n : UInt64) : Heap :=
  { cellRaw (cellRaw h) with
    bytes := upd (upd (cellRaw (cellRaw h)).bytes h.nextBlk (some (lengthBytes cap).toArray)) (h.nextBlk + 1)
      (some (lengthBytes n).toArray) }

theorem cells2_bytes (h : Heap) (cap n : UInt64) (b : Nat) :
    (cells2 h cap n).bytes b = if b = h.nextBlk + 1 then some (lengthBytes n).toArray
      else if b = h.nextBlk then some (lengthBytes cap).toArray else h.bytes b := by
  simp only [cells2, cellRaw, upd_apply]
  by_cases e1 : b = h.nextBlk + 1
  · simp [e1]
  · by_cases e0 : b = h.nextBlk
    · simp [e1, e0]
    · simp [e1, e0]

theorem cells2_ro (h : Heap) (cap n : UInt64) (b : Nat) :
    (cells2 h cap n).ro b = if b = h.nextBlk + 1 ∨ b = h.nextBlk then false else h.ro b := by
  simp only [cells2, cellRaw, upd_apply]
  by_cases e1 : b = h.nextBlk + 1
  · simp [e1]
  · by_cases e0 : b = h.nextBlk
    · simp [e1, e0]
    · simp [e1, e0]

theorem cells2_others (h : Heap) (cap n : UInt64) :
    (cells2 h cap n).words = h.words ∧ (cells2 h cap n).streams = h.streams ∧
    (cells2 h cap n).gzheaders = h.gzheaders ∧ (cells2 h cap n).dstates = h.dstates ∧
    (cells2 h cap n).istates = h.istates ∧ (cells2 h cap n).gzstates = h.gzstates ∧
    (cells2 h cap n).static = h.static ∧ (cells2 h cap n).allocOk = h.allocOk ∧
    (cells2 h cap n).garbage = h.garbage ∧ (cells2 h cap n).nalloc = h.nalloc ∧
    (cells2 h cap n).nextBlk = h.nextBlk + 2 ∧ (cells2 h cap n).libcErrorBorrow = h.libcErrorBorrow := by
  simp [cells2, cellRaw]

theorem cells2_live (h : Heap) (cap n : UInt64) (b : Nat) :
    (cells2 h cap n).live b ↔ h.live b ∨ b = h.nextBlk ∨ b = h.nextBlk + 1 := by
  obtain ⟨o1, o2, o3, o4, o5, o6, -⟩ := cells2_others h cap n
  simp only [Heap.live, cells2_bytes, o1, o2, o3, o4, o5, o6]
  by_cases e1 : b = h.nextBlk + 1
  · simp [e1]
  · by_cases e0 : b = h.nextBlk
    · simp [e0]
    · simp [e1, e0]

theorem cells2_fresh {h : Heap} (fresh : Fresh h) (cap n : UInt64) : Fresh (cells2 h cap n) := by
  intro b hb live
  rw [cells2_live] at live
  rw [(cells2_others h cap n).2.2.2.2.2.2.2.2.2.2.1] at hb
  rcases live with l | l | l
  · exact fresh b (by omega) l
  · omega
  · omega

theorem cells2_uniq {h : Heap} (fresh : Fresh h) (u : Uniq h) (cap n : UInt64) : Uniq (cells2 h cap n) := by
  intro b
  have ub := u b
  obtain ⟨o1, o2, o3, o4, o5, o6, -⟩ := cells2_others h cap n
  simp only [cells2_bytes, o1, o2, o3, o4, o5, o6]
  have n0 := fresh h.nextBlk (Nat.le_refl _)
  have n1 := fresh (h.nextBlk + 1) (by omega)
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at n0 n1
  by_cases e1 : b = h.nextBlk + 1
  · subst e1; simp [n1.2.1, n1.2.2.1, n1.2.2.2.1, n1.2.2.2.2.1, n1.2.2.2.2.2.1, n1.2.2.2.2.2.2]
  · by_cases e0 : b = h.nextBlk
    · subst e0; simp [n0.2.1, n0.2.2.1, n0.2.2.2.1, n0.2.2.2.2.1, n0.2.2.2.2.2.1, n0.2.2.2.2.2.2]
    · simpa [e1, e0] using ub

theorem cells2_kept {h : Heap} (fresh : Fresh h) (cap n : UInt64) : ByteViewsKept h (cells2 h cap n) where
  bytes b hb := by
    have n0 : b ≠ h.nextBlk := fun e => fresh b (by omega) (Or.inl hb)
    have n1 : b ≠ h.nextBlk + 1 := fun e => fresh b (by omega) (Or.inl hb)
    refine ⟨by rw [cells2_bytes]; simp [n0, n1], by rw [cells2_ro]; simp [n0, n1]⟩
  dstates := (cells2_others h cap n).2.2.2.1
  static := (cells2_others h cap n).2.2.2.2.2.2.1
  borrow := (cells2_others h cap n).2.2.2.2.2.2.2.2.2.2.2

theorem cells2_agree {h : Heap} (cap n : UInt64) :
    Agree (fun b => b ≠ h.nextBlk ∧ b ≠ h.nextBlk + 1) h (cells2 h cap n) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, -, -, o12⟩ := cells2_others h cap n
  refine ⟨fun b ⟨n0, n1⟩ => ⟨by rw [cells2_bytes]; simp [n0, n1], by rw [o1], by rw [o2], by rw [o3], by rw [o4],
    by rw [o5], by rw [o6], by rw [cells2_ro]; simp [n0, n1]⟩, o7, o8, o9, o12⟩

theorem cells2_fit {h : Heap} (fresh : Fresh h) (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (cap n : UInt64) :
    ZlibF.PlatformMemory.ByteObjectsFit (cells2 h cap n) := by
  intro rr a g
  cases rr with
  | blk c =>
    simp only [Space.get, cells2_bytes] at g
    split at g
    · cases g; simp [lengthBytes_length, ZlibF.PlatformMemory.byteObjectLimit]
    · split at g
      · cases g; simp [lengthBytes_length, ZlibF.PlatformMemory.byteObjectLimit]
      · exact fit (.blk c) a g
  | str i => exact fit (.str i) a (by simpa [Space.get, staticStringBytes, cells2_others] using g)
  | dstate_depth i => exact fit (.dstate_depth i) a (by simpa [Space.get, cells2_others] using g)
  | st_dist_code => exact fit .st_dist_code a (by simpa [Space.get, cells2_others] using g)
  | st_length_code => exact fit .st_length_code a (by simpa [Space.get, cells2_others] using g)

theorem cells2_got (h : Heap) (cap n : UInt64) : LengthCell (cells2 h cap n) (cellPtr h) cap := by
  have g : Space.get (cells2 h cap n) (BRef.blk h.nextBlk) = some (lengthBytes cap).toArray := by
    simp only [Space.get, cells2_bytes]; simp
  refine ⟨Or.inr ⟨.blk h.nextBlk, 0, _, rfl, g, by simp [lengthBytes_length], ?_⟩,
    Or.inr ⟨.blk h.nextBlk, 0, _, rfl, g, by simp only [Space.ro, cells2_ro]; simp, by simp [lengthBytes_length]⟩⟩
  simp only [List.toList_toArray, List.drop_zero]
  rw [List.take_of_length_le (by rw [lengthBytes_length]; exact Nat.le_refl _)]
  rfl

theorem cells2_used (h : Heap) (cap n : UInt64) : LengthCell (cells2 h cap n) (cellPtr (cellRaw h)) n := by
  have g : Space.get (cells2 h cap n) (BRef.blk (h.nextBlk + 1)) = some (lengthBytes n).toArray := by
    simp only [Space.get, cells2_bytes]; simp
  have p : cellPtr (cellRaw h) = .ref (.blk (h.nextBlk + 1)) 0 := rfl
  rw [p]
  refine ⟨Or.inr ⟨.blk (h.nextBlk + 1), 0, _, rfl, g, by simp [lengthBytes_length], ?_⟩,
    Or.inr ⟨.blk (h.nextBlk + 1), 0, _, rfl, g, by simp only [Space.ro, cells2_ro]; simp,
      by simp [lengthBytes_length]⟩⟩
  simp only [List.toList_toArray, List.drop_zero]
  rw [List.take_of_length_le (by rw [lengthBytes_length]; exact Nat.le_refl _)]
  rfl

/-- The heap after the first cell of `uncompress2` is filled. -/
def cells1 (h : Heap) (cap : UInt64) : Heap :=
  Space.put (cellRaw (cellRaw h)) (BRef.blk h.nextBlk) (lengthBytes cap).toArray

/-- The steps of the prologue of `uncompress2`: two cells made and filled with the caller lengths. -/
theorem prologue2_steps {h : Heap} (fresh : Fresh h) {destLen sourceLen : BPtr} {cap n : UInt64}
    (dcell : LengthCell h destLen cap) (scell : LengthCell h sourceLen n) :
    allocLocal 8 h = .ok (cellPtr h, cellRaw h) ∧
    allocLocal 8 (cellRaw h) = .ok (cellPtr (cellRaw h), cellRaw (cellRaw h)) ∧
    load64 destLen (cellRaw (cellRaw h)) = .ok (cap, cellRaw (cellRaw h)) ∧
    store64 (cellPtr h) cap (cellRaw (cellRaw h)) = .ok ((), cells1 h cap) ∧
    load64 sourceLen (cells1 h cap) = .ok (n, cells1 h cap) ∧
    store64 (cellPtr (cellRaw h)) n (cells1 h cap) = .ok ((), cells2 h cap n) := by
  have f1 := cellRaw_fresh fresh
  have k1 := cellRaw_kept fresh
  have k2 := k1.trans (cellRaw_kept f1)
  have gK : Space.get (cellRaw (cellRaw h)) (BRef.blk h.nextBlk) =
      some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)) := by
    simp [Space.get, cellRaw]
  have st1 := store64_ref (v := cap) (i := 0) gK (by simp [Space.ro, cellRaw]) (by simp)
  rw [cell_array] at st1
  have k3 : ByteViewsKept h (cells1 h cap) := by
    refine ⟨fun b hb => ?_, rfl, rfl, rfl⟩
    have n0 : b ≠ h.nextBlk := fun e => fresh b (by omega) (Or.inl hb)
    have n1 : b ≠ h.nextBlk + 1 := fun e => fresh b (by omega) (Or.inl hb)
    simp [cells1, Space.put, cellRaw, upd_ne _ _ _ _ n0, upd_ne _ _ _ _ n1]
  have gK1 : Space.get (cells1 h cap) (BRef.blk (h.nextBlk + 1)) =
      some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)) := by
    simp [cells1, Space.get, Space.put, cellRaw]
  have st2 := store64_ref (v := n) (i := 0) gK1 (by simp [cells1, Space.ro, Space.put, cellRaw]) (by simp)
  rw [cell_array] at st2
  exact ⟨alloc_cell_run fresh, alloc_cell_run f1, load64_cell (k2.cell_of dcell), st1, load64_cell (k3.cell_of scell),
    st2⟩

/-- A writable view reads the same array in a heap equal entry by entry. -/
theorem same_view {X Y : Heap} (s : SameObjectsUpToTableShape X Y) {r : BRef} {a : Array UInt8}
    (g : Space.get X r = some a) (ro : Space.ro X r = false) :
    Space.get Y r = some a ∧ Space.ro Y r = false := by
  obtain ⟨s1, -, s3, -, -, s6, -⟩ := s
  cases r with
  | blk c =>
    simp only [Space.get, Space.ro] at g ro ⊢
    refine ⟨by rw [s1 c]; exact g, ?_⟩
    rw [s3 c (Or.inl (by rw [g]; simp))]; exact ro
  | dstate_depth c =>
    simp only [Space.get] at g ⊢
    rw [s6 c]
    exact ⟨g, rfl⟩
  | str i => simp [Space.ro] at ro
  | st_dist_code => simp [Space.ro] at ro
  | st_length_code => simp [Space.ro] at ro

theorem same_cell {X Y : Heap} (s : SameObjectsUpToTableShape X Y) {p : BPtr} {v : UInt64}
    (c : LengthCell X p v) : LengthCell Y p v := by
  obtain ⟨b, w⟩ := c
  rcases w with ⟨-, h8⟩ | ⟨r, i, a, rfl, g, ro, fit⟩
  · cases h8
  have e := same_view s g ro
  rcases b with ⟨h0, -, -⟩ | ⟨r', i', a', hp, g', fit', hx⟩
  · cases h0
  · cases hp
    rw [g] at g'; cases g'
    exact ⟨Or.inr ⟨r, i, a, rfl, e.1, fit', hx⟩, Or.inr ⟨r, i, a, rfl, e.1, e.2, fit⟩⟩

theorem live_below {h : Heap} (fresh : Fresh h) {c : Nat} (l : h.live c) : c < h.nextBlk := by
  by_cases lt : c < h.nextBlk
  · exact lt
  · exact absurd l (fresh c (by omega))

/-- Writing a length to a writable cell makes it hold that length. -/
theorem cell_written {X : Heap} {p : BPtr} (w : Writable X p 8) (v : UInt64) :
    LengthCell (writeOut X p (lengthBytes v)) p v := by
  rcases w with ⟨-, h8⟩ | ⟨r, i, a, rfl, g, ro, fit⟩
  · cases h8
  have ne : lengthBytes v ≠ [] := by intro e; have := congrArg List.length e; simp [lengthBytes_length] at this
  have len := lengthBytes_length v
  rcases writeOut_same (xs := lengthBytes v) (i := i) g ro with e | ⟨e', -⟩
  · refine ⟨Or.inr ⟨r, i, _, rfl, e, by rw [written_size a i _ (by omega)]; exact fit, ?_⟩,
      Or.inr ⟨r, i, _, rfl, e, by rw [writeOut_ro]; exact ro, by rw [written_size a i _ (by omega)]; exact fit⟩⟩
    show lengthBytes v = _
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]
    rw [written_get? a i (lengthBytes v) (by omega), len]
    by_cases jl : j < 8
    · simp only [jl, ite_true, show ¬ i + j < i by omega, show i + j < i + 8 by omega, ite_false,
        show i + j - i = j by omega]
    · simp only [jl, ite_false]
      rw [List.getElem?_eq_none (by omega)]
  · exact absurd e' ne

/-- The epilogue heaps of `uncompress2`. -/
def epiW (A : Heap) (sourceLen destLen : BPtr) (usedV gotV : UInt64) : Heap :=
  writeOut (writeOut A sourceLen (lengthBytes usedV)) destLen (lengthBytes gotV)

def freed2 (W : Heap) (k : Nat) : Heap :=
  { ({ W with bytes := upd W.bytes k none } : Heap) with bytes := upd (upd W.bytes k none) (k + 1) none }

/-- The steps of the epilogue of `uncompress2`: copy back both counts and free both cells. -/
theorem epilogue2_steps {h A : Heap} {sourceLen destLen : BPtr} {gotV usedV n cap : UInt64}
    (cg : LengthCell A (cellPtr h) gotV) (cu : LengthCell A (cellPtr (cellRaw h)) usedV)
    (cs : LengthCell A sourceLen n) (cd : LengthCell A destLen cap)
    (sgS : Separate (cellPtr h) 8 sourceLen 8) (sgD : Separate (cellPtr h) 8 destLen 8)
    (suS : Separate (cellPtr (cellRaw h)) 8 sourceLen 8) (suD : Separate (cellPtr (cellRaw h)) 8 destLen 8)
    (sDS : Separate destLen 8 sourceLen 8) :
    load64 (cellPtr (cellRaw h)) A = .ok (usedV, A) ∧
    store64 sourceLen usedV A = .ok ((), writeOut A sourceLen (lengthBytes usedV)) ∧
    load64 (cellPtr h) (writeOut A sourceLen (lengthBytes usedV)) =
      .ok (gotV, writeOut A sourceLen (lengthBytes usedV)) ∧
    store64 destLen gotV (writeOut A sourceLen (lengthBytes usedV)) = .ok ((), epiW A sourceLen destLen usedV gotV) ∧
    freeB (cellPtr h) (epiW A sourceLen destLen usedV gotV) =
      .ok ((), { epiW A sourceLen destLen usedV gotV with
        bytes := upd (epiW A sourceLen destLen usedV gotV).bytes h.nextBlk none }) ∧
    freeB (cellPtr (cellRaw h)) { epiW A sourceLen destLen usedV gotV with
        bytes := upd (epiW A sourceLen destLen usedV gotV).bytes h.nextBlk none } =
      .ok ((), freed2 (epiW A sourceLen destLen usedV gotV) h.nextBlk) := by
  have lbne : ∀ v, lengthBytes v ≠ [] := by
    intro v e; have := congrArg List.length e; simp [lengthBytes_length] at this
  have len8 : ∀ v, (lengthBytes v).length ≤ 8 := fun v => by rw [lengthBytes_length]; exact Nat.le_refl _
  obtain ⟨W1, st1, S1⟩ := store64_writable usedV cs.2
  have e1 := store_eq_writeOut S1 (lbne _)
  subst e1
  have cg1 := cell_writeOut_sep cg sgS (len8 usedV) cs.2
  have cu1 := cell_writeOut_sep cu suS (len8 usedV) cs.2
  have cd1 := cell_writeOut_sep cd sDS (len8 usedV) cs.2
  obtain ⟨W2, st2, S2⟩ := store64_writable gotV cd1.2
  have e2 := store_eq_writeOut S2 (lbne _)
  subst e2
  have cg2 := cell_writeOut_sep cg1 sgD (len8 gotV) cd1.2
  have cu2 := cell_writeOut_sep cu1 suD (len8 gotV) cd1.2
  have bytesOf : ∀ {X : Heap} {j : Nat} {v : UInt64}, LengthCell X (.ref (.blk j) 0) v →
      ∃ a, X.bytes j = some a ∧ X.ro j = false := by
    intro X j v c
    rcases c.2 with ⟨h0, -⟩ | ⟨r, i, a, hq, g, ro, -⟩
    · cases h0
    · simp only [Ptr.ref.injEq] at hq; obtain ⟨rfl, rfl⟩ := hq
      exact ⟨a, g, ro⟩
  obtain ⟨ag, hg, rg⟩ := bytesOf cg2
  obtain ⟨au, hu, ru⟩ := bytesOf cu2
  refine ⟨load64_cell cu, st1, load64_cell cg1, st2, ?_, ?_⟩
  · exact freeB_blk_run hg rg
  · have ne : h.nextBlk + 1 ≠ h.nextBlk := by omega
    have hu' : ({ epiW A sourceLen destLen usedV gotV with
        bytes := upd (epiW A sourceLen destLen usedV gotV).bytes h.nextBlk none } : Heap).bytes (h.nextBlk + 1) =
        some au := by simp only [upd_ne _ _ _ _ ne]; exact hu
    exact freeB_blk_run hu' ru

/-- `int uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen)`,
from the decoder facts of batch 3 (`DecoderFacts`), which are explicit hypotheses. -/
theorem uncompress2_of_facts (facts : DecoderFacts) : Goal.uncompress2 := by
  intro h dest destLen source sourceLen capacity n src fresh uniq globals fit dcellO scellO nn srcB destW sep
  obtain ⟨dl, sl⟩ := nn rfl
  have dcell := dcellO dl
  have scell := scellO sl
  have kept := cells2_kept fresh capacity n
  have agree := cells2_agree (h := h) capacity n
  -- caller pointers are below the cells
  have below : ∀ (q : BPtr), (∀ r i, q = .ref r i → ∃ a, Space.get h r = some a) →
      ∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c < h.nextBlk := by
    intro q reads r i hq c hc
    obtain ⟨a, g⟩ := reads r i hq
    exact live_below fresh (view_block_live g c hc)
  have readsW : ∀ (q : BPtr) (m : Nat), (q ≠ .null → Writable h q m) →
      ∀ r i, q = .ref r i → ∃ a, Space.get h r = some a := by
    intro q m w r i hq
    rcases w (by rw [hq]; simp) with ⟨h0, -⟩ | ⟨r', i', a, hq', g, -, -⟩
    · rw [hq] at h0; cases h0
    · rw [hq] at hq'; cases hq'; exact ⟨a, g⟩
  have readsB : ∀ (q : BPtr) (m : Nat) (xs : List UInt8), (q ≠ .null → Bytes h q m xs) →
      ∀ r i, q = .ref r i → ∃ a, Space.get h r = some a := by
    intro q m xs b r i hq
    rcases b (by rw [hq]; simp) with ⟨h0, -, -⟩ | ⟨r', i', a, hq', g, -, -⟩
    · rw [hq] at h0; cases h0
    · rw [hq] at hq'; cases hq'; exact ⟨a, g⟩
  have destB := below dest (readsW dest _ destW)
  have srcBl := below source (readsB source _ _ srcB)
  have dlB := below destLen (readsW destLen 8 (fun _ => dcell.2))
  have slB := below sourceLen (readsW sourceLen 8 (fun _ => scell.2))
  have keepOf : ∀ (q : BPtr), (∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c < h.nextBlk) →
      ∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk ∧ c ≠ h.nextBlk + 1 := by
    intro q qb r i hq c hc
    have := qb r i hq c hc
    exact ⟨by omega, by omega⟩
  have sepCell : ∀ (j : Nat) (q : BPtr) (m : Nat), (∀ r i, q = .ref r i → ∀ c, BRef.block r = some c →
      c < h.nextBlk) → h.nextBlk ≤ j → Separate (.ref (.blk j) 0) 8 q m := by
    intro j q m qb hj
    by_cases m0 : m = 0
    · exact Or.inr (Or.inl m0)
    right; right
    cases q with
    | null => simp
    | ref r i =>
      left
      intro e
      have := qb r i rfl j (by rw [← e]; rfl)
      omega
  have sepU : UtilitySeparation dest capacity.toNat source n.toNat (cellPtr h) (cellPtr (cellRaw h)) :=
    ⟨sep.1, sepCell _ dest _ destB (Nat.le_refl _), sepCell _ source _ srcBl (Nat.le_refl _),
      sepCell _ dest _ destB (Nat.le_succ _), sepCell _ source _ srcBl (Nat.le_succ _),
      Or.inr (Or.inr (Or.inl (by simp [cellPtr, cellRaw])))⟩
  obtain ⟨rc, after', run', bad', good'⟩ := uncompress2_z_of_facts facts (cells2 h capacity n) dest (cellPtr h)
    source (cellPtr (cellRaw h)) capacity n src (cells2_fresh fresh capacity n) (cells2_uniq fresh uniq capacity n)
    (by simp only [LibraryGlobals] at globals ⊢; rw [(cells2_others h capacity n).2.2.2.2.2.2.1]; exact globals)
    (cells2_fit fresh fit capacity n) (fun _ => cells2_got h capacity n) (fun _ => cells2_used h capacity n)
    (fun e => absurd e (by decide)) (fun sn => kept.bytes_of (srcB sn)) (fun dn => kept.writable_of (destW dn)) sepU
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := prologue2_steps fresh dcell scell
  have lbne : ∀ v, lengthBytes v ≠ [] := by
    intro v e; have := congrArg List.length e; simp [lengthBytes_length] at this
  have sepCells : ∀ (q : BPtr), (∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c < h.nextBlk) →
      Separate (cellPtr h) 8 q 8 ∧ Separate (cellPtr (cellRaw h)) 8 q 8 :=
    fun q qb => ⟨sepCell _ q 8 qb (Nat.le_refl _), sepCell _ q 8 qb (Nat.le_succ _)⟩
  have runTo : ∀ (gotV usedV : UInt64), LengthCell after' (cellPtr h) gotV →
      LengthCell after' (cellPtr (cellRaw h)) usedV → LengthCell after' sourceLen n →
      LengthCell after' destLen capacity →
      C.run (uncompress2 dest destLen source sourceLen) h =
        .ok (rc, freed2 (epiW after' sourceLen destLen usedV gotV) h.nextBlk) := by
    intro gotV usedV cg cu cs cd
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := epilogue2_steps (n := n) (cap := capacity) cg cu cs cd
      (sepCells sourceLen slB).1 (sepCells destLen dlB).1 (sepCells sourceLen slB).2 (sepCells destLen dlB).2
      sep.2.2.2.2.2
    unfold uncompress2
    simp only [C.run, bind_app, p1, p2, p3, p4, p5, p6]
    rw [show Zlib.Uncompr.uncompress2_z dest (cellPtr h) source (cellPtr (cellRaw h)) (cells2 h capacity n) =
      .ok (rc, after') from run']
    simp only [bind_app, e1, e2, e3, e4, e5, e6, pure_app]
  have x'k : ∀ (X : Heap), (∀ c, c = h.nextBlk ∨ c = h.nextBlk + 1 → X.words c = none ∧ X.streams c = none ∧
      X.gzheaders c = none ∧ X.dstates c = none ∧ X.istates c = none ∧ X.gzstates c = none) →
      ∀ (q : BPtr) (xs : List UInt8),
      (∀ r i, q = .ref r i → (∀ c, BRef.block r = some c → c < h.nextBlk) ∨ ∃ j, r = .blk j) →
      ∀ c, c = h.nextBlk ∨ c = h.nextBlk + 1 → (writeOut X q xs).words c = none ∧
        (writeOut X q xs).streams c = none ∧ (writeOut X q xs).gzheaders c = none ∧
        (writeOut X q xs).dstates c = none ∧ (writeOut X q xs).istates c = none ∧
        (writeOut X q xs).gzstates c = none := by
    intro X hx q xs hq c hc
    cases q with
    | null => simpa [writeOut] using hx c hc
    | ref r i =>
      rcases hq r i rfl with qb | ⟨j, rfl⟩
      · obtain ⟨-, t2, t3, t4, t5, t6, t7, -⟩ := writeOut_same_other (H := X) (p := .ref r i) (xs := xs) c
          (fun r' i' hp hb => by
            simp only [Ptr.ref.injEq] at hp; obtain ⟨rfl, -⟩ := hp
            have := qb c hb; rcases hc with rfl | rfl <;> omega)
        rw [t2, t3, t4, t5, t6, t7]; exact hx c hc
      · obtain ⟨o1, o2, o3, o4, o5, o6⟩ := writeOut_blk_others X j i xs
        rw [o1, o2, o3, o4, o5, o6]; exact hx c hc
  have Gnone : ∀ c, c = h.nextBlk ∨ c = h.nextBlk + 1 → (cells2 h capacity n).words c = none ∧
      (cells2 h capacity n).streams c = none ∧ (cells2 h capacity n).gzheaders c = none ∧
      (cells2 h capacity n).dstates c = none ∧ (cells2 h capacity n).istates c = none ∧
      (cells2 h capacity n).gzstates c = none := by
    intro c hc
    obtain ⟨o1, o2, o3, o4, o5, o6, -⟩ := cells2_others h capacity n
    have nl : ¬ h.live c := by rcases hc with rfl | rfl <;> exact fresh _ (by omega)
    simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at nl
    rw [o1, o2, o3, o4, o5, o6]
    exact ⟨nl.2.1, nl.2.2.1, nl.2.2.2.1, nl.2.2.2.2.1, nl.2.2.2.2.2.1, nl.2.2.2.2.2.2⟩
  have hk0 : ¬ h.live h.nextBlk := fresh _ (Nat.le_refl _)
  have hk1 : ¬ h.live (h.nextBlk + 1) := fresh _ (by omega)
  by_cases badW : (source = .null ∧ n ≠ 0) ∨ (dest = .null ∧ capacity ≠ 0)
  · obtain ⟨rcE, sm⟩ := bad' (Or.inr (Or.inr badW))
    refine ⟨rc, _, runTo capacity n (same_cell sm (cells2_got h capacity n)) (same_cell sm (cells2_used h capacity n))
      (same_cell sm (kept.cell_of scell)) (same_cell sm (kept.cell_of dcell)), fun _ => ⟨rcE, ?_⟩, ?_⟩
    · have s2 := same_writeOut_both (same_writeOut_both sm sourceLen (lengthBytes n)) destLen (lengthBytes capacity)
      rw [cell_self_write (kept.cell_of scell), cell_self_write (kept.cell_of dcell)] at s2
      exact same_without_two s2 agree hk0 hk1 Gnone (by simp [cells2_others]) (by simp [cells2_others])
    · intro _ _ sN dN
      exfalso
      rcases badW with b | b
      · exact b.2 (sN b.1)
      · exact b.2 (dN b.1)
  · have sN : source = .null → n = 0 := fun e => Classical.byContradiction fun ne => badW (Or.inl ⟨e, ne⟩)
    have dN : dest = .null → capacity = 0 := fun e => Classical.byContradiction fun ne => badW (Or.inr ⟨e, ne⟩)
    obtain ⟨out, usedN, gotV, consumed, h₁', h₂', exp', S1, S2, S3, sm, unc, counts, mem'⟩ :=
      good' (by simp [cellPtr, cellRaw]) (by simp [cellPtr]) sN dN
    have f1 := store_fun S1
    have f2 := store_fun S2
    have f3 := store_fun S3
    subst f1 f2 f3
    have outLe : out.length ≤ capacity.toNat := by
      have u := unc
      unfold Uncompressed Api.Uncompress2 at u
      rw [if_neg (by decide)] at u
      exact u.2.1
    have wDest : Writable h dest capacity.toNat := by
      by_cases dn : dest = .null
      · exact Or.inl ⟨dn, by rw [dN dn]; rfl⟩
      · exact destW dn
    have wDestG : Writable (cells2 h capacity n) dest capacity.toNat := kept.writable_of wDest
    have len8 : ∀ v, (lengthBytes v).length ≤ 8 := fun v => by rw [lengthBytes_length]; exact Nat.le_refl _
    have sUG : Separate (cellPtr (cellRaw h)) 8 (cellPtr h) 8 :=
      Or.inr (Or.inr (Or.inl (by simp [cellPtr, cellRaw])))
    -- the cells of the expected inner heap
    have gG := cells2_got h capacity n
    have uG := cells2_used h capacity n
    have g1 := cell_writeOut_sep (xs := out) gG sepU.2.1 outLe wDestG
    have u1 := cell_writeOut_sep (xs := out) uG sepU.2.2.2.1 outLe wDestG
    have u2 := cell_written (v := consumed) u1.2
    have g2 := cell_writeOut_sep (xs := lengthBytes consumed) g1 (separate_symm sUG) (len8 _) u1.2
    have g3 := cell_written (v := gotV) g2.2
    have u3 := cell_writeOut_sep (xs := lengthBytes gotV) u2 sUG (len8 _) g2.2
    have callerCell : ∀ (q : BPtr) (v : UInt64), LengthCell h q v → Separate q 8 dest capacity.toNat →
        (∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c < h.nextBlk) →
        LengthCell (writeOut (writeOut (writeOut (cells2 h capacity n) dest out) (cellPtr (cellRaw h))
          (lengthBytes consumed)) (cellPtr h) (lengthBytes gotV)) q v := by
      intro q v c sq qb
      have c1 := cell_writeOut_sep (xs := out) (kept.cell_of c) sq outLe wDestG
      have c2 := cell_writeOut_sep (xs := lengthBytes consumed) c1 (separate_symm (sepCells q qb).2) (len8 _) u1.2
      exact cell_writeOut_sep (xs := lengthBytes gotV) c2 (separate_symm (sepCells q qb).1) (len8 _) g2.2
    have sE := callerCell sourceLen n scell sep.2.2.2.1 slB
    have dE := callerCell destLen capacity dcell sep.2.1 dlB
    have run := runTo gotV consumed (same_cell sm g3) (same_cell sm u3) (same_cell sm sE) (same_cell sm dE)
    -- the caller stores
    have sC1 := cell_writeOut_sep (xs := out) scell sep.2.2.2.1 outLe wDest
    have dC1 := cell_writeOut_sep (xs := out) dcell sep.2.1 outLe wDest
    have dC2 := cell_writeOut_sep (xs := lengthBytes consumed) dC1 sep.2.2.2.2.2 (len8 _) sC1.2
    refine ⟨rc, _, run, fun b => absurd (by
      rcases b with b | b | b | b
      · exact absurd b sl
      · exact absurd b dl
      · exact Or.inl b
      · exact Or.inr b) badW, fun _ _ _ _ => ?_⟩
    refine ⟨out, usedN, gotV, consumed, writeOut h dest out, _, _, agree.store_in S1 (keepOf dest destB),
      store_writeOut (by rw [lengthBytes_length]; exact sC1.2), store_writeOut (by rw [lengthBytes_length]; exact dC2.2),
      ?_, unc, counts, ?_⟩
    · have s2 := same_writeOut_both (same_writeOut_both sm sourceLen (lengthBytes consumed)) destLen
        (lengthBytes gotV)
      have a1 := agree.writeOut_both (xs := out) (keepOf dest destB)
      have a2 := a1.write_out (xs := lengthBytes consumed) (p := cellPtr (cellRaw h))
        (fun r i hp c hc kc => by
          simp only [cellPtr, cellRaw, Ptr.ref.injEq] at hp; obtain ⟨rfl, -⟩ := hp
          simp only [BRef.block, Option.some.injEq] at hc; exact kc.2 hc.symm)
      have a3 := a2.write_out (xs := lengthBytes gotV) (p := cellPtr h)
        (fun r i hp c hc kc => by
          simp only [cellPtr, Ptr.ref.injEq] at hp; obtain ⟨rfl, -⟩ := hp
          simp only [BRef.block, Option.some.injEq] at hc; exact kc.1 hc.symm)
      have a4 := a3.writeOut_both (xs := lengthBytes consumed) (keepOf sourceLen slB)
      have a5 := a4.writeOut_both (xs := lengthBytes gotV) (keepOf destLen dlB)
      have notKeep : ∀ q : BPtr, (∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c < h.nextBlk) →
          ∀ r i, q = .ref r i → (∀ c, BRef.block r = some c → c < h.nextBlk) ∨ ∃ j, r = .blk j :=
        fun q qb r i hq => Or.inl (qb r i hq)
      have cellBlk : ∀ (h' : Heap), ∀ r i, cellPtr h' = .ref r i →
          (∀ c, BRef.block r = some c → c < h.nextBlk) ∨ ∃ j, r = .blk j :=
        fun h' r i hp => Or.inr ⟨h'.nextBlk, by simp only [cellPtr, Ptr.ref.injEq] at hp; exact hp.1.symm⟩
      have xk := x'k _ (x'k _ (x'k _ (x'k _ (x'k _ Gnone dest out (notKeep dest destB)) (cellPtr (cellRaw h))
        (lengthBytes consumed) (cellBlk _)) (cellPtr h) (lengthBytes gotV) (cellBlk _)) sourceLen
        (lengthBytes consumed) (notKeep sourceLen slB)) destLen (lengthBytes gotV) (notKeep destLen dlB)
      have gl : ∀ (X : Heap) (q : BPtr) (xs : List UInt8), (writeOut X q xs).nextBlk = X.nextBlk ∧
          (writeOut X q xs).nalloc = X.nalloc := fun X q xs =>
        ⟨(writeOut_globals X q xs).2.2.2.1, (writeOut_globals X q xs).2.2.2.2.1⟩
      refine same_without_two s2 a5 ?_ ?_ xk ?_ ?_
      · rw [writeOut_live, writeOut_live, writeOut_live]; exact hk0
      · rw [writeOut_live, writeOut_live, writeOut_live]; exact hk1
      · simp only [(gl _ _ _).1, (cells2_others h capacity n).2.2.2.2.2.2.2.2.2.2.1]; omega
      · simp only [(gl _ _ _).2, (cells2_others h capacity n).2.2.2.2.2.2.2.2.2.1]; exact Nat.le_refl _
    · intro hm
      obtain ⟨j, lo, hi, bad⟩ := mem' hm
      refine ⟨j, by rw [(cells2_others h capacity n).2.2.2.2.2.2.2.2.2.1] at lo; exact lo, ?_, ?_⟩
      · simp only [freed2, epiW, (writeOut_globals _ _ _).2.2.2.2.1]; exact hi
      · rw [(cells2_others h capacity n).2.2.2.2.2.2.2.1] at bad; exact bad

theorem singleWrap_uncompress : uncompress = singleWrap uncompress2 := rfl

/-- `int uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)`,
from the decoder facts of batch 3 (`DecoderFacts`), which are explicit hypotheses. -/
theorem uncompress_of_facts (facts : DecoderFacts) : Goal.uncompress := by
  unfold Goal.uncompress
  rw [singleWrap_uncompress]
  exact single_of_counted (uncompress2_of_facts facts)

end ZlibF.Spec.Public.Proofs.Uncompress
