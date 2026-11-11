import ZlibF.Proof.«public-uncompress2-z»

/-!
# uncompr.c: local length cells of the wrappers

`uncompress2`, `uncompress_z` and `uncompress` keep their counts in automatic 8-byte
cells. A cell takes the next block of a `Fresh` heap without an allocator attempt and
holds the stored value; freeing it leaves the caller heap entry by entry.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Inflate.Spec Zlib.Uncompr
set_option autoImplicit false

/-- The heap with a local cell holding `v` at the next block. -/
def cellHeap (h : Heap) (v : UInt64) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (lengthBytes v).toArray)
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk + 1 }

/-- The pointer of the local cell. -/
def cellPtr (h : Heap) : BPtr := .ref (.blk h.nextBlk) 0

/-- The heap right after the local cell is made, before the store. -/
def cellRaw (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)))
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk + 1 }

theorem alloc_cell_run {h : Heap} (fresh : Fresh h) : allocLocal 8 h = .ok (cellPtr h, cellRaw h) := by
  have slot : h.slotUsed h.nextBlk = false := Heap.slotUsed_eq_false.2 (fresh h.nextBlk (Nat.le_refl _))
  unfold allocLocal allocBytes; rw [slot]; rfl

theorem store_cell_run (h : Heap) (v : UInt64) : store64 (cellPtr h) v (cellRaw h) = .ok ((), cellHeap h v) := by
  have g : Space.get (cellRaw h) (BRef.blk h.nextBlk) =
      some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)) := by
    simp [Space.get, cellRaw]
  rw [cellPtr, store64_ref g (by simp [Space.ro, cellRaw]) (by simp)]
  congr 2
  rw [store64Array_eq _ _ _ (by simp)]
  simp [Space.put, cellHeap, cellRaw, upd_upd]
  congr 2

theorem cell_alloc_store {h : Heap} (fresh : Fresh h) (v : UInt64) :
    (do let c ← allocLocal 8; store64 c v; pure c : M BPtr) h = .ok (cellPtr h, cellHeap h v) := by
  have slot : h.slotUsed h.nextBlk = false := Heap.slotUsed_eq_false.2 (fresh h.nextBlk (Nat.le_refl _))
  have run : allocLocal 8 h = .ok (cellPtr h, { h with
      bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)))
      ro := upd h.ro h.nextBlk false
      nextBlk := h.nextBlk + 1 }) := by
    unfold allocLocal allocBytes; rw [slot]; rfl
  simp only [bind_app, run, pure_app]
  have g : Space.get ({ h with
      bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)))
      ro := upd h.ro h.nextBlk false
      nextBlk := h.nextBlk + 1 } : Heap) (BRef.blk h.nextBlk) =
      some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)) := by
    simp [Space.get]
  rw [cellPtr, store64_ref g (by simp [Space.ro]) (by simp)]
  simp only []
  congr 2
  rw [store64Array_eq _ _ _ (by simp)]
  simp [Space.put, cellHeap, upd_upd]
  congr 2

theorem cellHeap_live (h : Heap) (v : UInt64) (b : Nat) :
    (cellHeap h v).live b ↔ h.live b ∨ b = h.nextBlk := by
  simp only [cellHeap, Heap.live, upd_apply]
  by_cases e : b = h.nextBlk
  · subst e; simp
  · simp [e]

theorem cellHeap_fresh {h : Heap} (fresh : Fresh h) (v : UInt64) : Fresh (cellHeap h v) := by
  intro b hb live
  rw [cellHeap_live] at live
  simp only [cellHeap] at hb
  rcases live with l | l
  · exact fresh b (by omega) l
  · omega

theorem cellHeap_uniq {h : Heap} (fresh : Fresh h) (u : Uniq h) (v : UInt64) : Uniq (cellHeap h v) := by
  intro b
  have ub := u b
  have n0 := fresh h.nextBlk (Nat.le_refl _)
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at n0
  simp only [cellHeap, upd_apply]
  by_cases e : b = h.nextBlk
  · subst e; simp [n0.2.1, n0.2.2.1, n0.2.2.2.1, n0.2.2.2.2.1, n0.2.2.2.2.2.1, n0.2.2.2.2.2.2]
  · simpa [e] using ub

theorem cellHeap_kept {h : Heap} (fresh : Fresh h) (v : UInt64) : ByteViewsKept h (cellHeap h v) where
  bytes b hb := by
    have ne : b ≠ h.nextBlk := fun e => fresh b (by omega) (Or.inl hb)
    simp [cellHeap, upd_ne _ _ _ _ ne]
  dstates := rfl
  static := rfl
  borrow := rfl

theorem cellHeap_fit {h : Heap} (fresh : Fresh h) (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (v : UInt64) :
    ZlibF.PlatformMemory.ByteObjectsFit (cellHeap h v) := by
  intro rr a g
  cases rr with
  | blk c =>
    by_cases e : c = h.nextBlk
    · subst e
      simp [Space.get, cellHeap] at g
      subst g
      simp [lengthBytes_length, ZlibF.PlatformMemory.byteObjectLimit]
    · simp only [Space.get, cellHeap, upd_ne _ _ _ _ e] at g
      exact fit (.blk c) a g
  | str i => exact fit (.str i) a g
  | dstate_depth i => exact fit (.dstate_depth i) a g
  | st_dist_code => exact fit .st_dist_code a g
  | st_length_code => exact fit .st_length_code a g

theorem cellHeap_cell (h : Heap) (v : UInt64) : LengthCell (cellHeap h v) (cellPtr h) v := by
  refine ⟨Or.inr ⟨.blk h.nextBlk, 0, (lengthBytes v).toArray, rfl, by simp [Space.get, cellHeap],
    by simp [lengthBytes_length], ?_⟩, Or.inr ⟨.blk h.nextBlk, 0, (lengthBytes v).toArray, rfl,
    by simp [Space.get, cellHeap], by simp [Space.ro, cellHeap], by simp [lengthBytes_length]⟩⟩
  simp only [List.toList_toArray, List.drop_zero]
  rw [List.take_of_length_le (by rw [lengthBytes_length]; exact Nat.le_refl _)]
  rfl

theorem cellHeap_globals {h : Heap} (g : LibraryGlobals h) (v : UInt64) : LibraryGlobals (cellHeap h v) := g

/-- A pointer into a caller block is separate from the local cell. -/
theorem separate_cell {h : Heap} {p : BPtr} {n : Nat}
    (blockOf : ∀ i, p ≠ .ref (.blk h.nextBlk) i) : Separate (cellPtr h) 8 p n := by
  by_cases n0 : n = 0
  · exact Or.inr (Or.inl n0)
  right; right
  cases p with
  | null => simp [cellPtr]
  | ref r i =>
    simp only [cellPtr]
    left
    intro e
    exact blockOf i (by rw [e])

/-- The caller heap and the heap with the cell agree off the cell's block. -/
theorem cellHeap_agree {h : Heap} (fresh : Fresh h) (v : UInt64) :
    Agree (· ≠ h.nextBlk) h (cellHeap h v) := by
  refine ⟨fun b ne => ⟨by simp [cellHeap, upd_ne _ _ _ _ ne], rfl, rfl, rfl, rfl, rfl, rfl,
    by simp [cellHeap, upd_ne _ _ _ _ ne]⟩, rfl, rfl, rfl, rfl⟩

/-- An extra write into the cell's block keeps agreement off that block. -/
theorem Agree.write_right {k : Nat} {X X' : Heap} (a : Agree (· ≠ k) X X') {p : BPtr} {xs : List UInt8}
    (inK : ∀ r i, p = .ref r i → BRef.block r = some k) : Agree (· ≠ k) X (writeOut X' p xs) := by
  obtain ⟨gS, gA, gG, -, -, gB⟩ := writeOut_globals X' p xs
  refine ⟨fun b ne => (a.blocks b ne).trans (writeOut_same_other b (fun r i hp hb => ?_)), ?_, ?_, ?_, ?_⟩
  · rw [inK r i hp] at hb; cases hb; exact ne rfl
  · rw [gS]; exact a.static
  · rw [gA]; exact a.allocOk
  · rw [gG]; exact a.garbage
  · rw [gB]; exact a.borrow

/-- A store on the heap with the cell is a store on the caller heap. -/
theorem Agree.store_left {k : Nat} {X X' X₁ : Heap} (a : Agree (· ≠ k) X X') {p : BPtr} {xs : List UInt8}
    (st : Store X' p xs X₁) (notK : ∀ r i, p = .ref r i → ∀ c, BRef.block r = some c → c ≠ k) :
    Store X p xs (writeOut X p xs) := by
  rcases st with ⟨rfl, -⟩ | ⟨r, i, arr, rfl, g, ro, fit, -⟩
  · rw [writeOut_nil]; exact Or.inl ⟨rfl, rfl⟩
  · have e := a.get (notK r i rfl)
    exact store_writeOut (Or.inr ⟨r, i, arr, rfl, by rw [← e.1]; exact g, by rw [← e.2]; exact ro, fit⟩)

/-- A store is a write. -/
theorem store_fun {h h' : Heap} {p : BPtr} {xs : List UInt8} (st : Store h p xs h') : h' = writeOut h p xs := by
  by_cases ne : xs = []
  · subst ne
    rcases st with ⟨-, rfl⟩ | ⟨r, i, a, rfl, g, -, fit, rfl⟩
    · rw [writeOut_nil]
    · rw [writeOut_nil]
      have arr : a.extract 0 i ++ ([] : List UInt8).toArray ++ a.extract (i + ([] : List UInt8).length) a.size = a := by
        apply Array.ext_getElem?
        intro j
        rw [written_get? a i [] fit]
        by_cases lo : j < i
        · simp [lo]
        · simp [lo]
      rw [arr]
      exact put_self_any g
  · exact store_eq_writeOut st ne

/-- The final comparison carries over once the cell's block is freed. -/
theorem same_without_cell {k : Nat} {X X' Y' : Heap} (s : SameObjectsUpToTableShape X' Y')
    (a : Agree (· ≠ k) X X') (xk : ¬ X.live k)
    (x'k : X'.words k = none ∧ X'.streams k = none ∧ X'.gzheaders k = none ∧ X'.dstates k = none ∧
      X'.istates k = none ∧ X'.gzstates k = none)
    (nb : X.nextBlk ≤ X'.nextBlk) (na : X.nalloc ≤ X'.nalloc) :
    SameObjectsUpToTableShape X { Y' with bytes := upd Y'.bytes k none } := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := s
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at xk
  have at_b : ∀ b, b ≠ k → SameAt X X' b := a.blocks
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    simp only [upd_apply]
    split
    · rename_i e; subst e; exact xk.1.symm
    · rename_i ne; rw [s1 b]; exact (at_b b ne).1
  · intro b
    by_cases ne : b = k
    · subst ne; rw [s2 b, x'k.1, xk.2.1]
    · rw [s2 b]; exact (at_b b ne).2.1
  · intro b live
    have ne : b ≠ k := by intro e; subst e; exact (by simp [Heap.live, xk.1, xk.2.1, xk.2.2.1, xk.2.2.2.1, xk.2.2.2.2.1, xk.2.2.2.2.2.1, xk.2.2.2.2.2.2] at live)
    have sb := at_b b ne
    have l' : X'.live b := by
      obtain ⟨t1, t2, t3, t4, t5, t6, t7, -⟩ := sb
      simp only [Heap.live] at live ⊢
      rw [t1, t2, t3, t4, t5, t6, t7]; exact live
    rw [show ({ Y' with bytes := upd Y'.bytes k none } : Heap).ro b = Y'.ro b from rfl, s3 b l']
    exact sb.2.2.2.2.2.2.2
  · intro b
    by_cases ne : b = k
    · subst ne; rw [s4 b, x'k.2.1, xk.2.2.1]
    · rw [s4 b]; exact (at_b b ne).2.2.1
  · intro b
    by_cases ne : b = k
    · subst ne; rw [s5 b, x'k.2.2.1, xk.2.2.2.1]
    · rw [s5 b]; exact (at_b b ne).2.2.2.1
  · intro b
    by_cases ne : b = k
    · subst ne; rw [s6 b, x'k.2.2.2.1, xk.2.2.2.2.1]
    · rw [s6 b]; exact (at_b b ne).2.2.2.2.1
  · intro b
    by_cases ne : b = k
    · subst ne; rw [s7 b, x'k.2.2.2.2.1, xk.2.2.2.2.2.1]
    · rw [s7 b]; exact (at_b b ne).2.2.2.2.2.1
  · intro b
    by_cases ne : b = k
    · subst ne; rw [s8 b, x'k.2.2.2.2.2, xk.2.2.2.2.2.2]
    · rw [s8 b]; exact (at_b b ne).2.2.2.2.2.2.1
  · show Y'.static = X.static; rw [s9]; exact a.static
  · show Y'.allocOk = X.allocOk; rw [s10]; exact a.allocOk
  · show Y'.garbage = X.garbage; rw [s11]; exact a.garbage
  · exact Nat.le_trans nb s12
  · exact Nat.le_trans na s13

theorem freeB_blk_run {H : Heap} {b : Nat} {a : Array UInt8} (hb : H.bytes b = some a) (ro : H.ro b = false) :
    freeB (.ref (.blk b) 0) H = .ok ((), { H with bytes := upd H.bytes b none }) := by
  simp [freeB, hb, ro]

/-- A pointer through which the caller heap reads is not into the next block. -/
theorem not_cell_block {h : Heap} (fresh : Fresh h) {p : BPtr}
    (reads : ∀ r i, p = .ref r i → ∃ a, Space.get h r = some a) :
    ∀ r i, p = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk := by
  intro r i hp c hc e
  obtain ⟨a, g⟩ := reads r i hp
  exact fresh c (by omega) (view_block_live g c hc)

theorem writeOut_blk_others (X : Heap) (b i : Nat) (xs : List UInt8) :
    (writeOut X (.ref (.blk b) i) xs).words = X.words ∧ (writeOut X (.ref (.blk b) i) xs).streams = X.streams ∧
    (writeOut X (.ref (.blk b) i) xs).gzheaders = X.gzheaders ∧
    (writeOut X (.ref (.blk b) i) xs).dstates = X.dstates ∧
    (writeOut X (.ref (.blk b) i) xs).istates = X.istates ∧
    (writeOut X (.ref (.blk b) i) xs).gzstates = X.gzstates := by
  simp only [writeOut]
  split
  · split <;> simp [Space.put]
  · simp

theorem writeOut_some {X : Heap} {r : BRef} {i : Nat} {xs : List UInt8} {a : Array UInt8}
    (g : Space.get X r = some a) (ne : xs ≠ []) :
    writeOut X (.ref r i) xs = Space.put X r (a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size) := by
  simp [writeOut, g, ne]

theorem writeOut_none {X : Heap} {r : BRef} {i : Nat} {xs : List UInt8} (g : Space.get X r = none) :
    writeOut X (.ref r i) xs = X := by
  simp [writeOut, g]

/-- Writing the same array through a byte block keeps two heaps equal entry by entry. -/
theorem same_put_blk {X Y : Heap} (s : SameObjectsUpToTableShape X Y) (c : Nat) (w : Array UInt8)
    (live : X.bytes c ≠ none) :
    SameObjectsUpToTableShape (Space.put X (BRef.blk c) w) (Space.put Y (BRef.blk c) w) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := s
  refine ⟨fun b => ?_, s2, fun b l => s3 b ?_, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩
  · simp only [Space.put, upd_apply]
    split
    · rfl
    · exact s1 b
  · simp only [Space.put, Heap.live, upd_apply] at l ⊢
    by_cases e : b = c
    · subst e; left; exact live
    · simpa [e] using l

theorem same_put_depth {X Y : Heap} (s : SameObjectsUpToTableShape X Y) (c : Nat) (w : Array UInt8) :
    SameObjectsUpToTableShape (Space.put X (BRef.dstate_depth c) w) (Space.put Y (BRef.dstate_depth c) w) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := s
  have g := s6 c
  simp only [Space.put]
  rw [g]
  cases e : X.dstates c with
  | none => exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩
  | some st =>
    refine ⟨s1, s2, fun b l => s3 b ?_, s4, s5, fun b => ?_, s7, s8, s9, s10, s11, s12, s13⟩
    · simp only [Heap.live, upd_apply] at l ⊢
      by_cases eb : b = c
      · subst eb; right; right; right; right; left; rw [e]; simp
      · simpa [eb] using l
    · simp only [upd_apply]
      split
      · rfl
      · exact s6 b

/-- The same write keeps two heaps equal entry by entry. -/
theorem same_writeOut_both {X Y : Heap} (s : SameObjectsUpToTableShape X Y) (p : BPtr) (xs : List UInt8) :
    SameObjectsUpToTableShape (writeOut X p xs) (writeOut Y p xs) := by
  cases p with
  | null => exact s
  | ref r i =>
    by_cases ne : xs = []
    · subst ne; rw [writeOut_nil, writeOut_nil]; exact s
    cases r with
    | blk c =>
      have g : Space.get Y (BRef.blk c) = Space.get X (BRef.blk c) := s.1 c
      cases gx : Space.get X (BRef.blk c) with
      | none => rw [writeOut_none gx, writeOut_none (by rw [g, gx])]; exact s
      | some a =>
        rw [writeOut_some gx ne, writeOut_some (by rw [g, gx]) ne]
        exact same_put_blk s c _ (by simp only [Space.get] at gx; rw [gx]; simp)
    | dstate_depth c =>
      have g : Space.get Y (BRef.dstate_depth c) = Space.get X (BRef.dstate_depth c) := by
        simp only [Space.get]; rw [s.2.2.2.2.2.1 c]
      cases gx : Space.get X (BRef.dstate_depth c) with
      | none => rw [writeOut_none gx, writeOut_none (by rw [g, gx])]; exact s
      | some a =>
        rw [writeOut_some gx ne, writeOut_some (by rw [g, gx]) ne]
        exact same_put_depth s c _
    | str k =>
      have e : ∀ Z : Heap, writeOut Z (.ref (.str k) i) xs = Z := by
        intro Z; cases gz : Space.get Z (BRef.str k) with
        | none => exact writeOut_none gz
        | some a => rw [writeOut_some gz ne]; rfl
      rw [e, e]; exact s
    | st_dist_code =>
      have e : ∀ Z : Heap, writeOut Z (.ref .st_dist_code i) xs = Z := by
        intro Z; rw [writeOut_some (a := Z.static.dist_code) rfl ne]; rfl
      rw [e, e]; exact s
    | st_length_code =>
      have e : ∀ Z : Heap, writeOut Z (.ref .st_length_code i) xs = Z := by
        intro Z; rw [writeOut_some (a := Z.static.length_code) rfl ne]; rfl
      rw [e, e]; exact s

end ZlibF.Spec.Public.Proofs.Uncompress
