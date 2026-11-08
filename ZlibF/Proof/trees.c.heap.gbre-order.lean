import ZlibF.Proof.«trees.c.heap.gbre»

/-! # The order retained by source length reassignment -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- Lengths already assigned in the descending scan are nondecreasing in
heap position. Internal nodes are skipped and do not enter the order. -/
def ReOrdered (H len : Nat → Nat) (maxc hc : Nat) : Prop :=
  ∀ q q', hc ≤ q → q ≤ q' → q' < 573 → H q ≤ maxc → H q' ≤ maxc → len (H q) ≤ len (H q')

theorem ReOrdered.initial (H len : Nat → Nat) (maxc : Nat) : ReOrdered H len maxc 573 := by
  intro q q' lower between upper _leaf _leaf'
  omega

/-- The existing exact scanned counts imply that every already assigned
leaf has length between the current bit level and the maximum level. -/
theorem ReSt.processed_range {tk : TK} {e0 e : DeflateState} {hm J elems maxc L hc b n : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64}
    (shape : PShape (Hn e0) hm J elems maxc) (level : b ≤ L)
    (state : ReSt tk e0 hm J maxc L xb c opt0 hc b n e) :
    ∀ q, hc ≤ q → q < 573 → Hn e0 q ≤ maxc →
      b ≤ curL (tk.arr e) (Hn e0 q) ∧ curL (tk.arr e) (Hn e0 q) ≤ L := by
  obtain ⟨T, O, fields, _size, hcLower, _hcUpper, _count, _cost, _freq, _outside, counts, _total⟩ := state
  rw [fields, tk_arr_mkP2]
  intro q lower upper leaf
  have boundary := shape.hm_eq
  have index : hm + 1 + (q - hm - 1) = q := by omega
  have atLeastOne := le_rs
    (F := fun i => if hc ≤ hm + 1 + i ∧ Hn e0 (hm + 1 + i) ≤ maxc ∧
      curL T (Hn e0 (hm + 1 + i)) = curL T (Hn e0 q) then 1 else 0)
    (n := 2 * J) (i := q - hm - 1) (by omega)
  rw [index, if_pos ⟨lower, leaf, rfl⟩] at atLeastOne
  change 1 ≤ scnt (Hn e0) hm maxc J hc (curL T) (curL T (Hn e0 q)) at atLeastOne
  rw [counts] at atLeastOne
  by_cases above : b < curL T (Hn e0 q) ∧ curL T (Hn e0 q) ≤ L
  · exact ⟨by omega, above.2⟩
  · rw [if_neg above] at atLeastOne
    by_cases same : curL T (Hn e0 q) = b
    · omega
    · rw [if_neg same] at atLeastOne
      omega

/-- Skipping an internal node extends the scanned region without adding a
leaf to its order. -/
theorem ReOrdered.skip {H len : Nat → Nat} {maxc hc : Nat}
    (before : ReOrdered H len maxc hc) (internal : maxc < H (hc - 1)) :
    ReOrdered H len maxc (hc - 1) := by
  intro q q' lower between upper leaf leaf'
  have notNew : q ≠ hc - 1 := by intro same; rw [same] at leaf; omega
  exact before q q' (by omega) between upper leaf leaf'

/-- Assigning the current level to the next scanned leaf preserves sorted
lengths. Distinct retained node positions prevent changing an earlier leaf.
The lower bound on processed lengths is supplied by actual scanned counts. -/
theorem ReOrdered.assign {H len next : Nat → Nat} {hm J elems maxc hc b : Nat}
    (shape : PShape H hm J elems maxc) (hcLower : hm + 2 ≤ hc) (hcUpper : hc ≤ 573)
    (before : ReOrdered H len maxc hc)
    (lower : ∀ q, hc ≤ q → q < 573 → H q ≤ maxc → b ≤ len (H q))
    (update : ∀ v, next v = if v = H (hc - 1) then b else len v) :
    ReOrdered H next maxc (hc - 1) := by
  have old (q : Nat) (lo : hc ≤ q) (hi : q < 573) : H q ≠ H (hc - 1) := by
    intro same
    have equal := shape.inj q (hc - 1) (by omega) hi (by omega) (by omega) same
    omega
  intro q q' lo between hi leaf leaf'
  by_cases new : q = hc - 1
  · by_cases same : q' = hc - 1
    · rw [new, same]
      exact Nat.le_refl _
    · have oldLower : hc ≤ q' := by omega
      rw [new, update, if_pos rfl, update, if_neg (old q' oldLower hi)]
      exact lower q' oldLower hi leaf'
  · have oldLower : hc ≤ q := by omega
    rw [update, if_neg (old q oldLower (by omega)), update, if_neg (old q' (by omega) hi)]
    exact before q q' oldLower between hi leaf leaf'

/-- At the end of reassignment every retained leaf has actually been
scanned. The exact count total excludes a skipped, still-unassigned leaf. -/
theorem ReSt.final_scanned {tk : TK} {e0 e : DeflateState} {hm J elems maxc L hc : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64}
    (ctx : RCtx tk e0 hm J elems maxc L c)
    (state : ReSt tk e0 hm J maxc L xb c opt0 hc 0 0 e) :
    ∀ q, hm + 1 ≤ q → q < 573 → Hn e0 q ≤ maxc → hc ≤ q := by
  obtain ⟨_T, _O, _fields, _size, _lower, _upper, _count, _cost, _freq, _outside, _counts, total⟩ := state
  have boundary := ctx.shape.hm_eq
  have both := stot_utot (Hn e0) hm maxc J hc
  simp only [Nat.sub_zero, ctx.c0, Nat.add_zero, Aab_zero c L ctx.c0, ctx.ctot] at total
  intro q lower upper leaf
  by_cases scanned : hc ≤ q
  · exact scanned
  · have index : hm + 1 + (q - hm - 1) = q := by omega
    have positive := le_rs
      (F := fun i => if hm + 1 + i < hc ∧ Hn e0 (hm + 1 + i) ≤ maxc then 1 else 0)
      (n := 2 * J) (i := q - hm - 1) (by omega)
    rw [index, if_pos ⟨by omega, leaf⟩] at positive
    change 1 ≤ utot (Hn e0) hm maxc J hc at positive
    omega

/-- The ordered scanned tail covers every leaf when the actual outer
loop finishes. This order is by retained heap position, ready for ranking. -/
theorem ReSt.complete_order {tk : TK} {e0 e : DeflateState} {hm J elems maxc L hc : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64}
    (ctx : RCtx tk e0 hm J elems maxc L c)
    (state : ReSt tk e0 hm J maxc L xb c opt0 hc 0 0 e)
    (ordered : ReOrdered (Hn e0) (curL (tk.arr e)) maxc hc) :
    ReOrdered (Hn e0) (curL (tk.arr e)) maxc (hm + 1) := by
  intro q q' lower between upper leaf leaf'
  exact ordered q q' (state.final_scanned ctx q lower (by omega) leaf) between upper leaf leaf'

/-- The exact scanned counts become the full final length histogram once
the outer scan has assigned every leaf. -/
theorem ReSt.final_counts {tk : TK} {e0 e : DeflateState} {hm J elems maxc L hc : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64}
    (ctx : RCtx tk e0 hm J elems maxc L c)
    (state : ReSt tk e0 hm J maxc L xb c opt0 hc 0 0 e) :
    ∀ x, blP (Hn e0) hm maxc (curL (tk.arr e)) (2 * J) x =
      if 0 < x ∧ x ≤ L then c x else 0 := by
  have scanned := state.final_scanned ctx
  obtain ⟨T, O, fields, _size, _lo, _hi, _count, _cost, _freq, _outside, counts, _total⟩ := state
  rw [fields, tk_arr_mkP2]
  have boundary := ctx.shape.hm_eq
  intro x
  have same : scnt (Hn e0) hm maxc J hc (curL T) x = blP (Hn e0) hm maxc (curL T) (2 * J) x := by
    unfold scnt blP
    apply rs_congr
    intro i bound
    by_cases leaf : Hn e0 (hm + 1 + i) ≤ maxc
    · have lower := scanned (hm + 1 + i) (by omega) (by omega) leaf
      simp only [lower, leaf, true_and]
    · simp only [leaf, false_and, and_false, ite_false]
  rw [← same, counts]
  by_cases above : 0 < x ∧ x ≤ L
  · rw [if_pos above, if_pos above]
  · rw [if_neg above, if_neg above]
    by_cases zero : x = 0
    · subst x
      rw [if_pos rfl, ctx.c0]
    · rw [if_neg zero]

end Zlib.Trees.Proofs
