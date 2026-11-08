import ZlibF.Math.DeflatePushCost
import ZlibF.Math.DeflateWeightedMass
import ZlibF.Math.DeflateRankedLengths

/-! # Transporting actual leaf-rank budgets to original source symbols -/

namespace ZlibF.Math.DeflatePush
open Zlib.Trees.Proofs.GB
open Zlib.Trees.HuffmanAbstract
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A symbol-form class budget uses alphabet capacity, not the number of
occurrences in the block. Unused original symbols contribute zero budget. -/
def SymbolFibPush (alphabet weight : Nat) (frequency length : Nat → Nat) : Prop :=
  ∃ classes origin : Nat → Nat,
    (∀ v, v < alphabet → frequency v ≠ 0 → CodeClass weight (frequency v) (length v) (classes v) (origin v)) ∧
    mass (fun v => if frequency v = 0 then 0 else pushCostA (classes v) (origin v)) alphabet + 1 ≤ alphabet

open Classical in
noncomputable def nodePosition (H : Nat → Nat) (hm J v : Nat) : Nat :=
  if found : ∃ i, i < 2 * J ∧ H (hm + 1 + i) = v then Classical.choose found else 0

theorem nodePosition_spec {H : Nat → Nat} {hm J v : Nat}
    (found : ∃ i, i < 2 * J ∧ H (hm + 1 + i) = v) :
    nodePosition H hm J v < 2 * J ∧ H (hm + 1 + nodePosition H hm J v) = v := by
  unfold nodePosition
  rw [dif_pos found]
  exact Classical.choose_spec found

theorem mass_eq_rs (f : Nat → Nat) (n : Nat) : mass f n = rs f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [mass, rs_succ, ih]

theorem rs_eq_sumR (f : Nat → Nat) (n : Nat) : rs (fun i => f (i + 1)) n = sumR f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rs_succ, sumR, ih]

/-- Original used symbols inject into actual retained leaf ranks. Their
frequencies agree with the pre-code tree. Restricting the rank class budget
therefore gives a valid symbol budget, even when dummy leaves were added. -/
theorem SymbolFibPush.of_ranked_tree {H treeFrequency frequency length : Nat → Nat}
    {hm J alphabet maxc weight : Nat} (shape : PShape H hm J alphabet maxc)
    (used : ∀ v, v < alphabet → frequency v ≠ 0 → v ≤ maxc ∧ ∃ q, hm < q ∧ q < 573 ∧ H q = v)
    (frequencies : ∀ v, v < alphabet → frequency v ≠ 0 → treeFrequency v = frequency v)
    (ranked : FibPushR (LeafRank.count H hm J maxc) weight
      (LeafRank.value H treeFrequency hm J maxc) (LeafRank.value H length hm J maxc)) :
    SymbolFibPush alphabet weight frequency length := by
  obtain ⟨classes, origin, classified, budget⟩ := ranked
  let ranks := LeafRank.count H hm J maxc
  let rank := fun v => cntL (LeafRank.selected H hm maxc) (nodePosition H hm J v + 1)
  have boundary := shape.hm_eq
  have rankSpec (v : Nat) (bound : v < alphabet) (nonzero : frequency v ≠ 0) :
      1 ≤ rank v ∧ rank v ≤ ranks ∧ H (hm + 1 + LeafRank.index H hm J maxc (rank v)) = v := by
    obtain ⟨symbol, q, lower, upper, value⟩ := used v bound nonzero
    have found : ∃ i, i < 2 * J ∧ H (hm + 1 + i) = v :=
      ⟨q - hm - 1, by omega, by rw [show hm + 1 + (q - hm - 1) = q by omega]; exact value⟩
    have position := nodePosition_spec found
    have selected : LeafRank.selected H hm maxc (nodePosition H hm J v) = true := by
      simp only [LeafRank.selected, position.2, symbol, decide_true]
    have bounds := rank_bounds (LeafRank.selected H hm maxc) position.1 selected
    have inverse := idxR_rank (LeafRank.selected H hm maxc) position.1 selected
    refine ⟨bounds.1, bounds.2, ?_⟩
    change H (hm + 1 + idxR (LeafRank.selected H hm maxc) (2 * J) (rank v)) = v
    rw [inverse, position.2]
  have rankInjective (v v' : Nat) (bound : v < alphabet) (bound' : v' < alphabet)
      (nonzero : frequency v ≠ 0) (nonzero' : frequency v' ≠ 0) (same : rank v = rank v') : v = v' := by
    have node := (rankSpec v bound nonzero).2.2
    have node' := (rankSpec v' bound' nonzero').2.2
    rw [same] at node
    exact node.symm.trans node'
  refine ⟨fun v => classes (rank v), fun v => origin (rank v), ?_, ?_⟩
  · intro v bound nonzero
    obtain ⟨lower, upper, node⟩ := rankSpec v bound nonzero
    have claim := classified (rank v) lower upper
    change CodeClass weight (LeafRank.value H treeFrequency hm J maxc (rank v))
      (LeafRank.value H length hm J maxc (rank v)) (classes (rank v)) (origin (rank v)) at claim
    have weightValue : LeafRank.value H treeFrequency hm J maxc (rank v) = frequency v := by
      unfold LeafRank.value
      rw [node, frequencies v bound nonzero]
    have lengthValue : LeafRank.value H length hm J maxc (rank v) = length v := by
      unfold LeafRank.value
      rw [node]
    rwa [weightValue, lengthValue] at claim
  · let P := fun v => if frequency v = 0 then ranks + v else rank v - 1
    let F := fun q => if q < ranks then pushCostA (classes (q + 1)) (origin (q + 1)) else 0
    have range (v : Nat) (bound : v < alphabet) : P v < ranks + alphabet := by
      dsimp only [P]
      by_cases zero : frequency v = 0
      · rw [if_pos zero]; omega
      · rw [if_neg zero]
        have spec := rankSpec v bound zero
        have positiveAlphabet := shape.maxc_lt
        omega
    have injective : ∀ v v', v < alphabet → v' < alphabet → P v = P v' → v = v' := by
      intro v v' bound bound' same
      dsimp only [P] at same
      by_cases zero : frequency v = 0 <;> by_cases zero' : frequency v' = 0
      · simp only [zero, zero', ite_true] at same; omega
      · simp only [zero, zero', ite_true, ite_false] at same
        have spec := rankSpec v' bound' zero'
        omega
      · simp only [zero, zero', ite_true, ite_false] at same
        have spec := rankSpec v bound zero
        omega
      · simp only [zero, zero', ite_false] at same
        have spec := rankSpec v bound zero
        have spec' := rankSpec v' bound' zero'
        exact rankInjective v v' bound bound' zero zero' (by omega)
    have costs (v : Nat) (bound : v < alphabet) :
        (if frequency v = 0 then 0 else pushCostA (classes (rank v)) (origin (rank v))) = F (P v) := by
      dsimp only [P, F]
      by_cases zero : frequency v = 0
      · simp only [zero, ite_true]
        rw [if_neg (by omega)]
      · simp only [zero, ite_false]
        have spec := rankSpec v bound zero
        rw [if_pos (by omega), Nat.sub_add_cancel spec.1]
    have transported : rs (fun v => F (P v)) alphabet ≤ rs F (ranks + alphabet) := by
      rw [rs_image P F alphabet (ranks + alphabet) range]
      apply rs_le
      intro q _bound
      have multiplicity := cnt_le_one P alphabet q injective
      have scaled := Nat.mul_le_mul_right (F q) multiplicity
      simpa only [Nat.one_mul] using scaled
    have zeros : rs (fun i => F (ranks + i)) alphabet = 0 := by
      apply rs_eq_zero
      intro i _bound
      dsimp only [F]
      rw [if_neg (by omega)]
    have allRanks : rs F (ranks + alphabet) = sumR (fun r => pushCostA (classes r) (origin r)) ranks := by
      rw [rs_split, zeros, Nat.add_zero]
      have points : rs F ranks = rs (fun i => pushCostA (classes (i + 1)) (origin (i + 1))) ranks := by
        apply rs_congr
        intro i bound
        dsimp only [F]
        rw [if_pos bound]
      rw [points]
      exact rs_eq_sumR (fun r => pushCostA (classes r) (origin r)) ranks
    have original : mass (fun v => if frequency v = 0 then 0 else pushCostA (classes (rank v)) (origin (rank v))) alphabet =
        rs (fun v => F (P v)) alphabet := by
      rw [mass_eq_rs]
      exact rs_congr costs
    have rankCount : ranks ≤ alphabet := by
      have bound := nLeaves_le shape
      have sameCount : ranks = nLeaves H hm J maxc := by
        dsimp only [ranks, LeafRank.count, cntL, nLeaves]
        apply rs_congr
        intro i _bound
        simp only [LeafRank.selected, decide_eq_true_eq]
      rw [sameCount]
      have symbols := shape.maxc_lt
      omega
    calc
      mass (fun v => if frequency v = 0 then 0 else pushCostA (classes (rank v)) (origin (rank v))) alphabet + 1 =
          rs (fun v => F (P v)) alphabet + 1 := congrArg (fun n => n + 1) original
      _ ≤ rs F (ranks + alphabet) + 1 := Nat.add_le_add_right transported 1
      _ = sumR (fun r => pushCostA (classes r) (origin r)) ranks + 1 := congrArg (fun n => n + 1) allRanks
      _ ≤ ranks := budget
      _ ≤ alphabet := rankCount

/-- Only in-alphabet frequencies participate in the symbol budget. -/
theorem SymbolFibPush.congr_frequency {alphabet weight : Nat} {frequency other length : Nat → Nat}
    (budget : SymbolFibPush alphabet weight frequency length)
    (same : ∀ v, v < alphabet → other v = frequency v) : SymbolFibPush alphabet weight other length := by
  obtain ⟨classes, origin, classified, total⟩ := budget
  refine ⟨classes, origin, ?_, ?_⟩
  · intro v bound nonzero
    rw [same v bound] at nonzero ⊢
    exact classified v bound nonzero
  · have counts : mass (fun v => if other v = 0 then 0 else pushCostA (classes v) (origin v)) alphabet =
        mass (fun v => if frequency v = 0 then 0 else pushCostA (classes v) (origin v)) alphabet := by
      apply mass_congr
      intro v bound
      rw [same v bound]
    rw [counts]
    exact total

/-- An unused sentinel can change without affecting any originally used
symbol. Only nonzero-frequency lengths enter the class inequalities. -/
theorem SymbolFibPush.congr_length {alphabet weight : Nat} {frequency length other : Nat → Nat}
    (budget : SymbolFibPush alphabet weight frequency length)
    (same : ∀ v, v < alphabet → frequency v ≠ 0 → other v = length v) :
    SymbolFibPush alphabet weight frequency other := by
  obtain ⟨classes, origin, classified, total⟩ := budget
  refine ⟨classes, origin, ?_, total⟩
  intro v bound nonzero
  rw [same v bound nonzero]
  exact classified v bound nonzero

end ZlibF.Math.DeflatePush
