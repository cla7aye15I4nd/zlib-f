import ZlibF.Math.DeflateSymbolFibPush
import ZlibF.Math.DeflateDefaultBudget

/-! # FibPush bounds positive excess of the original buffered symbols -/

namespace ZlibF.Math.DeflatePush
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

def literalExcess (length extra : Nat → Nat) (v : Nat) : Nat :=
  if v < 257 then 0 else length v + extra (v - 257) - 9

def distanceExcess (length extra : Nat → Nat) (v : Nat) : Nat := length v + extra v - 15

def symbolCost (literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode : Nat → Nat)
    (s : Symbol) : Nat :=
  if s.distance = 0 then literalLength s.value else
    literalLength (lengthCode s.value + 257) + literalExtra (lengthCode s.value) +
      distanceLength (distanceCode (s.distance - 1)) + distanceExtra (distanceCode (s.distance - 1))

/-- The integer certificates, exact original frequency histograms and the
two proved symbol budgets imply a whole-block excess bound. Extra-bit table
bounds and coefficient sums are finite data facts about the actual tables.
No translated execution contract is assumed in this pure arithmetic lemma. -/
theorem symbol_excess_from_fib (xs : List Symbol)
    (literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode : Nat → Nat)
    (literalWeight distanceWeight : Nat)
    (valid : ∀ s ∈ xs, s.Valid)
    (literalKeys : ∀ s ∈ xs, s.literalKey lengthCode < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey distanceCode = some k → k < 30)
    (literalBits : ∀ c, c < 29 → literalExtra c < 6)
    (distanceBits : ∀ c, c < 30 → distanceExtra c < 14)
    (literalLengths : ∀ v, v < 286 → literalFrequency lengthCode xs v ≠ 0 → literalLength v ≤ 15)
    (distanceLengths : ∀ v, v < 30 → distanceFrequency distanceCode xs v ≠ 0 → distanceLength v ≤ 15)
    (literalFib : SymbolFibPush 286 literalWeight (literalFrequency lengthCode xs) literalLength)
    (distanceFib : SymbolFibPush 30 distanceWeight (distanceFrequency distanceCode xs) distanceLength)
    (literalCoefficients : mass (fun v => if v < 257 then 0 else lengthCoefficient (literalExtra (v - 257))) 286 = 1921)
    (distanceCoefficients : mass (fun v => distanceCoefficient (distanceExtra v)) 30 = 1660)
    (literalTotal : literalWeight ≤ xs.length + 3) (distanceTotal : distanceWeight ≤ xs.length + 3) :
    1000 * Zlib.Trees.Overlay.bitExcess
      (xs.map (symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode)) ≤
      6257 * (xs.length + 3) := by
  let FL := literalFrequency lengthCode xs
  let FD := distanceFrequency distanceCode xs
  let GL := literalExcess literalLength literalExtra
  let GD := distanceExcess distanceLength distanceExtra
  let YL := fun v => if v < 257 then 0 else lengthCoefficient (literalExtra (v - 257))
  let YD := fun v => distanceCoefficient (distanceExtra v)
  let DC := fun s : Symbol => match s.distanceKey distanceCode with | none => 0 | some k => GD k
  obtain ⟨classL, originL, classesL, budgetL⟩ := literalFib
  obtain ⟨classD, originD, classesD, budgetD⟩ := distanceFib
  let PC_L := fun v => if FL v = 0 then 0 else pushCostA (classL v) (originL v)
  let PC_D := fun v => if FD v = 0 then 0 else pushCostA (classD v) (originD v)
  have literalBound := weighted_tree_bound FL GL YL PC_L 286 400 3 literalWeight 285 (by
    intro v bound nonzero
    by_cases low : v < 257
    · simp only [GL, literalExcess, YL, low, ite_true, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      omega
    · have code := length_code_bound (FL v) (literalLength v) (literalExtra (v - 257))
        literalWeight (classL v) (originL v) (literalLengths v bound nonzero)
        (literalBits (v - 257) (by omega)) (classesL v bound nonzero)
      simpa only [GL, literalExcess, YL, low, ite_false, PC_L, nonzero] using code)
    (by dsimp only [PC_L, FL]; omega)
  have distanceBound := weighted_tree_bound FD GD YD PC_D 30 1334 3 distanceWeight 29 (by
    intro v bound nonzero
    have code := distance_code_bound (FD v) (distanceLength v) (distanceExtra v)
      distanceWeight (classD v) (originD v) (distanceLengths v bound nonzero)
      (distanceBits v bound) (classesD v bound nonzero)
    simpa only [GD, distanceExcess, YD, PC_D, nonzero, ite_false] using code)
    (by dsimp only [PC_D, FD]; omega)
  have literalMass : mass FL 286 = xs.length + 1 := literal_frequency_mass lengthCode literalKeys
  have distanceMass : mass FD 30 ≤ xs.length := distance_frequency_mass distanceCode distanceKeys
  rw [literalMass, literalCoefficients] at literalBound
  rw [distanceCoefficients] at distanceBound
  have literalCosts : mass (fun v => FL v * GL v) 286 = (xs.map (fun s => GL (s.literalKey lengthCode))).sum := by
    have point : mass (fun v => FL v * GL v) 286 =
        mass (fun v => countKey (fun s => some (s.literalKey lengthCode)) xs v * GL v) 286 := by
      apply mass_congr
      intro v _bound
      by_cases endMarker : v = 256
      · subst v
        have zero : GL 256 = 0 := rfl
        simp only [zero, Nat.mul_zero]
      · simp only [FL, literalFrequency, endMarker, ite_false, Nat.zero_add]
    rw [point]
    exact weighted_count_key (Symbol.literalKey lengthCode) 286 GL literalKeys
  have distanceCosts : mass (fun v => FD v * GD v) 30 = (xs.map DC).sum :=
    weighted_optional_key (Symbol.distanceKey distanceCode) 30 GD distanceKeys
  have split : ∀ s ∈ xs,
      symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode s - 24 ≤
        GL (s.literalKey lengthCode) + DC s := by
    intro s member
    have value := (valid s member).2
    by_cases literal : s.distance = 0
    · have key : s.literalKey lengthCode = s.value := by simp only [Symbol.literalKey, literal, ite_true]
      have positive : literalFrequency lengthCode xs s.value ≠ 0 := by
        have count := count_key_positive (fun s => some (s.literalKey lengthCode)) member
          (show some (s.literalKey lengthCode) = some s.value by rw [key])
        unfold literalFrequency
        omega
      have length := literalLengths s.value (by omega) positive
      simp only [symbolCost, literal, ite_true, GL, literalExcess, key,
        show s.value < 257 by omega, DC, Symbol.distanceKey, ite_true, Nat.zero_add]
      omega
    · simp only [symbolCost, literal, ite_false, GL, literalExcess, Symbol.literalKey,
        show ¬ lengthCode s.value + 257 < 257 by omega, DC, Symbol.distanceKey,
        Nat.add_sub_cancel, GD, distanceExcess]
      change literalLength (lengthCode s.value + 257) + literalExtra (lengthCode s.value) +
        distanceLength (distanceCode (s.distance - 1)) + distanceExtra (distanceCode (s.distance - 1)) - 24 ≤
        (literalLength (lengthCode s.value + 257) + literalExtra (lengthCode s.value) - 9) +
        (distanceLength (distanceCode (s.distance - 1)) + distanceExtra (distanceCode (s.distance - 1)) - 15)
      omega
  have summed := list_sum_le_split xs
    (fun s => symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode s - 24)
    (fun s => GL (s.literalKey lengthCode)) DC split
  have scaled := Nat.mul_le_mul_left 1000 summed
  rw [Nat.mul_add, ← literalCosts, ← distanceCosts] at scaled
  unfold Zlib.Trees.Overlay.bitExcess
  rw [List.map_map]
  change 1000 * (xs.map (fun s => symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode s - 24)).sum ≤ 6257 * (xs.length + 3)
  apply Zlib.Trees.Overlay.excess_from_coarse_weights (literalWeight := literalWeight) (distanceWeight := distanceWeight)
    ?_ literalTotal distanceTotal
  omega

end ZlibF.Math.DeflatePush
