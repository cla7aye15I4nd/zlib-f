import ZlibF.Math.DeflateMemoryBounds
import ZlibF.Math.DeflateSymbolExcess

namespace ZlibF.Math.DeflatePush
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

/-- Without length repair, exact source frequencies obey direct Fibonacci
bounds and no class/origin repair charge is needed. The resulting 5315
coefficient is sufficient for memory four under the existing header bound.
These are representation data premises, not execution contracts. -/
theorem symbol_excess_without_repair (xs : List Symbol)
    (literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode : Nat → Nat)
    (literalWeight distanceWeight : Nat)
    (valid : ∀ s ∈ xs, s.Valid)
    (literalKeys : ∀ s ∈ xs, s.literalKey lengthCode < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey distanceCode = some k → k < 30)
    (literalBits : ∀ c, c < 29 → literalExtra c < 6)
    (distanceBits : ∀ c, c < 30 → distanceExtra c < 14)
    (literalLengths : ∀ v, v < 286 → literalFrequency lengthCode xs v ≠ 0 → literalLength v ≤ 15)
    (distanceLengths : ∀ v, v < 30 → distanceFrequency distanceCode xs v ≠ 0 → distanceLength v ≤ 15)
    (literalFib : ∀ v, v < 286 → literalFrequency lengthCode xs v ≠ 0 →
      literalFrequency lengthCode xs v * fib (literalLength v + 1) ≤ literalWeight)
    (distanceFib : ∀ v, v < 30 → distanceFrequency distanceCode xs v ≠ 0 →
      distanceFrequency distanceCode xs v * fib (distanceLength v + 1) ≤ distanceWeight)
    (literalCoefficients : mass (fun v => if v < 257 then 0 else lengthCoefficient (literalExtra (v - 257))) 286 = 1921)
    (distanceCoefficients : mass (fun v => distanceCoefficient (distanceExtra v)) 30 = 1660)
    (literalTotal : literalWeight ≤ xs.length + 3) (distanceTotal : distanceWeight ≤ xs.length + 3) :
    1000 * Zlib.Trees.Overlay.bitExcess
      (xs.map (symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode)) ≤
      5315 * (xs.length + 3) := by
  let FL := literalFrequency lengthCode xs
  let FD := distanceFrequency distanceCode xs
  let GL := literalExcess literalLength literalExtra
  let GD := distanceExcess distanceLength distanceExtra
  let YL := fun v => if v < 257 then 0 else lengthCoefficient (literalExtra (v - 257))
  let YD := fun v => distanceCoefficient (distanceExtra v)
  let DC := fun s : Symbol => match s.distanceKey distanceCode with | none => 0 | some k => GD k
  let classL : Nat → Nat := fun _ => 0
  let originL : Nat → Nat := fun _ => 0
  let classD : Nat → Nat := fun _ => 0
  let originD : Nat → Nat := fun _ => 0
  have classesL : ∀ v, v < 286 → FL v ≠ 0 →
      CodeClass literalWeight (FL v) (literalLength v) (classL v) (originL v) := by
    intro v bound nonzero
    exact Or.inl ⟨rfl, literalFib v bound nonzero⟩
  have classesD : ∀ v, v < 30 → FD v ≠ 0 →
      CodeClass distanceWeight (FD v) (distanceLength v) (classD v) (originD v) := by
    intro v bound nonzero
    exact Or.inl ⟨rfl, distanceFib v bound nonzero⟩
  let PC_L := fun v => if FL v = 0 then 0 else pushCostA (classL v) (originL v)
  let PC_D := fun v => if FD v = 0 then 0 else pushCostA (classD v) (originD v)
  have literalBound := weighted_tree_bound FL GL YL PC_L 286 400 3 literalWeight 0 (by
    intro v bound nonzero
    by_cases low : v < 257
    · simp only [GL, literalExcess, YL, low, ite_true, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      omega
    · have code := length_code_bound (FL v) (literalLength v) (literalExtra (v - 257))
        literalWeight (classL v) (originL v) (literalLengths v bound nonzero)
        (literalBits (v - 257) (by omega)) (classesL v bound nonzero)
      simpa only [GL, literalExcess, YL, low, ite_false, PC_L, nonzero] using code)
    (by simp [PC_L, classL, pushCostA, mass_zero])
  have distanceBound := weighted_tree_bound FD GD YD PC_D 30 1334 3 distanceWeight 0 (by
    intro v bound nonzero
    have code := distance_code_bound (FD v) (distanceLength v) (distanceExtra v)
      distanceWeight (classD v) (originD v) (distanceLengths v bound nonzero)
      (distanceBits v bound) (classesD v bound nonzero)
    simpa only [GD, distanceExcess, YD, PC_D, nonzero, ite_false] using code)
    (by simp [PC_D, classD, pushCostA, mass_zero])
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
  change 1000 * (xs.map (fun s => symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode s - 24)).sum ≤ 5315 * (xs.length + 3)
  omega


end ZlibF.Math.DeflatePush

#print axioms ZlibF.Math.DeflatePush.symbol_excess_without_repair

namespace ZlibF.Math.DeflateMemLevel
open Zlib.Trees.HuffmanAbstract
open Zlib.Trees.Overlay
open ZlibF.Math.DeflateSelection
set_option autoImplicit false

/-- The full positive-weight Fibonacci source bound, before clamping,
excludes a depth as soon as its minimum weight exceeds the root. -/
theorem depth_lt_of_fibonacci_weight {frequency depth weight cutoff : Nat}
    (positive : 1 ≤ frequency)
    (bound : frequency * fib (depth + 1) + fib depth ≤ weight)
    (small : weight < fib cutoff + fib (cutoff + 1)) : depth < cutoff := by
  by_cases less : depth < cutoff
  · exact less
  · have first := fib_mono (show cutoff ≤ depth by omega)
    have second := fib_mono (show cutoff + 1 ≤ depth + 1 by omega)
    have scaled := Nat.mul_le_mul_right (fib (depth + 1)) positive
    omega

/-- Actual constructor weight bounds for memory one through four imply
strictly sub-limit raw depths. Thus their length clamp has no work to do;
the source producer must transport this fact through gen_bitlen. -/
theorem small_memory_raw_depth_bound {memory frequency depth weight : Nat}
    (low : 1 ≤ memory) (high : memory ≤ 4) (positive : 1 ≤ frequency)
    (bound : frequency * fib (depth + 1) + fib depth ≤ weight)
    (root : weight ≤ symbolSlots memory + 2) :
    depth ≤ if memory = 1 then 9 else if memory = 2 then 11 else if memory = 3 then 12 else 14 := by
  have cases : memory = 1 ∨ memory = 2 ∨ memory = 3 ∨ memory = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · have small : weight < fib 10 + fib 11 := by change weight < 144; change weight ≤ 130 at root; omega
    have d := depth_lt_of_fibonacci_weight positive bound small
    simpa only [ite_true] using (show depth ≤ 9 by omega)
  · have small : weight < fib 12 + fib 13 := by change weight < 377; change weight ≤ 258 at root; omega
    have d := depth_lt_of_fibonacci_weight positive bound small
    simpa only [show ¬ (2 : Nat) = 1 by decide, ite_false, ite_true] using (show depth ≤ 11 by omega)
  · have small : weight < fib 13 + fib 14 := by change weight < 610; change weight ≤ 514 at root; omega
    have d := depth_lt_of_fibonacci_weight positive bound small
    simpa only [show ¬ (3 : Nat) = 1 by decide, show ¬ (3 : Nat) = 2 by decide, ite_false, ite_true] using (show depth ≤ 12 by omega)
  · have small : weight < fib 15 + fib 16 := by change weight < 1597; change weight ≤ 1026 at root; omega
    have d := depth_lt_of_fibonacci_weight positive bound small
    simpa only [show ¬ (4 : Nat) = 1 by decide, show ¬ (4 : Nat) = 2 by decide,
      show ¬ (4 : Nat) = 3 by decide, ite_false] using (show depth ≤ 14 by omega)

/-- The raw tree clamp to fifteen is the identity in small memory. -/
theorem small_memory_raw_depth_unclamped {memory frequency depth weight : Nat}
    (low : 1 ≤ memory) (high : memory ≤ 4) (positive : 1 ≤ frequency)
    (bound : frequency * fib (depth + 1) + fib depth ≤ weight)
    (root : weight ≤ symbolSlots memory + 2) : min depth 15 = depth := by
  have cap := small_memory_raw_depth_bound low high positive bound root
  have numeric : (if memory = 1 then 9 else if memory = 2 then 11 else if memory = 3 then 12 else 14) ≤ 14 := by
    split <;> (try split) <;> (try split) <;> omega
  omega

/-- Removing the repair charge closes the prefix arithmetic already at
memory four, using the same coarse 2283-bit header bound. -/
theorem unrepaired_overlay_from_memory_four {memory start header : Nat}
    (low : 4 ≤ memory) (high : memory ≤ 9) (costs : List Nat)
    (startMax : start ≤ 7) (headerMax : header ≤ 2283)
    (symbolsFit : costs.length + 1 ≤ symbolSlots memory)
    (excess : 1000 * bitExcess costs ≤ 5315 * (costs.length + 3)) (k : Nat) :
    start + 3 + header + (costs.take k).sum + 15 ≤ 8 * (symbolSlots memory + 3 * k) := by
  have capacityMin : 1024 ≤ symbolSlots memory := by
    have cases : memory = 4 ∨ memory = 5 ∨ memory = 6 ∨ memory = 7 ∨ memory = 8 ∨ memory = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have prefixCost := prefix_bits_le costs k
  omega

/-- The same unrepaired budget fits the complete pending allocation. -/
theorem unrepaired_pending_room_from_memory_four {memory start header : Nat}
    (low : 4 ≤ memory) (high : memory ≤ 9) (costs : List Nat)
    (startMax : start ≤ 7) (headerMax : header ≤ 2283)
    (symbolsFit : costs.length + 1 ≤ symbolSlots memory)
    (excess : 1000 * bitExcess costs ≤ 5315 * (costs.length + 3)) :
    start + 3 + header + costs.sum + 15 + 7 ≤ 8 * pendingBytes memory := by
  have capacityMin : 1024 ≤ symbolSlots memory := by
    have cases : memory = 4 ∨ memory = 5 ∨ memory = 6 ∨ memory = 7 ∨ memory = 8 ∨ memory = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have total := prefix_bits_le costs costs.length
  rw [List.take_length] at total
  unfold pendingBytes
  omega

/-- Reaching the dynamic branch of the actual selected-cost expression
implies strictly smaller bytes and excludes the force-fixed setting. -/
theorem dynamic_selected_byte_cost {opt fixed : UInt64} {forceFixed : Bool}
    (dynamic : selectedCost opt fixed forceFixed ≠ fixed) :
    selectedCost opt fixed forceFixed = opt ∧ opt < fixed ∧ forceFixed = false := by
  unfold selectedCost at dynamic ⊢
  by_cases selected : fixed ≤ opt ∨ forceFixed = true
  · rw [ite_eq_left selected] at dynamic
    exact False.elim (dynamic rfl)
  · rw [ite_eq_right selected]
    have order : ¬ fixed ≤ opt := fun le => selected (Or.inl le)
    have force : forceFixed = false := by
      cases same : forceFixed
      · rfl
      · exact False.elim (selected (Or.inr same))
    exact ⟨rfl, UInt64.lt_iff_toNat_lt.mpr (by have notle : ¬ fixed.toNat ≤ opt.toNat := fun le => order (UInt64.le_iff_toNat_le.mpr le); omega), force⟩

/-- The source's strictly smaller rounded byte cost implies a strictly
smaller underlying bit count when the real counter additions cannot wrap. -/
theorem dynamic_selected_bit_cost {opt fixed : UInt64}
    (optSmall : opt.toNat + 10 < 18446744073709551616)
    (fixedSmall : fixed.toNat + 10 < 18446744073709551616)
    (selected : byteCost opt < byteCost fixed) : opt.toNat < fixed.toNat := by
  have rounding (word : UInt64) (small : word.toNat + 10 < 18446744073709551616) :
      (byteCost word).toNat = (word.toNat + 10) / 8 := by
    have first : (word + 3).toNat = word.toNat + 3 := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by change word.toNat + 3 < 18446744073709551616; omega)
    have second : (word + 3 + 7).toNat = word.toNat + 10 := by
      rw [UInt64.toNat_add, first]
      exact Nat.mod_eq_of_lt (by change word.toNat + 3 + 7 < 18446744073709551616; omega)
    unfold byteCost
    rw [UInt64.toNat_shiftRight, second]
    change (word.toNat + 10) >>> 3 = _
    rw [Nat.shiftRight_eq_div_pow]
  have order := UInt64.lt_iff_toNat_lt.mp selected
  rw [rounding opt optSmall, rounding fixed fixedSmall] at order
  omega

end ZlibF.Math.DeflateMemLevel

#print axioms ZlibF.Math.DeflateMemLevel.depth_lt_of_fibonacci_weight
#print axioms ZlibF.Math.DeflateMemLevel.small_memory_raw_depth_bound
#print axioms ZlibF.Math.DeflateMemLevel.small_memory_raw_depth_unclamped
#print axioms ZlibF.Math.DeflateMemLevel.unrepaired_overlay_from_memory_four
#print axioms ZlibF.Math.DeflateMemLevel.unrepaired_pending_room_from_memory_four
#print axioms ZlibF.Math.DeflateMemLevel.dynamic_selected_byte_cost
#print axioms ZlibF.Math.DeflateMemLevel.dynamic_selected_bit_cost
