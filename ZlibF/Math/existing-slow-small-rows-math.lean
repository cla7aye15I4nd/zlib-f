import ZlibF.Math.DeflateSymbolExcess

namespace ZlibF.Math.SmallMemoryRows
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflatePush
set_option autoImplicit false

/-- A coefficient that gives EOB zero weight counts only real source
occurrences, not the separately initialized end marker. -/
theorem literal_weighted_without_end (lc : Nat → Nat) (xs : List Symbol) (cost : Nat → Nat)
    (endZero : cost 256 = 0) (keys : ∀ s ∈ xs, s.literalKey lc < 286) :
    mass (fun v => literalFrequency lc xs v * cost v) 286 =
      (xs.map (fun s => cost (s.literalKey lc))).sum := by
  have point : mass (fun v => literalFrequency lc xs v * cost v) 286 =
      mass (fun v => countKey (fun s => some (s.literalKey lc)) xs v * cost v) 286 := by
    apply mass_congr
    intro v _bound
    by_cases marker : v = 256
    · subst v; simp only [endZero,Nat.mul_zero]
    · simp only [literalFrequency,marker,ite_false,Nat.zero_add]
  rw [point]
  exact weighted_count_key (Symbol.literalKey lc) 286 cost keys

/-- Every real match contributes once to a length-code histogram and once
to a distance-code histogram. This is the ungrouped LP equality row m. -/
theorem match_frequency_balance (lc dc : Nat → Nat) (xs : List Symbol)
    (valid : ∀ s ∈ xs, s.Valid) (literalKeys : ∀ s ∈ xs, s.literalKey lc < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey dc = some k → k < 30) :
    mass (fun v => literalFrequency lc xs v * (if v < 257 then 0 else 1)) 286 =
      mass (distanceFrequency dc xs) 30 := by
  rw [literal_weighted_without_end lc xs _ rfl literalKeys]
  have distance := weighted_optional_key (Symbol.distanceKey dc) 30 (fun _ => 1) distanceKeys
  simp only [Nat.mul_one] at distance
  change mass (distanceFrequency dc xs) 30 = _ at distance
  rw [distance]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s member
  by_cases literal : s.distance = 0
  · have value := (valid s member).2
    simp only [Symbol.literalKey,Symbol.distanceKey,literal,ite_true]
    rw [ite_eq_left (by omega)]
  · simp only [Symbol.literalKey,Symbol.distanceKey,literal,ite_false]
    rw [ite_eq_right (by omega)]

/-- Valid literals and matches never use the END_BLOCK index. Its frequency
is exactly the one written by real block initialization. -/
theorem end_frequency (lc : Nat → Nat) (xs : List Symbol) (valid : ∀ s ∈ xs, s.Valid) :
    literalFrequency lc xs 256 = 1 := by
  have zero : countKey (fun s => some (s.literalKey lc)) xs 256 = 0 := by
    induction xs with
    | nil => rfl
    | cons s xs ih =>
      have rest := ih (fun t member => valid t (by simp [member]))
      have value := (valid s (by simp)).2
      have key : s.literalKey lc ≠ 256 := by unfold Symbol.literalKey; split <;> omega
      simp only [countKey,Option.some.injEq,key,ite_false,rest,Nat.zero_add]
  simp only [literalFrequency,ite_true,zero,Nat.add_zero]

/-- All twenty-five excess split rows hold for the real per-symbol cost
histograms. No Huffman optimality or bit-length-tree budget is assumed. -/
theorem excess_split_family (xs : List Symbol) (L D LX DX lc dc : Nat → Nat)
    (valid : ∀ s ∈ xs, s.Valid) (literalKeys : ∀ s ∈ xs, s.literalKey lc < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey dc = some k → k < 30)
    (literalBound : ∀ s ∈ xs, s.distance = 0 → L s.value ≤ 24)
    (a : Nat) (splitBound : a ≤ 24) :
    Zlib.Trees.Overlay.bitExcess (xs.map (symbolCost L D LX DX lc dc)) ≤
      mass (fun v => literalFrequency lc xs v * (if v < 257 then 0 else L v + LX (v-257) - a)) 286 +
      mass (fun v => distanceFrequency dc xs v * (D v + DX v - (24-a))) 30 := by
  let GL := fun v => if v < 257 then 0 else L v + LX (v-257) - a
  let GD := fun v => D v + DX v - (24-a)
  let distance := fun s : Symbol => match s.distanceKey dc with | none => 0 | some k => GD k
  have literalCosts := literal_weighted_without_end lc xs GL rfl literalKeys
  have distanceCosts := weighted_optional_key (Symbol.distanceKey dc) 30 GD distanceKeys
  change mass (fun v => distanceFrequency dc xs v * GD v) 30 = (xs.map distance).sum at distanceCosts
  have point : ∀ s ∈ xs, symbolCost L D LX DX lc dc s - 24 ≤ GL (s.literalKey lc) + distance s := by
    intro s member
    by_cases literal : s.distance = 0
    · have bound := literalBound s member literal
      have value := (valid s member).2
      simp only [symbolCost,Symbol.literalKey,Symbol.distanceKey,literal,ite_true,GL,distance]
      rw [ite_eq_left (by omega)]
      omega
    · simp only [symbolCost,Symbol.literalKey,Symbol.distanceKey,literal,ite_false,GL,distance]
      rw [ite_eq_right (by omega),Nat.add_sub_cancel]
      dsimp only [GD]
      have thresholds : a + (24-a) = 24 := by omega
      have leftBound : L (lc s.value+257)+LX (lc s.value) ≤
          (L (lc s.value+257)+LX (lc s.value)-a)+a := by omega
      have rightBound : D (dc (s.distance-1))+DX (dc (s.distance-1)) ≤
          (D (dc (s.distance-1))+DX (dc (s.distance-1))-(24-a))+(24-a) := by omega
      omega
  have summed := list_sum_le_split xs (fun s => symbolCost L D LX DX lc dc s - 24)
    (fun s => GL (s.literalKey lc)) distance point
  rw [← literalCosts,← distanceCosts] at summed
  simpa only [Zlib.Trees.Overlay.bitExcess,List.map_map,Function.comp_def,GL,GD] using summed

#print axioms literal_weighted_without_end
#print axioms match_frequency_balance
#print axioms end_frequency
#print axioms excess_split_family
end ZlibF.Math.SmallMemoryRows
