import ZlibF.Math.DeflateSymbolExcess

/-!
# Symbol excess of small blocks without length-limit repair

`DeflateSymbolExcess` bounds the excess of a block by `6.257` bits per symbol. That bound
allows the repair of `gen_bitlen` (lengths pushed down to 15 bits), and it charges every
code a coefficient times the tree weight. For a small block neither is needed:

* A Huffman tree of total weight `W < F(17) = 1597` has no node at depth 15 or more,
  so `gen_bitlen` never clamps a length. Every used symbol of frequency `f` and length `l`
  then satisfies `f * F(l + 1) + F(l) ≤ W` (`SymbolFibPlus`).
* For a fixed weight cap, one code with `e` extra bits contributes at most a constant to
  the block excess, whatever its frequency. The constants below are the exact maxima of
  `f * (l + e - threshold)` over that constraint, for the caps 514 and 1026.

`symbol_excess_from_fib_plus` sums these constants over the alphabets. The overlay lemmas at
the end turn the result and the proved header bound of 2283 bits into the room of a dynamic
block for `lit_bufsize` 512 and 1024. Nothing here refers to the heap.
-/

namespace ZlibF.Math.DeflateOverlaySmall
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush
open Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

/-- Every used symbol keeps its unclamped Fibonacci depth bound. -/
def SymbolFibPlus (alphabet weight : Nat) (frequency length : Nat → Nat) : Prop :=
  ∀ v, v < alphabet → frequency v ≠ 0 → frequency v * fib (length v + 1) + fib (length v) ≤ weight

theorem fib_values : fib 0 = 0 ∧ fib 1 = 1 ∧ fib 2 = 1 ∧ fib 3 = 2 ∧ fib 4 = 3 ∧ fib 5 = 5 ∧
    fib 6 = 8 ∧ fib 7 = 13 ∧ fib 8 = 21 ∧ fib 9 = 34 ∧ fib 10 = 55 ∧ fib 11 = 89 ∧ fib 12 = 144 ∧
    fib 13 = 233 ∧ fib 14 = 377 ∧ fib 15 = 610 ∧ fib 16 = 987 ∧ fib 17 = 1597 := by decide

/-- Per-code excess cap of a length code with `e` extra bits, tree weight at most 514. -/
def lengthCap514 : Nat → Nat
  | 0 => 5 | 1 => 10 | 2 => 16 | 3 => 28 | 4 => 46 | _ => 76

/-- Per-code excess cap of a distance code with `e` extra bits, tree weight at most 514. -/
def distanceCap514 : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 5 | 7 => 10 | 8 => 16 | 9 => 28
  | 10 => 46 | 11 => 76 | 12 => 126 | _ => 204

/-- Per-code excess cap of a length code with `e` extra bits, tree weight at most 1026. -/
def lengthCap1026 : Nat → Nat
  | 0 => 12 | 1 => 20 | 2 => 36 | 3 => 58 | 4 => 96 | _ => 156

/-- Per-code excess cap of a distance code with `e` extra bits, tree weight at most 1026. -/
def distanceCap1026 : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 12 | 7 => 20 | 8 => 36 | 9 => 58
  | 10 => 96 | 11 => 156 | 12 => 254 | _ => 408

theorem length_cap514 (f l e : Nat) (length : l ≤ 15) (extra : e < 6)
    (weight : f * fib (l + 1) + fib l ≤ 514) : f * (l + e - 9) ≤ lengthCap514 e := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, _⟩ := fib_values
  rcases e with _ | _ | _ | _ | _ | _ | e <;>
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
  simp only [lengthCap514, Nat.reduceAdd, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13,
    f14, f15, f16] at weight ⊢ <;> omega

theorem distance_cap514 (f l e : Nat) (length : l ≤ 15) (extra : e < 14)
    (weight : f * fib (l + 1) + fib l ≤ 514) : f * (l + e - 15) ≤ distanceCap514 e := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, _⟩ := fib_values
  rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | e <;>
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
  simp only [distanceCap514, Nat.reduceAdd, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13,
    f14, f15, f16] at weight ⊢ <;> omega

theorem length_cap1026 (f l e : Nat) (length : l ≤ 15) (extra : e < 6)
    (weight : f * fib (l + 1) + fib l ≤ 1026) : f * (l + e - 9) ≤ lengthCap1026 e := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, _⟩ := fib_values
  rcases e with _ | _ | _ | _ | _ | _ | e <;>
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
  simp only [lengthCap1026, Nat.reduceAdd, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13,
    f14, f15, f16] at weight ⊢ <;> omega

theorem distance_cap1026 (f l e : Nat) (length : l ≤ 15) (extra : e < 14)
    (weight : f * fib (l + 1) + fib l ≤ 1026) : f * (l + e - 15) ≤ distanceCap1026 e := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, _⟩ := fib_values
  rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | e <;>
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l <;>
  simp only [distanceCap1026, Nat.reduceAdd, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13,
    f14, f15, f16] at weight ⊢ <;> omega

/-- **Small-block excess.** If both trees keep their unclamped Fibonacci bounds and every code
of extra-bit count `e` contributes at most `capL e` (`capD e`) whatever its frequency, the block
excess is at most the sum of these caps over the alphabets. The caps are data: they come from
`length_cap514` and its siblings with the actual weight bound. -/
theorem symbol_excess_from_fib_plus (xs : List Symbol)
    (literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode : Nat → Nat)
    (literalWeight distanceWeight : Nat) (capL capD : Nat → Nat) (CL CD : Nat)
    (valid : ∀ s ∈ xs, s.Valid)
    (literalKeys : ∀ s ∈ xs, s.literalKey lengthCode < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey distanceCode = some k → k < 30)
    (literalBits : ∀ c, c < 29 → literalExtra c < 6)
    (distanceBits : ∀ c, c < 30 → distanceExtra c < 14)
    (literalLengths : ∀ v, v < 286 → literalFrequency lengthCode xs v ≠ 0 → literalLength v ≤ 15)
    (distanceLengths : ∀ v, v < 30 → distanceFrequency distanceCode xs v ≠ 0 → distanceLength v ≤ 15)
    (literalFib : SymbolFibPlus 286 literalWeight (literalFrequency lengthCode xs) literalLength)
    (distanceFib : SymbolFibPlus 30 distanceWeight (distanceFrequency distanceCode xs) distanceLength)
    (literalCap : ∀ f l e, l ≤ 15 → e < 6 → f * fib (l + 1) + fib l ≤ literalWeight →
      f * (l + e - 9) ≤ capL e)
    (distanceCap : ∀ f l e, l ≤ 15 → e < 14 → f * fib (l + 1) + fib l ≤ distanceWeight →
      f * (l + e - 15) ≤ capD e)
    (literalSum : mass (fun v => if v < 257 then 0 else capL (literalExtra (v - 257))) 286 ≤ CL)
    (distanceSum : mass (fun v => capD (distanceExtra v)) 30 ≤ CD) :
    Zlib.Trees.Overlay.bitExcess
      (xs.map (symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode)) ≤
      CL + CD := by
  let FL := literalFrequency lengthCode xs
  let FD := distanceFrequency distanceCode xs
  let GL := literalExcess literalLength literalExtra
  let GD := distanceExcess distanceLength distanceExtra
  let DC := fun s : Symbol => match s.distanceKey distanceCode with | none => 0 | some k => GD k
  have literalBound : mass (fun v => FL v * GL v) 286 ≤ CL := by
    refine Nat.le_trans (mass_mono ?_) literalSum
    intro v bound
    by_cases zero : FL v = 0
    · simp only [zero, Nat.zero_mul]
      omega
    · by_cases low : v < 257
      · simp only [GL, literalExcess, low, ite_true, Nat.mul_zero]
        omega
      · have code := literalCap (FL v) (literalLength v) (literalExtra (v - 257))
          (literalLengths v bound zero) (literalBits (v - 257) (by omega)) (literalFib v bound zero)
        simpa only [GL, literalExcess, low, ite_false] using code
  have distanceBound : mass (fun v => FD v * GD v) 30 ≤ CD := by
    refine Nat.le_trans (mass_mono ?_) distanceSum
    intro v bound
    by_cases zero : FD v = 0
    · simp only [zero, Nat.zero_mul]
      omega
    · have code := distanceCap (FD v) (distanceLength v) (distanceExtra v)
        (distanceLengths v bound zero) (distanceBits v bound) (distanceFib v bound zero)
      simpa only [GD, distanceExcess] using code
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
  unfold Zlib.Trees.Overlay.bitExcess
  rw [List.map_map]
  change (xs.map (fun s => symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode
    distanceCode s - 24)).sum ≤ CL + CD
  rw [← literalCosts, ← distanceCosts] at summed
  omega

/-- The overlay room from an order-free budget: if the entry bits, the tag, the header, the
block excess and the fifteen-bit margin fit `8 * lit_bufsize`, every prefix stays fifteen bits
below the next unread symbol. -/
theorem overlay_prefix_of_budget (capacity start header : Nat) (costs : List Nat)
    (startMax : start ≤ 7) (budget : header + Zlib.Trees.Overlay.bitExcess costs + 25 ≤ 8 * capacity)
    (k : Nat) :
    start + 3 + header + (costs.take k).sum + 15 ≤ 8 * (capacity + 3 * k) := by
  have prefixBound := Zlib.Trees.Overlay.prefix_bits_le costs k
  omega

/-- The same budget makes the whole block, with the end code and the final alignment, fit the
`4 * lit_bufsize` pending bytes. -/
theorem overlay_block_of_budget (capacity start header : Nat) (costs : List Nat)
    (startMax : start ≤ 7) (budget : header + Zlib.Trees.Overlay.bitExcess costs + 25 ≤ 8 * capacity)
    (symbolsFit : costs.length + 1 ≤ capacity) :
    start + 3 + header + costs.sum + 15 + 7 ≤ 8 * (4 * capacity) := by
  have total := Zlib.Trees.Overlay.prefix_bits_le costs costs.length
  rw [List.take_length] at total
  omega

end ZlibF.Math.DeflateOverlaySmall
