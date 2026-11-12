import ZlibF.Math.DeflateOverlaySmall

/-!
# Block excess from the Fibonacci bound with the actual frequencies

`symbol_excess_from_fib_plus` bounds the excess of every code by a cap that depends only on its
extra bits, the worst case over all frequencies. Here each code keeps its own frequency `f`: its
length is at most `fibLen f W`, the largest `ℓ ≤ 15` with `f·F(ℓ+1) + F(ℓ) ≤ W`, so it contributes
at most `f · (fibLen f W + e − th)`, with `th = 9` for a length code and `15` for a distance code
(a literal never exceeds the 24 bits it releases).
-/

namespace ZlibF.Math.DeflateOverlaySmall
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush
open Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

/-- The largest `ℓ ≤ n` with `f·F(ℓ+1) + F(ℓ) ≤ W`, or `0`. -/
def fibLenUpTo (f W : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if f * fib (n + 2) + fib (n + 1) ≤ W then n + 1 else fibLenUpTo f W n

/-- The longest code length the Fibonacci bound allows for frequency `f` in a tree of weight at
most `W`, among lengths at most 15. -/
def fibLen (f W : Nat) : Nat := fibLenUpTo f W 15

theorem fibLenUpTo_ge (f W : Nat) :
    ∀ n l, l ≤ n → f * fib (l + 1) + fib l ≤ W → l ≤ fibLenUpTo f W n := by
  intro n
  induction n with
  | zero => intro l le _; simp only [fibLenUpTo]; omega
  | succ n ih =>
    intro l le fits
    simp only [fibLenUpTo]
    split
    · exact le
    · rename_i no
      have ne : l ≠ n + 1 := by
        intro e; subst e; exact no fits
      exact Nat.le_trans (ih l (by omega) fits) (Nat.le_refl _)

theorem fibLen_ge {f W l : Nat} (length : l ≤ 15) (fits : f * fib (l + 1) + fib l ≤ W) : l ≤ fibLen f W :=
  fibLenUpTo_ge f W 15 l length fits

/-- The Fibonacci excess with the actual frequencies: length codes over 9 bits, distance codes
over 15 bits, each code at the longest length its frequency allows. -/
def excessFibActual (W : Nat) (FL FD literalExtra distanceExtra : Nat → Nat) : Nat :=
  mass (fun v => if v < 257 then 0 else FL v * (fibLen (FL v) W + literalExtra (v - 257) - 9)) 286 +
    mass (fun v => FD v * (fibLen (FD v) W + distanceExtra v - 15)) 30

/-- **The block excess is at most the per-code excess at the actual frequencies.** -/
theorem symbol_excess_fib_actual (xs : List Symbol)
    (literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode : Nat → Nat)
    (literalWeight distanceWeight W : Nat)
    (valid : ∀ s ∈ xs, s.Valid)
    (literalKeys : ∀ s ∈ xs, s.literalKey lengthCode < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey distanceCode = some k → k < 30)
    (literalLengths : ∀ v, v < 286 → literalFrequency lengthCode xs v ≠ 0 → literalLength v ≤ 15)
    (distanceLengths : ∀ v, v < 30 → distanceFrequency distanceCode xs v ≠ 0 → distanceLength v ≤ 15)
    (literalFib : SymbolFibPlus 286 literalWeight (literalFrequency lengthCode xs) literalLength)
    (distanceFib : SymbolFibPlus 30 distanceWeight (distanceFrequency distanceCode xs) distanceLength)
    (literalW : literalWeight ≤ W) (distanceW : distanceWeight ≤ W) :
    Zlib.Trees.Overlay.bitExcess
      (xs.map (symbolCost literalLength distanceLength literalExtra distanceExtra lengthCode distanceCode)) ≤
      excessFibActual W (literalFrequency lengthCode xs) (distanceFrequency distanceCode xs)
        literalExtra distanceExtra := by
  let FL := literalFrequency lengthCode xs
  let FD := distanceFrequency distanceCode xs
  let GL := literalExcess literalLength literalExtra
  let GD := distanceExcess distanceLength distanceExtra
  let DC := fun s : Symbol => match s.distanceKey distanceCode with | none => 0 | some k => GD k
  have literalBound : mass (fun v => FL v * GL v) 286 ≤
      mass (fun v => if v < 257 then 0 else FL v * (fibLen (FL v) W + literalExtra (v - 257) - 9)) 286 := by
    refine mass_mono ?_
    intro v bound
    by_cases zero : FL v = 0
    · simp only [zero, Nat.zero_mul]
      split <;> omega
    · by_cases low : v < 257
      · simp only [GL, literalExcess, low, ite_true, Nat.mul_zero]
        omega
      · have length := literalLengths v bound zero
        have longest : literalLength v ≤ fibLen (FL v) W :=
          fibLen_ge length (Nat.le_trans (literalFib v bound zero) literalW)
        simp only [GL, literalExcess, low, ite_false]
        exact Nat.mul_le_mul_left _ (by omega)
  have distanceBound : mass (fun v => FD v * GD v) 30 ≤
      mass (fun v => FD v * (fibLen (FD v) W + distanceExtra v - 15)) 30 := by
    refine mass_mono ?_
    intro v bound
    by_cases zero : FD v = 0
    · simp only [zero, Nat.zero_mul]
      omega
    · have length := distanceLengths v bound zero
      have longest : distanceLength v ≤ fibLen (FD v) W :=
        fibLen_ge length (Nat.le_trans (distanceFib v bound zero) distanceW)
      simp only [GD, distanceExcess]
      exact Nat.mul_le_mul_left _ (by omega)
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
    distanceCode s - 24)).sum ≤
    mass (fun v => if v < 257 then 0 else FL v * (fibLen (FL v) W + literalExtra (v - 257) - 9)) 286 +
      mass (fun v => FD v * (fibLen (FD v) W + distanceExtra v - 15)) 30
  rw [← literalCosts, ← distanceCosts] at summed
  omega

end ZlibF.Math.DeflateOverlaySmall
