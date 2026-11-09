import ZlibF.Math.DeflateStreamBudget
import ZlibF.Spec.Api.Compress

/-! # A counted output budget separates large slack from one-snapshot inputs

These are arithmetic facts. The actual utility must still produce the
counted-block budget on its own execution. They do not assert success
from an encoded-byte length bound alone.
-/

namespace ZlibF.Math.DeflateBound
set_option autoImplicit false

/-- The coarse stored-block envelope can equal the advertised bound.
A proof of a strict bound cannot simply strengthen the old comparison. -/
theorem counted_budget_first_full_equality :
    16383 + 5 * (16383 / 16383) + 11 = ZlibF.Spec.Api.compressBound 16383 := by
  decide +kernel

/-- At and above 2^25 input bytes, the existing counted-block envelope
has at least one byte of slack in the mathematical default formula. -/
theorem counted_budget_large_strict (n : Nat) (large : 33554432 ≤ n) :
    n + 5 * (n / 16383) + 11 < n + n / 4096 + n / 16384 + n / 33554432 + 13 := by
  by_cases high : 134217728 ≤ n
  · omega
  · have close : n / 16383 ≤ n / 16384 + 1 := by omega
    by_cases same : n / 16383 ≤ n / 16384
    · have quarter : 4 * (n / 16384) ≤ n / 4096 := by omega
      omega
    · have next : n / 16383 = n / 16384 + 1 := by omega
      by_cases first : n / 33554432 = 1
      · have remainder : 4 * (n / 16384) + 3 ≤ n / 4096 := by omega
        omega
      · by_cases second : n / 33554432 = 2
        · have remainder : 4 * (n / 16384) + 2 ≤ n / 4096 := by omega
          omega
        · have remainder : 4 * (n / 16384) + 2 ≤ n / 4096 := by omega
          omega

/-- The accepted per-object size premise prevents saturation of the
default formula. It is not a bound on a cumulative streaming history. -/
theorem compress_bound_object_formula (n : Nat) (object : n < 2 ^ 63) :
    ZlibF.Spec.Api.compressBound n = n + n / 4096 + n / 16384 + n / 33554432 + 13 := by
  have small : n + n / 4096 + n / 16384 + n / 33554432 + 13 < 2 ^ 64 := by omega
  unfold ZlibF.Spec.Api.compressBound
  rw [ite_eq_right (by omega)]

/-- A small source and its advertised capacity each fit strictly below
one maximum uInt offer. This is not by itself an engine completion proof. -/
theorem compress_bound_small_offer (n : Nat) (small : n < 33554432) :
    n < 4294967295 ∧ ZlibF.Spec.Api.compressBound n < 4294967295 := by
  have object : n < 2 ^ 63 := by omega
  rw [compress_bound_object_formula n object]
  omega

/-- The coarse envelope either leaves a byte for a later acknowledgement,
or both source and advertised room fit in the initial uInt offers.
The utility must still prove its actual first-call/completion behavior in
the second case; equality of total wire length is not discarded. -/
theorem counted_budget_capacity_split (n : Nat) (object : n < 2 ^ 63) :
    n + 5 * (n / 16383) + 11 < ZlibF.Spec.Api.compressBound n ∨
      (n < 33554432 ∧ n < 4294967295 ∧ ZlibF.Spec.Api.compressBound n < 4294967295) := by
  by_cases large : 33554432 ≤ n
  · left
    rw [compress_bound_object_formula n object]
    exact counted_budget_large_strict n large
  · right
    exact ⟨by omega, compress_bound_small_offer n (by omega)⟩

end ZlibF.Math.DeflateBound
