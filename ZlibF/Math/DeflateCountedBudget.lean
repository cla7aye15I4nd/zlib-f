import ZlibF.Math.DeflateUtilityBudget

/-! # Composing counted actual-loop and final-block budgets

These are natural-number composition lemmas. Actual execution must supply
the produced counts and potentials; none of these lemmas assumes a callee
specification or asserts utility success from wire length alone.
-/

namespace ZlibF.Math.DeflateBound
set_option autoImplicit false

/-- The represented-byte lower bound on every full block bounds its
actual count by the available represented input. -/
theorem counted_blocks_le_input {blocks closed n : Nat}
    (minimum : 16383 * blocks ≤ closed) (input : closed ≤ n) : blocks ≤ n / 16383 := by
  omega

/-- Published bytes and still-pending output share the same prefix
budget. Input not yet represented by a full block may enlarge the budget. -/
theorem counted_prefix_budget {blocks closed n produced pending initial : Nat}
    (minimum : 16383 * blocks ≤ closed) (input : closed ≤ n)
    (cost : produced + pending ≤ initial + closed + 5 * blocks) :
    produced + pending ≤ initial + n + 5 * (n / 16383) := by
  have count := counted_blocks_le_input minimum input
  omega

/-- Exactly one final block costs at most its remaining represented input
plus five. It composes with the actual loop's full-block budget even if
publication retains part of either block in pending storage. -/
theorem counted_final_budget {blocks closed remaining n written held tail pending initial : Nat}
    (minimum : 16383 * blocks ≤ closed) (input : closed + remaining ≤ n)
    (loopCost : written + held ≤ initial + closed + 5 * blocks)
    (finalCost : tail + pending ≤ held + remaining + 5) :
    written + tail + pending ≤ initial + n + 5 * (n / 16383) + 5 := by
  have count := counted_blocks_le_input minimum (by omega : closed ≤ n)
  omega

/-- The counted actual-strategy envelope leaves the six wrapper bytes
inside the advertised capacity under the permitted per-object size scope. -/
theorem strategy_budget_fits_compress_bound {n produced : Nat} (object : n < 2 ^ 63)
    (budget : produced ≤ n + 5 * (n / 16383) + 5) :
    produced + 6 ≤ ZlibF.Spec.Api.compressBound n := by
  rw [compress_bound_object_formula n object]
  have envelope := counted_blocks_to_default_bound n
  omega

/-- A strategy may have accepted only a prefix of its caller object. The
same complete-object budget still bounds that actual output count. -/
theorem accepted_strategy_budget_fits {accepted n produced : Nat} (object : n < 2 ^ 63)
    (acceptedBound : accepted ≤ n) (budget : produced ≤ accepted + 5 * (accepted / 16383) + 5) :
    produced + 6 ≤ ZlibF.Spec.Api.compressBound n := by
  apply strategy_budget_fits_compress_bound object
  have count : accepted / 16383 ≤ n / 16383 := Nat.div_le_div_right acceptedBound
  omega

/-- Large complete objects leave strict wire slack. Small-object first
FINISH completion must instead use its actual same-call trailer path. -/
theorem strategy_budget_large_strict {n produced : Nat} (object : n < 2 ^ 63)
    (large : 33554432 ≤ n) (budget : produced ≤ n + 5 * (n / 16383) + 5) :
    produced + 6 < ZlibF.Spec.Api.compressBound n := by
  rw [compress_bound_object_formula n object]
  have strict := counted_budget_large_strict n large
  omega

end ZlibF.Math.DeflateBound
