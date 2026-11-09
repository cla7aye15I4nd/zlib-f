import ZlibF.Proof.PlatformMemory
import ZlibF.Spec.Public.Memory
import ZlibF.Math.DeflateCountedBudget

/-! # The utility's original readable object supplies the budget scope -/

namespace ZlibF.Spec.Public.Proofs.CompressBound
open C ZlibF.Spec.Public
set_option autoImplicit false

/-- A source range is bounded by its one actual represented object.
This derives the budget's size premise from the explicit LP64 object
scope. It puts no bound on total stream length or allocation sums. -/
theorem source_bytes_object_bound {h : Heap} {source : BPtr} {n : Nat} {xs : List UInt8}
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h) (bytes : Bytes h source n xs) :
    n < 2 ^ 63 ∧ xs.length = n := by
  rcases bytes with ⟨_null, rfl, rfl⟩ | ⟨ref, offset, array, _pointer, get, bound, contents⟩
  · exact ⟨by decide, rfl⟩
  · have size := objects.size_lt get
    refine ⟨by omega, ?_⟩
    rw [contents]
    simp only [List.length_take, List.length_drop, Array.length_toList]
    exact Nat.min_eq_left (by omega)

/-- The counted actual-strategy estimate fits the original utility
source's advertised capacity. The estimate itself remains an actual
execution obligation; this theorem supplies its original object scope. -/
theorem source_strategy_budget_fits {h : Heap} {source : BPtr} {n accepted produced : Nat} {xs : List UInt8}
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h) (bytes : Bytes h source n xs)
    (acceptedBound : accepted ≤ n) (budget : produced ≤ accepted + 5 * (accepted / 16383) + 5) :
    produced + 6 ≤ ZlibF.Spec.Api.compressBound xs.length := by
  obtain ⟨scope, length⟩ := source_bytes_object_bound objects bytes
  rw [length]
  exact ZlibF.Math.DeflateBound.accepted_strategy_budget_fits scope acceptedBound budget

end ZlibF.Spec.Public.Proofs.CompressBound
