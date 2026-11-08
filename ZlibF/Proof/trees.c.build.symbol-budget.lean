import ZlibF.Proof.«trees.c.build.fib-origins»
import ZlibF.Math.DeflateSymbolFibPush

/-! # Original source frequencies satisfy the quantitative symbol budget -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass)
open ZlibF.Math.DeflatePush (SymbolFibPush)
set_option autoImplicit false

/-- The actual constructor's rank result yields classes for each original
used symbol. Its frequency is the real input frequency, and its length is
the final stored length. Dummy leaves do not consume extra symbol budget. -/
theorem BTFibOrigins.symbol_budget {tk : TK} {N : Nat} {original result : DeflateState}
    (origins : BTFibOrigins tk N original result) :
    ∃ weight, weight ≤ mass (fun v => (btFreq tk original v).toNat) N + 2 ∧
      SymbolFibPush N weight (fun v => (btFreq tk original v).toNat) (curL (tk.arr result)) := by
  obtain ⟨prepared, built, mc, K, tree, weight, frequencies, used, fib⟩ := origins
  refine ⟨frn (tk.arr built) (Hn built (574 - 2 * K)), weight, ?_⟩
  apply SymbolFibPush.of_ranked_tree tree.shape ?_ ?_ fib
  · intro v bound nonzero
    have wordNonzero : btFreq tk original v ≠ 0 := by
      intro zero
      apply nonzero
      rw [zero]
      rfl
    exact used v bound wordNonzero
  · intro v bound nonzero
    have wordNonzero : btFreq tk original v ≠ 0 := by
      intro zero
      apply nonzero
      rw [zero]
      rfl
    change (btFreq tk built v).toNat = (btFreq tk original v).toNat
    rw [frequencies v bound wordNonzero]

end Zlib.Trees.Proofs
