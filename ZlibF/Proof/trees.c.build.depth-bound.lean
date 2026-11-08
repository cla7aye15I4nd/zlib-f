import ZlibF.Proof.«trees.c.build.weight-values»
import ZlibF.Math.DeflateHuffmanDepth

/-! # Fibonacci levels rule out wrap in the actual depth bytes -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- Both the mathematical levels and the source depth bytes are bounded.
The last field rules out wrap in every actual parent-depth update. -/
structure BTDepthBound (tk : TK) (N K : Nat) (d : DeflateState) : Prop where
  level : ∀ q, 574 - 2 * K ≤ q → q < 573 →
    GB.clK (Hn d) (574 - 2 * K) N 1000 (2 * (K - 1)) (Hn d q) ≤ 22
  height : ∀ q, 574 - 2 * K ≤ q → q < 573 → d.depth[Hn d q]!.toNat ≤ 22
  nowrap : ∀ a, a < K - 1 →
    max d.depth[Hn d (572 - 2 * a)]!.toNat d.depth[Hn d (571 - 2 * a)]!.toNat + 1 < 256

/-- Actual layout, parent sums, removal order and initialized leaf depths
supply the complete Fibonacci argument. The source's modular recurrence
is used to bound its real bytes; agreement with natural height is never
assumed to establish the ordering or ancestor-chain bound. -/
theorem BTBuilt.depth_bound {tk : TK} {N K : Nat} {mc : Int32} {prepared d : DeflateState}
    (built : BTBuilt tk N K mc prepared d) (values : BTMergeValues tk N (K - 1) d)
    (order : BTMergeOrder tk K (K - 1) d) (leaves : BTLeafValues tk N (574 - 2 * K) d)
    (budget : (btFreq tk d (Hn d (574 - 2 * K))).toNat < 2 ^ 16) : BTDepthBound tk N K d := by
  have k2 := built.k2
  have kN := built.kN
  have n286 := built.n286
  have positive := GB.tree_weights_positive built.shape (fun v => (btFreq tk d v).toNat)
    leaves.positive values.sum
  have ordered : ∀ q q', 574 - 2 * K + 1 ≤ q' → q' ≤ q → q < 573 →
      (btFreq tk d (Hn d q)).toNat ≤ (btFreq tk d (Hn d q')).toNat := by
    intro q q' lower between upper
    exact order.monotone (q := q') (q' := q) (by omega) between upper
  have levels := GB.tree_levels_le_22 built.shape (fun v => (btFreq tk d v).toNat)
    positive values.sum ordered budget
  have zero : ∀ q, 574 - 2 * K ≤ q → q < 573 → Hn d q < N → d.depth[Hn d q]!.toNat = 0 := by
    intro q lower upper alphabet
    rw [leaves.depth q lower upper alphabet]
    rfl
  have bounds := GB.depth_upper built.shape (GB.clK_clamped (L := 1000) built.shape)
    (fun v => d.depth[v]!.toNat) zero values.depth 22 (by decide +kernel)
    (fun q lower upper _ => levels q lower upper)
  refine ⟨levels, ?_, ?_⟩
  · intro q lower upper
    have bound := bounds q lower upper
    omega
  · intro a bound
    have left := bounds (572 - 2 * a) (by omega) (by omega)
    have right := bounds (571 - 2 * a) (by omega) (by omega)
    have max : max d.depth[Hn d (572 - 2 * a)]!.toNat d.depth[Hn d (571 - 2 * a)]!.toNat ≤ 22 :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega

end Zlib.Trees.Proofs
