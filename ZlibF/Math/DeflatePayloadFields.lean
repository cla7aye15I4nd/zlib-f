import ZlibF.Math.DeflatePayload

/-! # Checked length-table intervals used by the payload writer -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every internal length-minus-three byte selects a legal code and
fitted extra-bit value whenever that value is emitted. The special
length-258 code has zero extra bits and never reads its base entry. -/
theorem length_payload_checked_fields (lc : Nat) (bound : lc < 256) :
    lcodeN lc < 29 ∧ 0 ≤ extra_lbits_tab[lcodeN lc]!.toInt ∧ extra_lbits_tab[lcodeN lc]!.toInt ≤ 5 ∧
    0 ≤ base_length_tab[lcodeN lc]!.toInt ∧ base_length_tab[lcodeN lc]!.toInt.toNat ≤ lc ∧
    (extra_lbits_tab[lcodeN lc]!.toInt ≠ 0 →
      lc - base_length_tab[lcodeN lc]!.toInt.toNat < 2 ^ extra_lbits_tab[lcodeN lc]!.toInt.toNat) := by
  have table : ∀ i : Fin 256,
      lcodeN i.val < 29 ∧ 0 ≤ extra_lbits_tab[lcodeN i.val]!.toInt ∧ extra_lbits_tab[lcodeN i.val]!.toInt ≤ 5 ∧
      0 ≤ base_length_tab[lcodeN i.val]!.toInt ∧ base_length_tab[lcodeN i.val]!.toInt.toNat ≤ i.val ∧
      (extra_lbits_tab[lcodeN i.val]!.toInt ≠ 0 →
        i.val - base_length_tab[lcodeN i.val]!.toInt.toNat < 2 ^ extra_lbits_tab[lcodeN i.val]!.toInt.toNat) := by
    decide +kernel
  exact table ⟨lc, bound⟩

end Zlib.Trees.Proofs.Out
