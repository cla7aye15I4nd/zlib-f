import ZlibF.Proof.«inflate.c.whole-epoch-final-acceptance»
import ZlibF.Math.InflateConfiguredWindowBridge

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- An independently valid RFC stream with the already observed wrapper
supplies a body parse using the actual default configured dictionary. The
window enlargement only preserves existing valid matches. -/
theorem Wrapper.original_valid_body {dictionary body decoded : List UInt8}
    (wrapper : Wrapper dictionary)
    (valid : Zlib.Decodes dictionary (wrapper.bytes ++ body) decoded) :
    Deflate.Prefix wrapper.dictionary body (be32 (adler32 decoded).toNat) decoded := by
  have configured :=
    ZlibF.Math.InflateConfiguredWindowBridge.zlib_decodes_with_default_window valid
  obtain ⟨cmf, flg, pre, data, source, _header, plain, preset⟩ := configured
  have identified : wrapper.cmf = cmf ∧ wrapper.flg = flg ∧
      ((if wrapper.flg.toNat / 32 % 2 = 1 then be32 (adler32 dictionary).toNat else []) ++ body =
        pre ++ data) := by
    simpa only [Wrapper.bytes, List.cons_append, List.nil_append, List.cons.injEq] using source
  obtain ⟨rfl, rfl, remainder⟩ := identified
  by_cases present : wrapper.flg.toNat / 32 % 2 = 1
  · obtain ⟨preEq, parsed⟩ := preset present
    rw [ite_eq_left present, preEq] at remainder
    have same : body = data := List.append_cancel_left remainder
    subst data
    simpa [Wrapper.dictionary, present] using parsed
  · have absent : wrapper.flg.toNat / 32 % 2 = 0 := by
      have bound := Nat.mod_lt (wrapper.flg.toNat / 32) (by decide : 0 < 2)
      omega
    obtain ⟨preEq, parsed⟩ := plain absent
    rw [ite_eq_right present, preEq] at remainder
    simp only [List.nil_append] at remainder
    subst data
    simpa [Wrapper.dictionary, present] using parsed

#print axioms Wrapper.original_valid_body
end Zlib.Inflate.Proofs.WholeEpoch
