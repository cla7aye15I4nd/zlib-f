import ZlibF.Spec.Api.InflateAccepted
import ZlibF.Proof.Format.Wrapper

namespace ZlibF.Math.InflateConfiguredAcceptance
open ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-- With a fixed configured dictionary capacity, accepted zlib streams
remain self-delimiting and deterministic. This does not replace the RFC
valid-source relation or assume an implementation's successful return. -/
theorem decodesWithWindow_ext
    {bits : Nat} {dict input trailing first second : List UInt8}
    (left : Zlib.DecodesWithWindow bits dict input first)
    (right : Zlib.DecodesWithWindow bits dict (input ++ trailing) second) :
    trailing = [] ∧ first = second := by
  obtain ⟨cmf, flg, pre, data, source, _header, plain, preset⟩ := left
  obtain ⟨cmf', flg', pre', data', source', _header', plain', preset'⟩ := right
  rw [source] at source'
  simp only [List.cons_append, List.cons.injEq] at source'
  obtain ⟨rfl, rfl, source'⟩ := source'
  by_cases absent : flg.toNat / 32 % 2 = 0
  · obtain ⟨rfl, parsed⟩ := plain absent
    obtain ⟨rfl, parsed'⟩ := plain' absent
    simp only [List.nil_append] at source'
    subst source'
    obtain ⟨length, output⟩ := Prefix.ext parsed parsed'
    refine ⟨?_, output⟩
    rw [be32_length, be32_length] at length
    exact List.eq_nil_of_length_eq_zero (by omega)
  · have present : flg.toNat / 32 % 2 = 1 := by omega
    obtain ⟨rfl, parsed⟩ := preset present
    obtain ⟨preEq, parsed'⟩ := preset' present
    have bodyEq : data ++ trailing = data' := by
      rw [← preEq] at source'
      exact List.append_cancel_left (by simpa only [List.append_assoc] using source')
    subst bodyEq
    obtain ⟨length, output⟩ := Prefix.ext parsed parsed'
    refine ⟨?_, output⟩
    rw [be32_length, be32_length] at length
    exact List.eq_nil_of_length_eq_zero (by omega)

/-- Two independent accepted parses of exactly the same bytes agree. -/
theorem decodesWithWindow_deterministic
    {bits : Nat} {dict input first second : List UInt8}
    (left : Zlib.DecodesWithWindow bits dict input first)
    (right : Zlib.DecodesWithWindow bits dict input second) : first = second := by
  exact (decodesWithWindow_ext (trailing := []) left
    (by simpa only [List.append_nil] using right)).2

/-- The default wrapper acceptance relation inherits exact ending and
output, including the configured-window preset-dictionary interpretation. -/
theorem default_accepted_ext
    {dict input trailing first second : List UInt8}
    (left : Api.Layer.InflateAccepted .zlib 15 dict input first)
    (right : Api.Layer.InflateAccepted .zlib 15 dict (input ++ trailing) second) :
    trailing = [] ∧ first = second :=
  decodesWithWindow_ext left.1 right.1

#print axioms decodesWithWindow_ext
#print axioms decodesWithWindow_deterministic
#print axioms default_accepted_ext
end ZlibF.Math.InflateConfiguredAcceptance
