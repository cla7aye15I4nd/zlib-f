import ZlibF.Proof.«inflate.c.whole-epoch-block-transitions»
import ZlibF.Proof.«inflate.c.wrapper-output-credit»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

/-- A complete-byte prefix of credited bits determines a real byte
prefix. The residual bits are exactly the remaining bytes, not guessed. -/
theorem bytes_prefix_of_bits {prefixBytes bytes : List UInt8} {tail : List Bool}
    (source : bytesBits bytes = bytesBits prefixBytes ++ tail) :
    ∃ suffix, bytes = prefixBytes ++ suffix ∧ bytesBits suffix = tail := by
  induction prefixBytes generalizing bytes with
  | nil => exact ⟨bytes, rfl, by simpa only [bytesBits_nil, List.nil_append] using source⟩
  | cons byte rest ih =>
    cases bytes with
    | nil =>
      have lengths := congrArg List.length source
      simp only [bytesBits_length, List.length_nil, List.length_cons, List.length_append] at lengths
      omega
    | cons other remaining =>
      have first := wrapper_readBits_byte byte (bytesBits rest)
      change readBits 8 (bytesBits (byte :: rest)) = some (byte.toNat, bytesBits rest) at first
      have extended := readBits_append 8 (bytesBits (byte :: rest)) byte.toNat (bytesBits rest) tail first
      have observed := wrapper_readBits_byte other (bytesBits remaining)
      change readBits 8 (bytesBits (other :: remaining)) = some (other.toNat, bytesBits remaining) at observed
      rw [← source] at extended
      obtain ⟨sameByte, sameTail⟩ := Prod.mk.inj (Option.some.inj (observed.symm.trans extended))
      have equal : other = byte := UInt8.toNat_inj.mp sameByte
      subst other
      obtain ⟨suffix, remainingEq, bitsEq⟩ := ih sameTail
      exact ⟨suffix, by simp only [remainingEq, List.cons_append], bitsEq⟩

/-- The actual credited wrapper anchor identifies the remaining original
body bytes under arbitrary later caller input. -/
theorem Wrapper.source_bytes {dictionary input future : List UInt8} {bodyPrefix : List Bool}
    (wrapper : Wrapper dictionary)
    (source : bytesBits input = bytesBits wrapper.bytes ++ bodyPrefix) :
    ∃ bodyBytes, input ++ future = wrapper.bytes ++ bodyBytes ∧
      bytesBits bodyBytes = bodyPrefix ++ bytesBits future := by
  obtain ⟨suffix, prefixEq, suffixEq⟩ := bytes_prefix_of_bits source
  refine ⟨suffix ++ future, ?_, ?_⟩
  · rw [prefixEq, List.append_assoc]
  · rw [bytesBits_append, suffixEq]

#print axioms bytes_prefix_of_bits
#print axioms Wrapper.source_bytes
end Zlib.Inflate.Proofs.WholeEpoch
