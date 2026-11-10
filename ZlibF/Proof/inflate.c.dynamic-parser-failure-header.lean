import ZlibF.Proof.«inflate.c.dynamic-reader-bad-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader
open ZlibF.Math.InflateHuffmanBodyContext ZlibF.Math.HeaderConsumedReplay
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem parser_failure_no_header
    {s : InflateState} {l : IL} {bs : List UInt8} {alphabet : List Nat} {badWord remaining : List Bool}
    (data : HeaderSourcePrefix s l bs alphabet)
    (inverse : ParserContext alphabet (s.nlen.toNat+s.ndist.toNat) [] data.consumed (actualLengthPrefix s))
    (source : stream l bs=badWord++remaining)
    (failure : NoCodeLensExtension alphabet (s.nlen.toNat+s.ndist.toNat) (actualLengthPrefix s) badWord) :
    ∃word,data.bodyInput=word++remaining ∧ NoHeaderExtension word := by
  obtain ⟨w1,source1,replay1⟩ := readBits_consumed_word data.first
  obtain ⟨w2,source2,replay2⟩ := readBits_consumed_word data.second
  obtain ⟨w3,source3,replay3⟩ := readBits_consumed_word data.third
  obtain ⟨wa,sourceA,replayA⟩ := readCodeLenLens_consumed_word data.alphabetRead
  have rejected:=inverse.reject failure
  rw [data.literalCount,data.distanceCount] at rejected
  refine ⟨w1++w2++w3++wa++data.consumed++badWord,?_,?_⟩
  · rw [source1,source2,source3,sourceA,data.source,source]
    simp only [List.append_assoc]
  · intro future L D rest header
    cases header with
    | dynamic a b d _counts ar _acceptable parsed _eob _vl _vd =>
      simp only [List.append_assoc] at a
      rw [replay1] at a
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj a)
      rw [replay2] at b
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj b)
      rw [replay3] at d
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj d)
      rw [replayA] at ar
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ar)
      apply rejected future rest _
      simpa only [List.append_assoc] using parsed

#print axioms parser_failure_no_header
end Zlib.Inflate.Proofs.DynamicRejects
