import ZlibF.Proof.«inflate.c.dynamic-eob-reject-source»
import ZlibF.Math.«whole-epoch-wrapper-prefix»
import ZlibF.Math.«whole-epoch-original-valid-body»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
open ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- A rejected header anchored to credited bytes rejects every original
RFC stream extension. Saved lookahead is included; unread memory is free. -/
theorem no_header_rejects_credited
    {log : DataLog} (block : BlockStart log.dictionary) (dynamic : block.kind=2)
    {word saved : List Bool}
    (source : bytesBits log.input=block.prefix++word++saved)
    (rejected : NoHeaderExtension word) : Rejects log := by
  intro future output valid
  have anchor : bytesBits log.input=bytesBits block.wrapper.bytes ++
      (block.previous++block.tag++word++saved) := by
    simpa only [BlockStart.prefix,List.append_assoc] using source
  obtain ⟨bodyBytes,original,bodySource⟩ := block.wrapper.source_bytes (future:=future) anchor
  rw [original] at valid
  obtain ⟨rest,blocks,_trailer⟩ := block.wrapper.original_valid_body valid
  have bitSource : bytesToBits bodyBytes=block.previous++(block.tag++(word++(saved++bytesBits future))) := by
    simpa only [bytesBits_eq_bytesToBits,List.append_assoc] using bodySource
  rw [bitSource] at blocks
  have aligned : (block.previous.length+(block.tag++(word++(saved++bytesBits future))).length)%8=0 := by
    have sizes := congrArg List.length bitSource
    simp only [bytesBits_eq_bytesToBits,bytesBits_length,List.length_append] at sizes
    simp only [List.length_append]
    have futureSize := bytesBits_length future
    omega
  have remaining := (block.context (block.tag++(word++(saved++bytesBits future))) rest output aligned).mp blocks
  have finalRead := readBits_append _ _ _ _ (word++(saved++bytesBits future)) block.finalRead
  have typeRead := readBits_append _ _ _ _ (word++(saved++bytesBits future)) block.typeRead
  have header_from_body {tail : List Bool} {decoded : List UInt8}
      (body : Body block.wrapper.dictionary block.kind block.before (word++(saved++bytesBits future)) tail decoded) : False := by
    rw [dynamic] at body
    cases body with
    | dynamic first second third counts alphabet acceptable lens eob vl vd _symbols =>
      exact rejected (saved++bytesBits future) _ _ _ (.dynamic first second third counts alphabet acceptable lens eob vl vd)
  cases remaining with
  | last actualFinal actualType body =>
    obtain ⟨_last,inputEq⟩ := Prod.mk.inj (Option.some.inj (finalRead.symm.trans actualFinal))
    rw [←inputEq] at actualType
    have typeRead0 : readBits 2 (block.middle++(word++(saved++bytesBits future)))=
        some (block.kind,word++(saved++bytesBits future)) := by simpa only [List.nil_append] using typeRead
    obtain ⟨kindEq,bodyEq⟩ := Prod.mk.inj (Option.some.inj (typeRead0.symm.trans actualType))
    rw [←kindEq,←bodyEq] at body
    exact header_from_body body
  | more actualFinal actualType body _tail =>
    obtain ⟨_last,inputEq⟩ := Prod.mk.inj (Option.some.inj (finalRead.symm.trans actualFinal))
    rw [←inputEq] at actualType
    have typeRead0 : readBits 2 (block.middle++(word++(saved++bytesBits future)))=
        some (block.kind,word++(saved++bytesBits future)) := by simpa only [List.nil_append] using typeRead
    obtain ⟨kindEq,bodyEq⟩ := Prod.mk.inj (Option.some.inj (typeRead0.symm.trans actualType))
    rw [←kindEq,←bodyEq] at body
    exact header_from_body body

#print axioms no_header_rejects_credited
end Zlib.Inflate.Proofs.DynamicRejects
