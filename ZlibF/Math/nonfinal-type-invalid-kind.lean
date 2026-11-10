import ZlibF.Proof.«inflate.c.nonfinal-type-fixed-trees-v1»
import ZlibF.Math.«whole-stored-rejection»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Deflate has no BTYPE3 body. The causal block context rules out any
future completion after the actually credited invalid tag. -/
theorem invalid_tag_blocks
    {dictionary : List UInt8} (block : BlockStart dictionary)
    {remaining : List Bool} {future : List UInt8} {rest : List Bool} {output : List UInt8}
    (kind : block.kind = 3)
    (aligned : (block.previous ++ block.tag ++ remaining ++ bytesBits future).length % 8 = 0) :
    ¬ Blocks block.wrapper.dictionary []
      (block.previous ++ block.tag ++ remaining ++ bytesBits future) rest output := by
  intro parsed
  have tail : Blocks block.wrapper.dictionary block.before
      (block.tag ++ remaining ++ bytesBits future) rest output := by
    have context := block.context (block.tag ++ remaining ++ bytesBits future) rest output
      (by simpa only [List.length_append, Nat.add_assoc] using aligned)
    exact context.mp (by simpa only [List.append_assoc] using parsed)
  have impossible {flag bt : Nat} {tagRest bodyInput bodyRest : List Bool} {decoded : List UInt8}
      (readFlag : readBits 1 (block.tag ++ remaining ++ bytesBits future) = some (flag, tagRest))
      (readType : readBits 2 tagRest = some (bt, bodyInput))
      (body : Body block.wrapper.dictionary bt block.before bodyInput bodyRest decoded) : False := by
    simp only [List.append_assoc] at readFlag
    have flagExpected := stored_readBits_append block.finalRead (remaining ++ bytesBits future)
    have flagRest : tagRest = block.middle ++ (remaining ++ bytesBits future) :=
      congrArg Prod.snd (Option.some.inj (readFlag.symm.trans flagExpected))
    subst tagRest
    have kindExpected := stored_readBits_append block.typeRead (remaining ++ bytesBits future)
    simp only [List.nil_append] at kindExpected
    have same := Option.some.inj (readType.symm.trans kindExpected)
    have kindEq : bt = block.kind := congrArg Prod.fst same
    rw [kindEq, kind] at body
    cases body
  cases tail with
  | last first second body => exact impossible first second body
  | more first second body _ => exact impossible first second body

/-- The rejection is based only on bytes already read by the translated C
branch. It does not constrain a caller's unread input or future buffer. -/
theorem invalid_tag_rejects
    {log : DataLog} (block : BlockStart log.dictionary) {remaining : List Bool}
    (kind : block.kind = 3)
    (source : bytesBits log.input = block.prefix ++ remaining) : Rejects log := by
  intro future output decoded
  have bodySource : bytesBits log.input = bytesBits block.wrapper.bytes ++
      (block.previous ++ block.tag ++ remaining) := by
    simpa only [BlockStart.prefix, List.append_assoc] using source
  obtain ⟨bodyBytes, bytes, bits⟩ := block.wrapper.source_bytes (future := future) bodySource
  rw [bytes] at decoded
  obtain ⟨rest, blocks, _padding⟩ := block.wrapper.original_valid_body decoded
  have alignment : (block.previous ++ block.tag ++ remaining ++ bytesBits future).length % 8 = 0 := by
    have lengths := congrArg List.length bits
    rw [bytesBits_length] at lengths
    omega
  have parsed : Blocks block.wrapper.dictionary []
      (block.previous ++ block.tag ++ remaining ++ bytesBits future) rest output := by
    simpa only [bytesBits_eq_bytesToBits, bits] using blocks
  exact invalid_tag_blocks block kind alignment parsed

#print axioms invalid_tag_blocks
#print axioms invalid_tag_rejects
end Zlib.Inflate.Proofs.WholeEpoch
