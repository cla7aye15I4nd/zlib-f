import ZlibF.Proof.«inflate.c.whole-stored-copy-dispatch»
import ZlibF.Math.«whole-epoch-original-valid-body»
import ZlibF.Math.«whole-epoch-wrapper-prefix»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.StoredCausal
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A checked mismatching stored complement cannot be repaired by any
later bytes. Both reads come from the actual 32-bit held source word. -/
theorem invalid_stored_body
    {dictionary before output : List UInt8} {padding word : List Bool} {future : List UInt8}
    {len nlen : Nat} {middle rest : List Bool}
    (short : padding.length < 8) (size : word.length = 32)
    (first : readBits 16 word = some (len, middle)) (second : readBits 16 middle = some (nlen, []))
    (bad : nlen ≠ 65535 - len) :
    ¬ Body dictionary 0 before ((padding ++ word) ++ bytesBits future) rest output := by
  intro parsed
  cases parsed with
  | @stored before _ r1 r2 r3 len0 nlen0 bytes first0 second0 complement payload =>
    have alignment : ((padding ++ word) ++ bytesBits future).length % 8 = padding.length := by
      simp only [List.length_append, bytesBits_length]
      omega
    have drop : ((padding ++ word) ++ bytesBits future).drop padding.length = word ++ bytesBits future := by
      rw [List.append_assoc, List.drop_left]
    rw [alignment, drop] at first0
    have firstExtended := stored_readBits_append first (bytesBits future)
    have same := Option.some.inj (first0.symm.trans firstExtended)
    have lenEq : len0 = len := congrArg Prod.fst same
    have restEq : r1 = middle ++ bytesBits future := congrArg Prod.snd same
    subst len0 r1
    have secondExtended := stored_readBits_append second (bytesBits future)
    simp only [List.nil_append] at secondExtended
    have nlenEq : nlen0 = nlen := congrArg Prod.fst (Option.some.inj (second0.symm.trans secondExtended))
    exact bad (nlenEq.symm.trans complement)

/-- The actual complete preceding-block context and current tag expose
an invalid LEN/NLEN regardless of BFINAL, future blocks or trailer bytes. -/
theorem invalid_stored_blocks
    {dictionary : List UInt8} (block : BlockStart dictionary)
    {padding word : List Bool} {future : List UInt8} {len nlen : Nat} {middle rest : List Bool} {output : List UInt8}
    (kind : block.kind = 0) (short : padding.length < 8) (size : word.length = 32)
    (first : readBits 16 word = some (len, middle)) (second : readBits 16 middle = some (nlen, []))
    (bad : nlen ≠ 65535 - len)
    (aligned : (block.previous ++ block.tag ++ padding ++ word ++ bytesBits future).length % 8 = 0) :
    ¬ Blocks block.wrapper.dictionary [] (block.previous ++ block.tag ++ padding ++ word ++ bytesBits future) rest output := by
  intro parsed
  have tail : Blocks block.wrapper.dictionary block.before (block.tag ++ ((padding ++ word) ++ bytesBits future)) rest output := by
    have context := block.context (block.tag ++ ((padding ++ word) ++ bytesBits future)) rest output
      (by simpa only [List.length_append, Nat.add_assoc] using aligned)
    exact context.mp (by simpa only [List.append_assoc] using parsed)
  have observe {flag bt : Nat} {tagRest bodyInput bodyRest : List Bool} {decoded : List UInt8}
      (readFlag : readBits 1 (block.tag ++ ((padding ++ word) ++ bytesBits future)) = some (flag, tagRest))
      (readType : readBits 2 tagRest = some (bt, bodyInput))
      (body : Body block.wrapper.dictionary bt block.before bodyInput bodyRest decoded) : False := by
    have flagExpected := stored_readBits_append block.finalRead ((padding ++ word) ++ bytesBits future)
    have flagRest : tagRest = block.middle ++ ((padding ++ word) ++ bytesBits future) :=
      congrArg Prod.snd (Option.some.inj (readFlag.symm.trans flagExpected))
    subst tagRest
    have kindExpected := stored_readBits_append block.typeRead ((padding ++ word) ++ bytesBits future)
    simp only [List.nil_append] at kindExpected
    have same := Option.some.inj (readType.symm.trans kindExpected)
    have kindEq : bt = block.kind := congrArg Prod.fst same
    have inputEq : bodyInput = (padding ++ word) ++ bytesBits future := congrArg Prod.snd same
    subst bodyInput
    rw [kindEq, kind] at body
    exact invalid_stored_body short size first second bad body
  cases tail with
  | last first0 second0 body => exact observe first0 second0 body
  | more first0 second0 body _later => exact observe first0 second0 body

/-- Rejection is anchored to the actual credited input, including its
held LEN/NLEN, rather than to unread caller memory or a desired parse. -/
theorem invalid_stored_rejects
    {log : DataLog} (block : BlockStart log.dictionary)
    {padding word : List Bool} {len nlen : Nat} {middle : List Bool}
    (kind : block.kind = 0) (short : padding.length < 8) (size : word.length = 32)
    (first : readBits 16 word = some (len, middle)) (second : readBits 16 middle = some (nlen, []))
    (bad : nlen ≠ 65535 - len)
    (source : bytesBits log.input = block.prefix ++ padding ++ word) : Rejects log := by
  intro future output decoded
  have bodySource : bytesBits log.input = bytesBits block.wrapper.bytes ++
      (block.previous ++ block.tag ++ padding ++ word) := by
    simpa only [BlockStart.prefix, List.append_assoc] using source
  obtain ⟨bodyBytes, bytes, bits⟩ := block.wrapper.source_bytes (future := future) bodySource
  rw [bytes] at decoded
  obtain ⟨rest, blocks, _padding⟩ := block.wrapper.original_valid_body decoded
  have alignment : (block.previous ++ block.tag ++ padding ++ word ++ bytesBits future).length % 8 = 0 := by
    have lengths := congrArg List.length bits
    rw [bytesBits_length] at lengths
    omega
  have parsed : Blocks block.wrapper.dictionary []
      (block.previous ++ block.tag ++ padding ++ word ++ bytesBits future) rest output := by
    simpa only [bytesBits_eq_bytesToBits, bits] using blocks
  exact invalid_stored_blocks block kind short size first second bad alignment parsed

#print axioms invalid_stored_body
#print axioms invalid_stored_blocks
#print axioms invalid_stored_rejects
end Zlib.Inflate.Proofs.WholeEpoch
