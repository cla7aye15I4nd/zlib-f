import ZlibF.Proof.«inflate.c.fast-loaded-source-identity»
import ZlibF.Proof.«inflate.c.fast-writeback-input-scalars»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Math.InflateFastSource
set_option autoImplicit false

/-- An actual arbitrary-input loop's source origin is enough for the
rollback/LOAD identity. No independent valid source or Symbols premise
is needed. The real origin also supplies both input-budget premises of
the checked suffix, rather than requiring them from a public caller. -/
theorem FastLoopExit.loaded_source_identity_of_origin
    {ctx : FastLoopContext} {h after : Heap} {result : Zlib.Inffast.L}
    {zNext : ZStream} {sNext : InflateState} {finalSlow loaded : IL}
    {input0 : List UInt8} {inputArray : Array UInt8}
    {startOff initialHold initialBits pulled consumed used : Nat}
    (final : FastLoopExit ctx h result)
    (packet : FastInputPacket h finalSlow (input0.drop pulled) result)
    (origin : Origin initialHold initialBits input0 result.hold.toNat result.bits.toNat pulled consumed)
    (physical : result.in_ = inputAdvance (.ref ctx.inputRef startOff) pulled)
    (outputRange : FastLoopOutputRange ctx h result)
    (smallEntry : initialBits < 8)
    (initialLast : ctx.c.last = .ref ctx.inputRef (startOff + input0.length - 5))
    (rawMargin : 6 ≤ input0.length) (inputWidth : input0.length < 2 ^ 32)
    (inputGet : Space.get h ctx.inputRef = some inputArray)
    (inputBound : startOff + input0.length ≤ inputArray.size)
    (suffixRun : C.run (fastAfterLoopView ctx.c result) h = .ok ((), after))
    (finalJ : DefaultStateJ after ctx.r ctx.zs zNext sNext)
    (loadedBits : loaded.bits = sNext.bits) (loadedHold : loaded.hold = sNext.hold)
    (loadedHave : loaded.have_ = zNext.avail_in)
    (count : loaded.have_.toNat + used = input0.length) :
    used = pulled - result.bits.toNat / 8 ∧
      stream loaded (input0.drop used) = stream finalSlow (input0.drop pulled) ∧
      ∃ committed : List Bool, committed.length = consumed ∧
        natBits initialBits initialHold ++ bytesBits (input0.take used) =
          committed ++ natBits loaded.bits.toNat loaded.hold.toNat := by
  have cursor : result.in_ = .ref ctx.inputRef (startOff + pulled) := physical
  have budget : FastLoopInputBudget ctx startOff initialBits result := by
    refine ⟨startOff + pulled, cursor, by omega, ?_⟩
    have account := origin.accounting
    omega
  have limit : FastLoopInputLimit ctx result := by
    refine ⟨startOff + pulled, startOff + input0.length - 5, cursor, initialLast, ?_⟩
    have bound := origin.pulledBound
    omega
  obtain ⟨io, resultPtr, _lower, _upper, _returned, _writtenPtr,
    writtenCount, writtenBits, writtenHold⟩ :=
    final.writeback_input_scalar_fields budget limit outputRange smallEntry initialLast
      rawMargin inputWidth inputGet inputBound suffixRun finalJ
  have inputOffset : io = startOff + pulled := (Ptr.ref.inj (resultPtr.symm.trans cursor)).2
  have rollbackBound := (origin.rollback smallEntry).1
  have remaining : loaded.have_.toNat = input0.length - (pulled - result.bits.toNat / 8) := by
    rw [loadedHave, writtenCount, inputOffset]
    omega
  exact packet.loaded_source_identity origin smallEntry
    (by simpa only [loadedBits] using writtenBits)
    (by simpa only [loadedHold] using writtenHold) count remaining

#print axioms FastLoopExit.loaded_source_identity_of_origin
end Zlib.Inflate.Proofs
