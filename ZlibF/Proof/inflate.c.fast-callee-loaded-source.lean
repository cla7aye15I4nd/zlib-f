import ZlibF.Proof.«inflate.c.fast-loop-source-origin-v1»
import ZlibF.Proof.«inflate.c.fast-loaded-source-identity»
import ZlibF.Proof.«inflate.c.fast-writeback-input-scalars»
import ZlibF.Proof.«inflate.c.payload-future-loop-account»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec ZlibF.Math.InflateFastSource
set_option autoImplicit false

/-- The real finite fast loop, its actual suffix and LOAD scalar fields
retain the exact independent input residual after returning unread bytes.
No exit origin or desired source equation is assumed. -/
theorem FastFutureReady.callee_loaded_source_identity
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h after finished : Heap} {q result : Zlib.Inffast.L}
    {entrySlow loaded : IL} {input0 : List UInt8} {startOff used : Nat}
    {zNext : ZStream} {sNext : InflateState}
    (semantic : FastFutureReady ctx L D dict future tail target h q)
    (entryPacket : FastInputPacket h entrySlow input0 q)
    (entryCursor : q.in_ = .ref ctx.inputRef startOff)
    (rawMargin : 6 ≤ input0.length)
    (initialLast : ctx.c.last = .ref ctx.inputRef (startOff + input0.length - 5))
    (smallEntry : q.bits.toNat < 8)
    (loopRun : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after))
    (suffixRun : C.run (fastAfterLoopView ctx.c result) after = .ok ((), finished))
    (finalJ : DefaultStateJ finished ctx.r ctx.zs zNext sNext)
    (loadedBits : loaded.bits = sNext.bits) (loadedHold : loaded.hold = sNext.hold)
    (loadedHave : loaded.have_ = zNext.avail_in)
    (count : loaded.have_.toNat + used = entrySlow.have_.toNat) :
    ∃ finalSlow pulled consumed,
      FastInputPacket after finalSlow (input0.drop pulled) result ∧
      Origin q.hold.toNat q.bits.toNat input0 result.hold.toNat result.bits.toNat pulled consumed ∧
      used = pulled - result.bits.toNat / 8 ∧
      stream loaded (input0.drop used) = stream finalSlow (input0.drop pulled) ∧
      ∃ committed : List Bool, committed.length = consumed ∧
        natBits q.bits.toNat q.hold.toNat ++ bytesBits (input0.take used) =
          committed ++ natBits loaded.bits.toNat loaded.hold.toNat := by
  obtain ⟨sourceResult, sourceAfter, finalSlow, pulled, consumed,
    sourceRun, sourceExit, finalPacket, origin, physical⟩ :=
    semantic.run_source_origin_from_entry entryPacket entryCursor rawMargin initialLast
  have sameSource := Except.ok.inj (sourceRun.symm.trans loopRun)
  cases sameSource
  obtain ⟨accountResult, accountAfter, accountRun, accountExit, budget,
    outputRange, inputLimit, sizes⟩ := semantic.run_accounted
      (FastLoopInputBudget.initial entryCursor)
  have sameAccount := Except.ok.inj (accountRun.symm.trans loopRun)
  cases sameAccount
  obtain ⟨inputRef, inputArray, inputOff, sourcePtr, sourceGet, room, _bytes⟩ :=
    entryPacket.source.next.resolve_left (by intro empty; rw [empty] at rawMargin; simp at rawMargin)
  have initialPtr : entrySlow.next = .ref ctx.inputRef startOff :=
    entryPacket.cursor.symm.trans entryCursor
  rw [initialPtr] at sourcePtr
  cases sourcePtr
  obtain ⟨afterArray, afterGet, sizeEq⟩ := sizes.view sourceGet
  have actualBound : startOff + input0.length ≤ afterArray.size := by omega
  have inputWidth : input0.length < 2 ^ 32 := by
    rw [← entryPacket.source.have_eq]
    exact UInt32.toNat_lt entrySlow.have_
  obtain ⟨io, resultPtr, _lower, _upper, _returned, _writtenPtr,
    writtenCount, writtenBits, writtenHold⟩ :=
    sourceExit.1.writeback_input_scalar_fields budget inputLimit outputRange
      smallEntry initialLast rawMargin inputWidth afterGet actualBound suffixRun finalJ
  have inputOffset : io = startOff + pulled := by
    have same := resultPtr.symm.trans physical
    simp only [inputAdvance] at same
    exact (Ptr.ref.inj same).2
  have rollbackBound := (origin.rollback smallEntry).1
  have remaining : loaded.have_.toNat = input0.length - (pulled - result.bits.toNat / 8) := by
    rw [loadedHave, writtenCount, inputOffset]
    omega
  have actualCount : loaded.have_.toNat + used = input0.length := by
    rwa [entryPacket.source.have_eq] at count
  obtain ⟨usedEq, sameStream, committed⟩ := finalPacket.loaded_source_identity origin smallEntry
    (by simpa only [loadedBits] using writtenBits)
    (by simpa only [loadedHold] using writtenHold) actualCount remaining
  exact ⟨finalSlow, pulled, consumed, finalPacket, origin, usedEq, sameStream, committed⟩

#print axioms FastFutureReady.callee_loaded_source_identity
end Zlib.Inflate.Proofs
