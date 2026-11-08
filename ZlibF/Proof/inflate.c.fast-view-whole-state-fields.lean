import ZlibF.Proof.«inflate.c.fast-view-loop-state-fields»
import ZlibF.Proof.«inflate.c.fast-view-entire-safe»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual normalized suffix preserves every byte-object size, the
window pointer, and the decoder mode. -/
theorem FastLoopExit.writeback_window_mode_sizes
    {ctx : FastLoopContext} {h : Heap} {result : Zlib.Inffast.L}
    {startOff startBits inputCount : Nat} {input : Array UInt8}
    (final : FastLoopExit ctx h result)
    (account : FastLoopInputBudget ctx startOff startBits result)
    (limit : FastLoopInputLimit ctx result)
    (output : FastLoopOutputRange ctx h result)
    (initialBits : startBits < 8)
    (last : ctx.c.last = .ref ctx.inputRef (startOff + inputCount - 5))
    (inputMargin : 6 ≤ inputCount) (inputWidth : inputCount < 2 ^ 32)
    (inputGet : Space.get h ctx.inputRef = some input)
    (inputBound : startOff + inputCount ≤ input.size) :
    ∃ finished zNext sNext,
      C.run (fastAfterLoopView ctx.c result) h = .ok ((), finished) ∧
      DefaultStateJ finished ctx.r ctx.zs zNext sNext ∧
      ByteViewSizes h finished ∧
      ∀ z s, DefaultStateJ h ctx.r ctx.zs z s →
        sNext.window = s.window ∧ sNext.mode = s.mode := by
  obtain ⟨slow, bs, z, s, packet, invariant, buffers⟩ := final
  obtain ⟨io, inPtr, lower, budget⟩ := account
  obtain ⟨io2, lastOff, limitPtr, lastPtr, upper⟩ := limit
  have sameIn : io2 = io := (Ptr.ref.inj (limitPtr.symm.trans inPtr)).2
  subst io2
  have sameLast : lastOff = startOff + inputCount - 5 :=
    (Ptr.ref.inj (lastPtr.symm.trans last)).2
  subst lastOff
  obtain ⟨oo, array, outPtr, outputLower, outputUpper, outputGet, outputSize⟩ := output
  have returned : (result.bits >>> 3).toNat ≤ io - startOff := by
    rw [Zlib.Inffast.Proofs.bits_whole]
    omega
  have inputFit : input.size < 2 ^ 63 := invariant.platform ctx.inputRef input inputGet
  have outputFit : array.size < 2 ^ 63 := invariant.platform ctx.dest array outputGet
  have outputWidth := UInt32.toNat_lt ctx.leftTotal
  have outputMargin := ctx.avail
  have raw := fastAfterLoopView_run ctx.c result ctx.streamPtr ctx.statePtr
    invariant.good.live.hz (by cases ctx.r <;> rfl) invariant.good.live.hs
    inputGet outputGet inputFit outputFit inPtr last outPtr ctx.endPtr
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  let bits := result.bits - ((result.bits >>> 3) <<< 3)
  let hold := result.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  let in_ : BPtr := .ref ctx.inputRef (io - (result.bits >>> 3).toNat)
  let ai := UInt32.ofNat
    (startOff + inputCount - 5 + 5 - (io - (result.bits >>> 3).toNat))
  let ao := UInt32.ofNat (ctx.oo + ctx.leftTotal.toNat - 257 + 257 - oo)
  let zNext : ZStream := { z with
    next_in := in_, next_out := result.out,
    avail_in := ai, avail_out := ao }
  let sNext : InflateState := { s with hold, bits }
  let finished := setI (ctx.r.put h zNext) ctx.zs sNext
  have run : C.run (fastAfterLoopView ctx.c result) h = .ok ((), finished) := by
    simpa only [finished, zNext, sNext, hold, bits, in_, ai, ao, setI, C.run] using raw
  have resultJ := (invariant.fast_writeback_normalized result in_ result.out ai ao).1
  refine ⟨finished, zNext, sNext, run, resultJ, ?_, ?_⟩
  · exact (byte_view_sizes_stream_put h ctx.r zNext).trans
      (byte_view_sizes_setI _ ctx.zs sNext)
  · intro zOther sOther otherJ
    have sourceEq : sOther = s := Option.some.inj
      (otherJ.good.live.hs.symm.trans invariant.good.live.hs)
    subst sOther
    exact ⟨rfl, rfl⟩

#print axioms FastLoopExit.writeback_window_mode_sizes

/-- The translated full fast call preserves all byte-object sizes and its
entry window. Its final mode is the entry mode, TYPE, or BAD. -/
theorem inflate_fast_default_view_state_fields
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ finished zNext sNext,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      ByteViewSizes h finished ∧
      sNext.window = s.window ∧
      (sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) := by
  obtain ⟨ctx, initial, result, after, startOff, off, used,
    input, hPrefix, sameR, sameZs, startCursor, initialBits, ready, hLoop,
    final, budget, output, limit, resultCursor, inputGet,
    usedBound, count, rollback⟩ :=
    fastEntryLoop_run_with_rollback invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have sizes : ByteViewSizes h after := ready.byte_view_sizes_of_run hLoop
  have fields := ready.window_mode_of_run hLoop
  obtain ⟨entrySlow, entryBs, entryOutput, entryOff, k,
    packet, entryJ, entryBuffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr,
    inputMargin, outPtr, outputGet, outputWrite,
    outputSize, current, beginLe, span, guard⟩ := ready
  have entryCursor : entrySlow.next = .ref ctx.inputRef startOff :=
    packet.cursor.symm.trans startCursor
  have sameEntryOff : entryOff = startOff :=
    (Ptr.ref.inj (nextPtr.symm.trans entryCursor)).2
  subst entryOff
  obtain ⟨initialInput, initialGet, initialBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using entryBuffers.input)
  have sizeEq : input.size = initialInput.size := by
    have sized := sizes ctx.inputRef
    rw [initialGet, inputGet] at sized
    simpa only [Option.map_some, Option.some.injEq] using sized
  have inputBoundAfter : startOff + entrySlow.have_.toNat ≤ input.size := by
    omega
  obtain ⟨finished, zNext, sNext, hSuffix, finalJ, suffixSizes, suffixFields⟩ :=
    final.writeback_window_mode_sizes budget limit output initialBits lastPtr
      inputMargin (UInt32.toNat_lt entrySlow.have_)
      inputGet inputBoundAfter
  obtain ⟨finalSlow, finalBs, finalZ, finalS, finalPacket,
    loopJ, finalBuffers⟩ := final
  have loopFields := fields finalZ finalS loopJ
  have suffixFields := suffixFields finalZ finalS loopJ
  have sameSource : ctx.s = s := by
    have hs := entryJ.good.live.hs
    rw [sameZs] at hs
    exact Option.some.inj (hs.symm.trans invariant.good.live.hs)
  have loopExact : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ ctx.c.last then
          pure (← Ptr.lt q.out ctx.c.end_, q)
        else pure (false, q)) initial) h = .ok (result, after) := hLoop
  refine ⟨finished, zNext, sNext,
    inflate_fast_compose (some r) slow.out_ ctx.c initial result
      hPrefix loopExact hSuffix, ?_, sizes.trans suffixSizes, ?_, ?_⟩
  · simpa only [sameR, sameZs] using finalJ
  · rw [suffixFields.1, loopFields.1, sameSource]
  · rw [suffixFields.2]
    simpa only [sameSource] using loopFields.2

#print axioms inflate_fast_default_view_state_fields
end Zlib.Inflate.Proofs
