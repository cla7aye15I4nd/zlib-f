import ZlibF.Proof.«inflate.c.fast-view-loop-break-mode»
import ZlibF.Proof.«inflate.c.fast-view-whole-state-fields»
import ZlibF.Proof.«inflate.c.fast-view-writeback-output-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual complete fast call carries a broken loop result only into
BAD or TYPE mode. Its normalized writeback does not change the mode. -/
theorem inflate_fast_default_view_broken_mode
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
    ∃ (finished : Heap) (zNext : ZStream)
        (sNext : InflateState) (result : Zlib.Inffast.L),
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      zNext.next_out = result.out ∧
      (result.broke = true →
        sNext.mode = BAD ∨ sNext.mode = TYPE) := by
  obtain ⟨ctx, initial, result, after, startOff, off, used,
    input, hPrefix, sameR, sameZs, startCursor, initialBits,
    ready, hLoop, final, budget, output, limit, resultCursor,
    inputGet, usedBound, count, rollback⟩ :=
    fastEntryLoop_run_with_rollback invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  obtain ⟨clearCtx, clearInitial, clearRun, clearReady,
    clear⟩ :=
    fastEntryPrefix_ready_not_broken invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have samePrefix := Except.ok.inj (clearRun.symm.trans hPrefix)
  have sameInitial : clearInitial = initial :=
    congrArg (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap =>
      p.1.2) samePrefix
  have clearActual : initial.broke = false := by
    rw [← sameInitial]
    exact clear
  obtain ⟨modeResult, modeAfter, modeRun, modeFinal,
    modePost⟩ := ready.run_broken_mode clearActual
  have sameLoop : (modeResult, modeAfter) = (result, after) :=
    Except.ok.inj (modeRun.symm.trans hLoop)
  cases sameLoop
  have sizes : ByteViewSizes h after :=
    ready.byte_view_sizes_of_run hLoop
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
    caller_range_ref_view
      (by simpa only [nextPtr] using entryBuffers.input)
  have sizeEq : input.size = initialInput.size := by
    have sized := sizes ctx.inputRef
    rw [initialGet, inputGet] at sized
    simpa only [Option.map_some, Option.some.injEq] using sized
  have inputBoundAfter : startOff + entrySlow.have_.toNat ≤
      input.size := by omega
  obtain ⟨finished, zNext, sNext, hSuffix, finalJ,
    suffixSizes, suffixFields⟩ :=
    final.writeback_window_mode_sizes budget limit output
      initialBits lastPtr inputMargin
      (UInt32.toNat_lt entrySlow.have_) inputGet
      inputBoundAfter
  have loopExact : C.run
      (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) initial) h =
      .ok (result, after) := hLoop
  have wholeRun :
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) :=
    inflate_fast_compose (some r) slow.out_ ctx.c initial result
      hPrefix loopExact hSuffix
  have storedOut := final.writeback_output_cursor
    budget limit output initialBits lastPtr inputMargin
    (UInt32.toNat_lt entrySlow.have_) inputGet inputBoundAfter
    hSuffix finalJ
  refine ⟨finished, zNext, sNext, result, wholeRun,
    by simpa only [sameR, sameZs] using finalJ,
    storedOut, ?_⟩
  intro broken
  obtain ⟨zMode, sMode, modeJ, modeKinds⟩ := modePost broken
  have suffixMode := (suffixFields zMode sMode modeJ).2
  rw [suffixMode]
  exact modeKinds

#print axioms inflate_fast_default_view_broken_mode

end Zlib.Inflate.Proofs
