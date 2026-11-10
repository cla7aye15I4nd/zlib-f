import ZlibF.Proof.«inflate.c.fast-committed-rejected-loaded»
import ZlibF.Proof.«inflate.c.fast-load-frame»
import ZlibF.Proof.«inflate.c.fast-view-public-exact-frame»
import ZlibF.Proof.«inflate.c.fast-committed-loop-geometry»
import ZlibF.Proof.«inflate.c.fast-view-caller-state»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableStability ZlibF.Spec
set_option autoImplicit false

/-- A real fast call and its translated LOAD preserve accepted-word source
content on arbitrary represented input and saved window. -/
theorem WordReady.callee_loaded_source_v4
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {bs : List UInt8} {ctx : FastLoopContext}
    {q : Zlib.Inffast.L} {p : Parameters ctx}
    (E : Env c h r zs z s)
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
      slow.bits < 8) = true)
    (prefixRun : C.run (fastEntryPrefix (some r) slow.out_) h =
      .ok ((ctx.c, q), h))
    (ready : WordReady p h q)
    (entryEq : p.entry = q)
    (rawEq : p.input = bs)
    (bitEq : q.bits = slow.bits)
    (entryPut : slow.put = .ref ctx.dest ctx.oo)
    (dstable : StableQuery DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (ltake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (dtake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (sameR : ctx.r = r) (sameZs : ctx.zs = zs) :
    ∃ finished loadedHeap zNext loadedState loaded used made
      result loopHeap array,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      runX (inflateAfterFast c) slow finished =
        .ok ((.ok (), loaded), loadedHeap) ∧
      DefaultStateJ loadedHeap r zs zNext loadedState ∧
      BufferFrame h loadedHeap
        (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, made⟩] ∧
      loaded.put = inputAdvance slow.put made ∧
      WordExit p loopHeap result ∧
      LoadedSourceOutcome p loopHeap result loaded used ∧
      WordRejectedExit p loopHeap result ∧
      LoadedRejectedOutcome p loopHeap result loaded used ∧
      ((result.broke = true ∧ ∃ i, DefaultStateJ loopHeap ctx.r ctx.zs
        {ctx.z with msg := .ref (.str i) 0} {ctx.s with mode := BAD}) →
        ∃ rejected : RejectedObservation p loopHeap result,
          WordSource rejected.toObservation ∧
          ∀ future rest output, ¬ Symbols p.L p.D p.dict p.start
            ((p.initialWords ++ rejected.word) ++ future) rest output) ∧
      loaded.have_.toNat + used = bs.length ∧
      loaded.left.toNat + made = slow.left.toNat ∧
      loaded.out_ = slow.out_ ∧
      Space.get loadedHeap ctx.dest = some array ∧
      ctx.oo + made ≤ array.size ∧
      FastPassiveFrame z zNext s loadedState ∧
      OutputSegment p loopHeap result array made
        ready.state.tracked.history := by
  obtain ⟨finished, zNext, sNext, used, made, regs,
    result, loopHeap, callRun, currentJ, finalBuffers,
    storedPut, usedBound, nextPtr, haveCount, putPtr,
    leftCount, small, budget, loopRun, exit, suffixRun,
    regsEq⟩ :=
    ready.callee_join_v2 invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast prefixRun
  obtain ⟨frameHeap, frameZ, frameS, frameUsed,
    frameMade, frameRun, frameJ, accounting, exactFrame⟩ :=
    inflate_fast_default_view_public_exact_frame invariant buffers mode
      inputCursor inputCount outputCursor outputCount stateHold stateBits fast
  have sameHeap : finished = frameHeap := congrArg Prod.snd
    (Except.ok.inj (callRun.symm.trans frameRun))
  subst frameHeap
  have sameStream : frameZ = zNext := Option.some.inj
    (frameJ.good.live.hz.symm.trans currentJ.good.live.hz)
  subst frameZ
  have pointer : zNext.next_out = inputAdvance slow.put made :=
    storedPut.symm.trans putPtr
  have framePointer : zNext.next_out = advance slow.put frameMade := by
    rw [← outputCursor]
    exact accounting.2.2.2.2.2.1
  have sameMade : frameMade = made := by
    cases sourcePtr : slow.put with
    | null => exact False.elim (buffers.output.nonnull sourcePtr)
    | ref dest off =>
        rw [sourcePtr] at pointer framePointer
        simp only [inputAdvance, advance] at pointer framePointer
        have equals := pointer.symm.trans framePointer
        have offsets := (Ptr.ref.inj equals).2
        omega
  subst frameMade
  have environment : Env c finished r zs zNext sNext :=
    ⟨E.strm, E.st, currentJ.good.live.hz,
      currentJ.good.live.hs⟩
  obtain ⟨loaded, loadedHeap, loadedState, loadRun,
    loadedJ, loadedShape⟩ :=
    inflateAfterFast_default_state_run (l := slow)
      environment currentJ
  have outputCountNat : zNext.avail_out.toNat + made = slow.left.toNat := by
    have count : regs.left.toNat + made = slow.left.toNat := leftCount
    simpa only [regsEq] using count
  obtain ⟨loadedFrame, heapFrame, stateFrame, loadFrameRun,
    frameLoadedJ, finalFrame, loadedPut, loadedLeft,
    loadedOut, loadedCount, loadedCheck,
    loadedWrap, loadedFlags, views⟩ :=
    FunctionalEpoch.inflateAfterFast_frame_credit_fields (l := slow)
      environment currentJ outputCountNat exactFrame
  have sameLoad := Except.ok.inj (loadRun.symm.trans loadFrameRun)
  have sameLoaded : loadedHeap = heapFrame := congrArg Prod.snd sameLoad
  subst heapFrame
  have outputAdvance : loaded.put = inputAdvance slow.put made := by
    rw [loadedShape]
    exact pointer
  obtain ⟨inputArray, inputGet, inputBound, outputRange⟩ :=
    ready.loop_source_geometry loopRun
  have smallEntry : p.entry.bits.toNat < 8 := by
    rw [entryEq, bitEq]
    have margins : slow.bits < 8 := by
      have facts : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
          slow.bits < 8 := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
      exact facts.2
    exact UInt32.lt_iff_toNat_lt.mp margins
  have inputWidth : p.input.length < 2 ^ 32 := by
    rw [rawEq, ← buffers.bits.have_eq]
    exact UInt32.toNat_lt slow.have_
  have loadedBits : loaded.bits = sNext.bits := by rw [loadedShape]
  have loadedHold : loaded.hold = sNext.hold := by rw [loadedShape]
  have loadedHave : loaded.have_ = zNext.avail_in := by rw [loadedShape]
  have loadedCount : loaded.have_.toNat + used = p.input.length := by
    rw [loadedHave, rawEq, ← buffers.bits.have_eq]
    have count : zNext.avail_in.toNat + used = slow.have_.toNat := by
      simpa only [regsEq] using haveCount
    exact count
  have currentCtx : DefaultStateJ finished ctx.r ctx.zs zNext sNext := by
    simpa only [sameR, sameZs] using currentJ
  have cases : LoadedSourceOutcome p loopHeap result loaded used :=
    exit.loaded_source_cases outputRange smallEntry inputWidth
      inputGet inputBound suffixRun currentCtx loadedBits loadedHold
      loadedHave loadedCount
  have loadedLeft : loaded.left.toNat + made = slow.left.toNat := by
    rw [loadedShape]
    have count : zNext.avail_out.toNat + made = slow.left.toNat := by
      simpa only [regsEq] using leftCount
    exact count
  have ctxEntry : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s :=
    ready.state.safety.source_default_state
  have sameEntryZ : ctx.z = z := by
    have hz := ctxEntry.good.live.hz
    rw [sameR] at hz
    exact Option.some.inj (hz.symm.trans invariant.good.live.hz)
  have sameEntryS : ctx.s = s := by
    have hs := ctxEntry.good.live.hs
    rw [sameZs] at hs
    exact Option.some.inj (hs.symm.trans invariant.good.live.hs)
  have smallQ : q.bits.toNat < 8 := by
    simpa only [entryEq] using smallEntry
  have passiveCtx := ready.loaded_passive_frame loopRun suffixRun
    smallQ currentCtx
    (by simpa only [sameR, sameZs] using environment) loadRun
    (by simpa only [sameR, sameZs] using loadedJ)
  have passive : FastPassiveFrame z zNext s loadedState := by
    simpa only [sameEntryZ, sameEntryS] using passiveCtx
  have suffixCursor :=
    (ready.suffix_passive_frame loopRun suffixRun smallQ currentCtx).2
  have initialOut : q.out = slow.put :=
    fastEntryPrefix_output_of_run invariant buffers mode
      inputCursor inputCount outputCursor outputCount stateHold
      stateBits fast prefixRun
  have initialPtr : q.out = .ref ctx.dest ctx.oo :=
    initialOut.trans entryPut
  have loadedPut : loaded.put = zNext.next_out := by rw [loadedShape]
  have resultPtr : result.out = .ref ctx.dest (ctx.oo + made) := by
    rw [← suffixCursor, ← loadedPut, outputAdvance, entryPut]
    rfl
  have loadViews :=
    FunctionalEpoch.inflateAfterFast_byte_views_of_run environment loadRun
  have views := ready.suffix_loaded_byte_views loopRun suffixRun
    smallQ loadViews
  obtain ⟨outputOff, outputArray, outputPtr, outputLower,
    outputUpper, outputAtLoop, outputBound⟩ := outputRange
  have outputAtLoad : Space.get loadedHeap ctx.dest = some outputArray :=
    (views ctx.dest).trans outputAtLoop
  have outputPhysicalBound : ctx.oo + made ≤ outputArray.size := by
    have offEq : outputOff = ctx.oo + made :=
      (Ptr.ref.inj (outputPtr.symm.trans resultPtr)).2
    omega
  have outputRange' : FastLoopOutputRange ctx loopHeap result :=
    ⟨outputOff, outputArray, outputPtr, outputLower,
      outputUpper, outputAtLoop, outputBound⟩
  have localFrame : BufferFrame h loadedHeap
      (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
      [⟨.ref ctx.dest ctx.oo, made⟩] := by
    simpa only [sameR, sameZs, ← entryPut] using finalFrame
  have segment := ready.output_segment exit outputRange'
    localFrame views initialPtr resultPtr outputAtLoad
  obtain ⟨rejectedResult, rejectedHeap, rejectedRun,
    rejectedExit⟩ := ready.run_with_rejected_word dstable ltake dtake
  have sameRejected : (result, loopHeap) =
      (rejectedResult, rejectedHeap) :=
    Except.ok.inj (loopRun.symm.trans rejectedRun)
  cases sameRejected
  have rejectedCases := rejectedExit.loaded_source_cases outputRange'
    smallEntry inputWidth inputGet inputBound suffixRun currentCtx
    loadedBits loadedHold loadedHave loadedCount
  have badSound :
      (result.broke = true ∧ ∃ i, DefaultStateJ loopHeap ctx.r ctx.zs
        {ctx.z with msg := .ref (.str i) 0} {ctx.s with mode := BAD}) →
        ∃ rejected : RejectedObservation p loopHeap result,
          WordSource rejected.toObservation ∧
          ∀ future rest output, ¬ Symbols p.L p.D p.dict p.start
            ((p.initialWords ++ rejected.word) ++ future) rest output := by
    intro bad
    obtain ⟨_broke, i, badJ⟩ := bad
    exact rejectedExit.no_symbols_of_bad badJ.good rfl
  refine ⟨finished, loadedHeap, zNext, loadedState, loaded,
    used, made, result, loopHeap, outputArray, callRun, loadRun,
    loadedJ, finalFrame, outputAdvance, exit, cases,
    rejectedExit, rejectedCases, badSound, ?_,
    loadedLeft, (by rw [loadedShape]), outputAtLoad, outputPhysicalBound,
    passive, segment⟩
  rw [← rawEq]
  exact loadedCount

#print axioms WordReady.callee_loaded_source_v4
end Zlib.Inflate.Proofs.FastCommittedLoop
