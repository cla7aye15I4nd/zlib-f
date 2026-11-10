import ZlibF.Proof.«inflate.c.fast-committed-callee-loaded-source»
import ZlibF.Proof.«inflate.c.fast-load-frame»
import ZlibF.Proof.«inflate.c.fast-view-public-exact-frame»
import ZlibF.Proof.«inflate.c.fast-committed-loop-geometry»
import ZlibF.Proof.«inflate.c.fast-view-caller-state»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- A real fast call and its translated LOAD preserve accepted-word source
content on arbitrary represented input and saved window. -/
theorem WordReady.callee_loaded_source_v2
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
    (sameR : ctx.r = r) (sameZs : ctx.zs = zs) :
    ∃ finished loadedHeap zNext loadedState loaded used made
      result loopHeap,
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
      loaded.have_.toNat + used = bs.length ∧
      loaded.left.toNat + made = slow.left.toNat := by
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
  refine ⟨finished, loadedHeap, zNext, loadedState, loaded,
    used, made, result, loopHeap, callRun, loadRun, loadedJ,
    finalFrame, outputAdvance, exit, cases, ?_, loadedLeft⟩
  rw [← rawEq]
  exact loadedCount

#print axioms WordReady.callee_loaded_source_v2
end Zlib.Inflate.Proofs.FastCommittedLoop
