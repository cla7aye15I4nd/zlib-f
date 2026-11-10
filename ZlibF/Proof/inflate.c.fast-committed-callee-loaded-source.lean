import ZlibF.Proof.«inflate.c.fast-committed-callee-join-v2»
import ZlibF.Proof.«inflate.c.fast-committed-loop-geometry»
import ZlibF.Proof.«inflate.c.fast-view-caller-state»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast loop's accepted normal/EOB exit carries the exact
committed word through suffix rollback and LOAD. BAD remains a separate
source-proved outcome. -/
def LoadedSourceOutcome {ctx : FastLoopContext}
    (p : Parameters ctx) (loopHeap : Heap) (result : Zlib.Inffast.L)
    (loaded : IL) (used : Nat) : Prop :=
    (∃ tracked : Tracked p loopHeap result,
      WordSource tracked.toObservation ∧
      stream loaded (p.input.drop used) =
        stream tracked.slow (p.input.drop tracked.pulled) ∧
      natBits p.entry.bits.toNat p.entry.hold.toNat ++
        bytesBits (p.input.take used) =
        tracked.word ++ natBits loaded.bits.toNat loaded.hold.toNat) ∨
    (∃ ended : Ended p loopHeap result,
      WordSource ended.toObservation ∧
      stream loaded (p.input.drop used) =
        stream ended.slow (p.input.drop ended.pulled) ∧
      natBits p.entry.bits.toNat p.entry.hold.toNat ++
        bytesBits (p.input.take used) =
        ended.word ++ natBits loaded.bits.toNat loaded.hold.toNat) ∨
    (result.broke = true ∧ ∃ i,
      DefaultStateJ loopHeap ctx.r ctx.zs
        {ctx.z with msg := .ref (.str i) 0}
        {ctx.s with mode := BAD})

/-- A real fast call and its translated LOAD preserve accepted-word source
content on arbitrary represented input and saved window. -/
theorem WordReady.callee_loaded_source
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
  have environment : Env c finished r zs zNext sNext :=
    ⟨E.strm, E.st, currentJ.good.live.hz,
      currentJ.good.live.hs⟩
  obtain ⟨loaded, loadedHeap, loadedState, loadRun,
    loadedJ, loadedShape⟩ :=
    inflateAfterFast_default_state_run (l := slow)
      environment currentJ
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
    exit, cases, ?_, loadedLeft⟩
  rw [← rawEq]
  exact loadedCount

#print axioms WordReady.callee_loaded_source
end Zlib.Inflate.Proofs.FastCommittedLoop
