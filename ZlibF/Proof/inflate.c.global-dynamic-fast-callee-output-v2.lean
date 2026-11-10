import ZlibF.Proof.«inflate.c.global-fast-entry-geometry»
import ZlibF.Proof.«inflate.c.fast-future-callee-prefix-cursor»
import ZlibF.Proof.«inflate.c.fast-future-checksum-frame»
import ZlibF.Proof.«inflate.c.fast-view-caller-state»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

private theorem caller_range_ref_view_any
    {h : Heap} {r : ZStreamRef} {ref : BRef}
    {off n : Nat} {write : Bool}
    (range : CallerRange h r (.ref ref off) n write) :
    ∃ array, Space.get h ref = some array ∧
      off + n ≤ array.size := by
  rcases range with null | ⟨⟨xs, bytes⟩, _, _⟩
  · cases null
  rcases bytes with empty | ⟨foundRef, foundOff, array,
      pointer, get, bound, _⟩
  · cases empty.1
  cases pointer
  exact ⟨array, get, bound⟩

/-- The actual dynamic LEN_ fast branch calls the translated fast decoder,
then executes LOAD and its TYPE back-counter update. The bytes and cursor
are those of the independent finite token parse. -/
theorem DynamicPayloadReady.fast_callee_output_v2
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {input : List UInt8} {flush : Int32}
    {future rest : List Bool} {decoded : List UInt8}
    (ready : DynamicPayloadReady h r zs log input flush future rest decoded)
    (fast : (ready.packet.boundary.regs.have_ >= 6 &&
      ready.packet.boundary.regs.left >= 258 &&
      ready.packet.boundary.regs.bits < 8) = true) :
    ∃ (ctx : FastLoopContext) (initial : Zlib.Inffast.L)
      (finished : Heap) (zNext : ZStream) (sNext : InflateState)
      (used made : Nat) (regs : IL) (result : Zlib.Inffast.L)
      (after : Heap) (array : Array UInt8) (off : Nat)
      (next : List UInt8) (loaded : IL) (loadedHeap : Heap)
      (loadedState : InflateState),
      runX (inflate_LEN_ ⟨some r, some (.tab zs), syncBuf h, flush⟩)
        ready.fastRegs
        (setI ready.packet.codeHeap zs ready.packet.boundary.state) =
          .ok ((.ok (), loaded), loadedHeap) ∧
      C.run (Zlib.Inffast.inflate_fast (some r) ready.fastRegs.out_)
        ready.fastHeap = .ok ((), finished) ∧
      C.run (fastEntryPrefix (some r) ready.fastRegs.out_)
        ready.fastHeap = .ok ((ctx.c, initial), ready.fastHeap) ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) initial) ready.fastHeap = .ok (result, after) ∧
      FastFutureExitCursor ctx
        (ready.packet.decoded.take ready.packet.codeState.nlen.toNat)
        (ready.packet.decoded.drop ready.packet.codeState.nlen.toNat)
        [] future rest decoded after result ∧
      C.run (fastAfterLoopView ctx.c result) after = .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      DefaultStateJ loadedHeap r zs zNext loadedState ∧
      loaded.put = zNext.next_out ∧
      zNext.next_out = result.out ∧
      result.out = .ref ctx.dest off ∧
      off = ctx.oo + made ∧ ctx.bg = ctx.oo ∧
      off ≤ array.size ∧
      next.length = made ∧
      Space.get loadedHeap ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array off (off - ctx.bg) = next ∧
      next <+: decoded ∧
      sNext.check = ready.calleeState.check ∧
      zNext.adler = ready.calleeStream.adler ∧
      sNext.wrap = ready.calleeState.wrap ∧
      sNext.flags = ready.calleeState.flags ∧
      loadedState.check = sNext.check ∧
      loadedState.wrap = sNext.wrap ∧
      loadedState.flags = sNext.flags ∧
      loadedState.mode = sNext.mode ∧
      loaded.left = zNext.avail_out ∧
      loaded.out_ = ready.fastRegs.out_ ∧
      loaded.left.toNat + made = ready.fastRegs.left.toNat ∧
      regs.put = zNext.next_out ∧
      regs.next = inputAdvance ready.fastRegs.next used ∧
      regs.have_.toNat + used = ready.fastRegs.have_.toNat ∧
      regs.put = inputAdvance ready.fastRegs.put made ∧
      regs.left.toNat + made = ready.fastRegs.left.toNat := by
  obtain ⟨ctx, initial, caller, prefixRun, sameR, sameZs, sameZ, sameS,
    putGeometry, _outGeometry, _inputGeometry, bitGeometry,
    _holdGeometry, leftGeometry, outTotalGeometry, _notBroken,
    semantic⟩ := ready.fast_entry_geometry fast
  obtain ⟨initialJ, buffers, inputCursor, inputCount,
    outputCursor, outputCount, stateHold, stateBits⟩ :=
    ready.fast_callee_state
  have dataMode : DataTableMode ready.calleeState.mode := by
    change DataTableMode LEN
    unfold DataTableMode
    decide
  obtain ⟨finished, zNext, sNext, used, made, regs, result, after,
    array, off, next, callRun, current, finalBuffers, storedPut,
    _usedBound, nextPtr, haveCount, putPtr, leftCount, _small,
    _budget, loopRun, semanticExit, suffixRun, resultPut,
    physical, _getAfter, getFinished, bytes, prefixBytes⟩ :=
    semantic.callee_output_prefix_cursor initialJ buffers dataMode
      inputCursor inputCount outputCursor outputCount stateHold
      stateBits fast prefixRun
  have environment : Env
      (⟨some r, some (.tab zs), syncBuf h, flush⟩ : Ctx)
      finished r zs zNext sNext :=
    ⟨rfl, rfl, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨loaded, loadedHeap, loadedState, loadRun,
    finalJ, loadShape⟩ :=
    inflateAfterFast_default_state_run (l := ready.fastRegs)
      environment current
  have callerEq :
      runX (inflate_LEN_ ⟨some r, some (.tab zs), syncBuf h, flush⟩)
        ready.fastRegs
        (setI ready.packet.codeHeap zs ready.packet.boundary.state) =
      runX (do
        Zlib.Inffast.inflate_fast (some r) ready.fastRegs.out_
        inflateAfterFast ⟨some r, some (.tab zs), syncBuf h, flush⟩)
        ready.fastRegs ready.fastHeap := by
    simpa only [DynamicPayloadReady.fastRegs,
      DynamicPayloadReady.fastHeap] using caller
  have source :
      runX (inflate_LEN_ ⟨some r, some (.tab zs), syncBuf h, flush⟩)
        ready.fastRegs
        (setI ready.packet.codeHeap zs ready.packet.boundary.state) =
        .ok ((.ok (), loaded), loadedHeap) := by
    rw [callerEq]
    have liftRun :
        runX (liftM (Zlib.Inffast.inflate_fast (some r)
          ready.fastRegs.out_) : X Unit) ready.fastRegs ready.fastHeap =
          .ok ((.ok (), ready.fastRegs), finished) := by
      exact runX_lift_ok callRun ready.fastRegs
    rw [runX_bind, liftRun]
    exact loadRun
  have exactLoad := inflateAfterFast_run environment (l := ready.fastRegs)
  have sameLoaded := Except.ok.inj (loadRun.symm.trans exactLoad)
  have heapEq : loadedHeap =
      if sNext.mode = TYPE then setI finished zs {sNext with back := -1}
      else finished := congrArg Prod.snd sameLoaded
  have loadedPut : loaded.put = zNext.next_out := by
    rw [loadShape]
  have finalGet : Space.get loadedHeap ctx.dest = some array := by
    rw [heapEq]
    by_cases type : sNext.mode = TYPE
    · simpa only [type, ↓reduceIte, byte_view_get_setI] using getFinished
    · simpa only [type, ↓reduceIte] using getFinished
  have initialSmall : initial.bits.toNat < 8 := by
    rw [bitGeometry]
    have facts :
        (6 ≤ ready.fastRegs.have_ ∧ 258 ≤ ready.fastRegs.left) ∧
          ready.fastRegs.bits < 8 := by
      simpa only [DynamicPayloadReady.fastRegs,
        Bool.and_eq_true, decide_eq_true_eq] using fast
    exact UInt32.lt_iff_toNat_lt.mp facts.2
  have currentCtx : DefaultStateJ finished ctx.r ctx.zs zNext sNext := by
    simpa only [sameR, sameZs] using current
  obtain ⟨checkFrame, adlerFrame, wrapFrame, flagsFrame⟩ :=
    semantic.callee_checksum_frame initialSmall loopRun suffixRun currentCtx
  have checkEq : sNext.check = ready.calleeState.check := by
    simpa only [sameS, DynamicPayloadReady.calleeState,
      DynamicPayloadReady.fastRegs] using checkFrame
  have adlerEq : zNext.adler = ready.calleeStream.adler := by
    simpa only [sameZ, DynamicPayloadReady.calleeStream,
      DynamicPayloadReady.fastRegs] using adlerFrame
  have wrapEq : sNext.wrap = ready.calleeState.wrap := by
    simpa only [sameS, DynamicPayloadReady.calleeState,
      DynamicPayloadReady.fastRegs] using wrapFrame
  have flagsEq : sNext.flags = ready.calleeState.flags := by
    simpa only [sameS, DynamicPayloadReady.calleeState,
      DynamicPayloadReady.fastRegs] using flagsFrame
  have loadedLeft : loaded.left = zNext.avail_out := by
    rw [loadShape]
  have loadedOut : loaded.out_ = ready.fastRegs.out_ := by
    rw [loadShape]
  have loadedStateEq : loadedState =
      if sNext.mode = TYPE then {sNext with back := -1}
      else sNext := by
    by_cases type : sNext.mode = TYPE
    · have get := finalJ.good.live.hs
      simp only [heapEq, type, ↓reduceIte,
        setI_istates_same] at get
      have eq := Option.some.inj get.symm
      simpa only [type, ↓reduceIte] using eq
    · have get := finalJ.good.live.hs
      simp only [heapEq, type, ↓reduceIte] at get
      have eq := Option.some.inj
        (get.symm.trans current.good.live.hs)
      simpa only [type, ↓reduceIte] using eq
  have loadedCheck : loadedState.check = sNext.check := by
    rw [loadedStateEq]
    split <;> rfl
  have loadedWrap : loadedState.wrap = sNext.wrap := by
    rw [loadedStateEq]
    split <;> rfl
  have loadedFlags : loadedState.flags = sNext.flags := by
    rw [loadedStateEq]
    split <;> rfl
  have loadedMode : loadedState.mode = sNext.mode := by
    rw [loadedStateEq]
    split <;> rfl
  have offEq : off = ctx.oo + made := by
    have join : inputAdvance ready.fastRegs.put made =
        .ref ctx.dest off :=
      putPtr.symm.trans (storedPut.trans (resultPut.trans physical))
    unfold DynamicPayloadReady.fastRegs at join
    rw [putGeometry, inputAdvance] at join
    exact (Ptr.ref.inj join).2.symm
  have noOutput : ready.fastRegs.out_ = ready.fastRegs.left := by
    obtain ⟨_bound, _origin, _buffers, _bits, _next, _have,
      _put, _left, noOutput, _window, _mode, _symbols,
      _dispatch⟩ := ready.packet.endpoint
    simpa only [DynamicPayloadReady.fastRegs] using noOutput
  have bgEq : ctx.bg = ctx.oo := by
    rw [ctx.beginEq, outTotalGeometry, leftGeometry]
    simp only [DynamicPayloadReady.fastRegs] at noOutput ⊢
    rw [noOutput]
    simp
  have bound : off ≤ array.size := by
    have finalPtr : regs.put = .ref ctx.dest off :=
      storedPut.trans (resultPut.trans physical)
    have range : CallerRange finished r (.ref ctx.dest off)
        regs.left.toNat true := by
      rw [← finalPtr]
      exact finalBuffers.output.range
    obtain ⟨rangeArray, getRange, upper⟩ :=
      caller_range_ref_view_any range
    have sameArray : rangeArray = array :=
      Option.some.inj (getRange.symm.trans getFinished)
    subst rangeArray
    omega
  have outputLength : next.length = made := by
    rw [← bytes, offEq, bgEq]
    simp only [ZlibF.Math.LZ77Copy.writtenBytes,
      List.length_take, List.length_drop, Array.length_toList]
    omega
  refine ⟨ctx, initial, finished, zNext, sNext, used, made,
    regs, result, after, array, off, next, loaded, loadedHeap,
    loadedState, source, callRun, prefixRun, loopRun,
    semanticExit, suffixRun,
    current, finalJ, loadedPut, resultPut,
    physical, offEq, bgEq, bound, outputLength, finalGet, bytes, prefixBytes,
    checkEq, adlerEq,
    wrapEq, flagsEq, loadedCheck, loadedWrap, loadedFlags,
    loadedMode,
    loadedLeft, loadedOut, ?_, storedPut,
    nextPtr, haveCount, putPtr, leftCount⟩
  obtain ⟨otherFinished, otherZ, otherS, otherUsed,
    otherMade, otherRun, otherJ, accounting,
    _sizes, _window, _modes, _bits, _readonly, _live,
    _nalloc, _budget⟩ :=
    inflate_fast_default_view_caller_budget initialJ buffers dataMode
      inputCursor inputCount outputCursor outputCount stateHold
      stateBits fast
  have sameHeap : finished = otherFinished := congrArg Prod.snd
    (Except.ok.inj (callRun.symm.trans otherRun))
  subst otherFinished
  have sameStream : otherZ = zNext := Option.some.inj
    (otherJ.good.live.hz.symm.trans current.good.live.hz)
  subst otherZ
  rcases accounting with ⟨_inBound, _outBound, _inCount,
    outCount, _inPtr, outPtr, _state, _alloc,
    _free, _opaque, _reserved⟩
  have sameMade : otherMade = made := by
    have startPtr : ready.calleeStream.next_out =
        .ref ctx.dest ctx.oo :=
      outputCursor.trans putGeometry
    rw [startPtr, ZlibF.Spec.Public.advance] at outPtr
    have endPtr : zNext.next_out = .ref ctx.dest
        (ctx.oo + made) := by
      rw [resultPut, physical, offEq]
    have equals := outPtr.symm.trans endPtr
    have offset := (Ptr.ref.inj equals).2
    omega
  subst otherMade
  rw [loadedLeft, ← outputCount]
  exact outCount

#print axioms DynamicPayloadReady.fast_callee_output_v2
end Zlib.Inflate.Proofs.FunctionalEpoch
