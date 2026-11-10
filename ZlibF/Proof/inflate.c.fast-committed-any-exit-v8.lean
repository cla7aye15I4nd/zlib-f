import ZlibF.Proof.«inflate.c.fast-committed-any-exit-segment-v8»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FastCommittedLoop
set_option autoImplicit false

/-- A physical output segment and the actual observed history are retained
for normal, EOB and BAD exits alike. -/
structure FastCommittedCallCutV8
    (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) (slow : IL) (bs : List UInt8)
    (L D : List Nat) (dict past current : List UInt8) where
  cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current
  entryHistory : cut.ready.state.tracked.history = current
  observationSegment : ∀ observation : Observation cut.p cut.loopHeap cut.result,
    ∃ more : List UInt8,
      more.length = cut.made ∧
      ZlibF.Math.LZ77Copy.writtenBytes cut.array (cut.ctx.oo + cut.made) cut.made = more ∧
      observation.history = current ++ more

theorem PayloadRepresentation.restore_committed_fast_call_cut_v8
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    {L D : List Nat} {dict past current : List UInt8}
    (E : Env c h r zs z s)
    (representation : PayloadRepresentation h r zs z s slow bs L D (dict ++ past))
    (mode : DataTableMode s.mode)
    (queryTake : InstalledQueryTake h s)
    (flags : InstalledQueryFlags h s)
    (historyView : ∀ dest oo output,
      slow.put = .ref dest oo → Space.get h dest = some output →
      ZlibF.Math.LZ77Copy.writtenBytes output oo
        (slow.out_.toNat - slow.left.toNat) = current)
    (fast : (slow.have_ >= 6 && slow.left >= 258 && slow.bits < 8) = true) :
    Nonempty (FastCommittedCallCutV8 c h r zs z s slow bs L D dict past current) := by
  obtain ⟨ctx, q, p, restoreRun, prefixRun, wordReady,
    meaningL, meaningD, sameDict, samePast,
    start, words, raw, entry, sameR, sameZs,
    sameZ, sameS, put, left, out, input, heldBits,
    heldHold⟩ :=
    representation.restore_committed_fast_entry_v2 E mode
      flags historyView fast
  obtain ⟨ready⟩ := wordReady
  obtain ⟨restoredRun, afterRep⟩ := representation.restore E
  obtain ⟨origin, buffers, bits, tables, dictionary⟩ := afterRep
  have dataMode : DataTableMode (leaveState s slow).mode := by
    change DataTableMode s.mode
    exact mode
  have restoredTake : InstalledQueryTake
      (setI (r.put h (leaveStream z slow)) zs (leaveState s slow))
      (leaveState s slow) :=
    queryTake.restore representation.1.good.live.hs slow
  obtain ⟨lenCode, distCode, lenWidth, distWidth⟩ :=
    fastEntryPrefix_table_geometry_of_run origin.toDefaultStateJ
      buffers dataMode rfl rfl rfl rfl rfl rfl fast prefixRun
  have tablesCtx : InstalledTables
      (setI (r.put h (leaveStream z slow)) zs (leaveState s slow))
      ctx.s L D := by simpa only [sameS] using tables
  have takeCtx : InstalledQueryTake
      (setI (r.put h (leaveStream z slow)) zs (leaveState s slow))
      ctx.s := by simpa only [sameS] using restoredTake
  obtain ⟨dstable, ltake, dtake⟩ :=
    ready.installed_query_properties tablesCtx takeCtx
      (by simpa only [sameS] using lenCode)
      (by simpa only [sameS] using distCode)
      (by simpa only [sameS] using lenWidth)
      (by simpa only [sameS] using distWidth)
  obtain ⟨finished, loadedHeap, zNext, loadedState,
    loaded, used, made, result, loopHeap, array, regs, sNext,
    callRun, loadRun,
    loadedJ, currentJ, frame, outputAdvance,
    exit, outcome, rejectedExit, rejectedOutcome, badSound,
    haveCount, leftCount, loadedOut,
    outputGet, outputBound,
    passive, coreRestored, segment,
    loopRun, suffixRun, finalBuffers, regsShape, loadedRegs,
    loadedNext, loadedIn, loadedRet, loadedBits, loadedHold,
    bitsSmall, bitsBudget⟩ :=
    ready.callee_loaded_source_v7
      ⟨E.strm, E.st, origin.good.live.hz,
        origin.good.live.hs⟩
      origin.toDefaultStateJ buffers dataMode
      rfl rfl rfl rfl rfl rfl fast prefixRun
      entry raw heldBits put dstable ltake dtake sameR sameZs
  obtain ⟨oldArray, restoredGet⟩ :=
    FastCommittedLoop.FastLoopReady.output_array ready.state.safety
  have oldGet : Space.get h ctx.dest = some oldArray := by
    simpa only [byte_view_get_setI, byte_view_get_stream_put]
      using restoredGet
  have entryOut : q.out = slow.put :=
    fastEntryPrefix_output_of_run origin.toDefaultStateJ buffers
      dataMode rfl rfl rfl rfl rfl rfl fast prefixRun
  have entryPtr : q.out = .ref ctx.dest ctx.oo := entryOut.trans put
  have countEq : ctx.oo - ctx.bg =
      slow.out_.toNat - slow.left.toNat := by
    rw [ctx.beginEq, out, left]
    have bound := ctx.made
    rw [out, left] at bound
    omega
  have seen : ZlibF.Math.LZ77Copy.writtenBytes oldArray ctx.oo
      (ctx.oo - ctx.bg) = current := by
    rw [countEq]
    exact historyView ctx.dest ctx.oo oldArray put oldGet
  have oldEq := ready.entry_history_eq entryPtr restoredGet seen
  have exactSegment : OutputSegment p loopHeap result array made current := by
    simpa only [oldEq] using segment
  have core : FastFinalStateFrame s loadedState :=
    coreRestored.restore_input
  have usedBound : used ≤ bs.length := by omega
  have Efinished : Env c finished r zs zNext sNext :=
    ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
  have loadCore := inflateAfterFast_state_core_frame Efinished loadRun loadedJ
  have loadViews := inflateAfterFast_byte_views_of_run Efinished loadRun
  have loadShape : loadedHeap =
      if sNext.mode = TYPE then setI finished zs { sNext with back := -1 }
      else finished := by
    have actual := inflateAfterFast_run (l := slow) Efinished
    have pair := Except.ok.inj (loadRun.symm.trans actual)
    exact congrArg Prod.snd pair
  have loadRo : ∀ ref : BRef, Space.ro loadedHeap ref = Space.ro finished ref := by
    intro ref
    rw [loadShape]
    split
    · exact byte_view_ro_setI finished zs {sNext with back := -1} ref
    · rfl
  have loadWindow : loadedState.window = sNext.window := by
    rw [loadCore]
  have loadedBuffers : DispatchBuffers loadedHeap r loaded (bs.drop used) := by
    rw [loadedRegs]
    exact finalBuffers.byte_views currentJ.good loadedJ.good loadWindow loadViews loadRo
  have allocRestored :
      (setI (r.put h (leaveStream z slow)) zs (leaveState s slow)).allocOk = h.allocOk := by
    cases r <;> simp [setI, ZStreamRef.put] <;> split <;> rfl
  have allocLoaded : loadedHeap.allocOk = h.allocOk := by
    have oracle := frame.1.2.1.trans
      (ZlibF.Spec.Public.CausalAllocationOracle.restore_regions
        (setI (r.put h (leaveStream z slow)) zs (leaveState s slow))
        loadedHeap [⟨slow.put, made⟩])
    exact oracle.symm.trans allocRestored
  have sCheck : loadedState.check = s.check := by
    simpa only [leaveState] using passive.1
  have sWrap : loadedState.wrap = s.wrap := by
    simpa only [leaveState] using passive.2.1
  have sFlags : loadedState.flags = s.flags := by
    simpa only [leaveState] using passive.2.2.1
  have sLenCode : loadedState.lencode = s.lencode := by
    simpa only [leaveState] using passive.2.2.2.1
  have sDistCode : loadedState.distcode = s.distcode := by
    simpa only [leaveState] using passive.2.2.2.2.1
  have zAdler : zNext.adler = z.adler := by
    simpa only [leaveStream] using passive.2.2.2.2.2.1
  have zAlloc : zNext.zalloc = z.zalloc := by
    simpa only [leaveStream] using passive.2.2.2.2.2.2.1
  have zFree : zNext.zfree = z.zfree := by
    simpa only [leaveStream] using passive.2.2.2.2.2.2.2.1
  let cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current := {
    ctx := ctx, q := q, p := p, restored := _, finished := finished,
    loadedHeap := loadedHeap, loopHeap := loopHeap,
    zNext := zNext, sNext := sNext, loadedState := loadedState,
    loaded := loaded, regs := regs, result := result, used := used,
    made := made, array := array, ready := ready,
    envStrm := E.strm, envState := E.st,
    entrySmall := (by
      rw [heldBits]
      have margin : slow.bits < 8 := by
        have all : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧ slow.bits < 8 := by
          simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
        exact all.2
      exact UInt32.lt_iff_toNat_lt.mp margin),
    restoreShape := rfl, restoreRun := restoreRun, prefixRun := prefixRun,
    loopRun := loopRun, suffixRun := suffixRun, callRun := callRun,
    loadRun := loadRun, initialJ := origin.toDefaultStateJ,
    finalJ := loadedJ, currentJ := currentJ, finalBuffers := finalBuffers,
    loadedBuffers := loadedBuffers, frame := frame, fullState := core,
    passive := passive, sourceExit := exit, sourceLoaded := outcome,
    rejectedExit := rejectedExit, rejectedLoaded := rejectedOutcome,
    badSound := badSound, outputSegment := exactSegment,
    pL := meaningL, pD := meaningD, pDict := sameDict,
    pPast := samePast, pStart := start, pWords := words,
    pInput := raw, pEntry := entry, qBits := heldBits,
    qHold := heldHold, qIn := input, qOut := entryOut,
    ctxR := sameR, ctxZs := sameZs, ctxZ := sameZ, ctxS := sameS,
    ctxPut := put, ctxLeft := left, ctxOut := out,
    usedBound := usedBound, haveCount := haveCount,
    leftCount := leftCount, loadedOut := loadedOut,
    loadedRet := loadedRet, loadedIn := loadedIn,
    loadedNext := loadedNext, loadedPut := outputAdvance,
    loadedBits := loadedBits, loadedHold := loadedHold,
    bitsSmall := bitsSmall, bitsBudget := bitsBudget,
    outputGet := outputGet, outputBound := outputBound,
    regsShape := regsShape, loadedRegs := loadedRegs,
    allocOracle := allocLoaded, zAdler := zAdler,
    zAlloc := zAlloc, zFree := zFree,
    sCheck := sCheck, sWrap := sWrap, sFlags := sFlags,
    sLenCode := sLenCode, sDistCode := sDistCode }
  exact ⟨{
    cut := cut
    entryHistory := oldEq
    observationSegment := fun observation => cut.observation_segment observation oldEq }⟩


#print axioms PayloadRepresentation.restore_committed_fast_call_cut_v8
end Zlib.Inflate.Proofs.FunctionalEpoch
