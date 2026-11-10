import ZlibF.Proof.«inflate.c.whole-epoch-fast-normal-progress-v4»
import ZlibF.Math.«whole-epoch-compressed-rejection-v1»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch Zlib.Inflate.Proofs.FastCommittedLoop
open ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false

theorem EpochCallCut4.fast_eob_progress
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).dictionary
      epoch.facts.word (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).output)
    (last : (leaveState s l).last = Int32.ofNat boundary.block.last)
    (mode : s.mode = LEN)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (full : FastCommittedCallCutV8 c h r zs z s l (raw.drop epoch.facts.used)
      boundary.L boundary.D boundary.block.wrapper.dictionary base.output epoch.facts.emitted)
    (ended : Ended full.cut.p full.cut.loopHeap full.cut.result)
    (source : WordSource ended.toObservation)
    (nextMode : full.cut.loadedState.mode = TYPE) : Nonempty (DispatchResult4 epoch) := by
  let cut := full.cut
  obtain ⟨facts, _used, emitted, word⟩ := epoch.fast_observation_facts full ended.toObservation source mode fast
  have normalized : leaveState cut.loadedState cut.loaded = cut.loadedState := by
    simp only [leaveState, cut.loadedHold, cut.loadedBits]
  have segment : Symbols boundary.L boundary.D boundary.block.wrapper.dictionary
      (base.output ++ epoch.facts.emitted) ended.word [] (base.output ++ ended.history) := by
    simpa only [full.cut.pL, full.cut.pD, full.cut.pDict, full.cut.pPast,
      full.cut.pStart, full.cut.pWords, List.nil_append] using ended.symbols
  have nextLast : cut.loadedState.last = Int32.ofNat boundary.block.last := by
    have frame := cut.fullState
    change cut.loadedState = {s with mode := cut.loadedState.mode, hold := cut.loadedState.hold, bits := cut.loadedState.bits, back := cut.loadedState.back} at frame
    rw [frame]
    exact last
  let nextLog := sourceLog (callLog base raw facts.used facts.emitted)
  have parsed : Symbols boundary.L boundary.D boundary.block.wrapper.dictionary
      (base.output ++ epoch.facts.emitted) ended.word [] nextLog.output := by
    dsimp only [nextLog, sourceLog, callLog]
    rw [emitted]
    exact segment
  let phase : SourcePhase nextLog (leaveState cut.loadedState cut.loaded) facts.word := by
    rw [word]
    exact boundary.ended_phase (log := nextLog) (Or.inl nextMode) nextLast parsed
  have materialized : phase.Materialized cut.loadedHeap :=
    WholeWrapper.low_materialized phase (by change cut.loadedState.mode ≤ TYPE; rw [nextMode]; decide)
  have reversible : phase.Reversible :=
    phase.reversible_of_not_codes (by change cut.loadedState.mode ≠ CODELENS; rw [nextMode]; decide)
  exact ⟨.progress cut.loadedHeap cut.zNext cut.loadedState cut.loaded
    (cut.dispatch_run epoch.facts.env mode fast) ⟨facts, .legacy phase, materialized, reversible⟩⟩

theorem EpochCallCut4.fast_bad_progress
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).dictionary
      epoch.facts.word (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).output)
    (mode : s.mode = LEN)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (full : FastCommittedCallCutV8 c h r zs z s l (raw.drop epoch.facts.used)
      boundary.L boundary.D boundary.block.wrapper.dictionary base.output epoch.facts.emitted)
    (bad : RejectedObservation full.cut.p full.cut.loopHeap full.cut.result)
    (source : WordSource bad.toObservation)
    (nextMode : full.cut.loadedState.mode = BAD) : Nonempty (DispatchResult4 epoch) := by
  let cut := full.cut
  obtain ⟨facts, _used, _emitted, word⟩ := epoch.fast_observation_facts full bad.toObservation source mode fast
  have rejected : Rejects (sourceLog (callLog base raw facts.used facts.emitted)) := by
    apply Compressed.rejects_credited (log := sourceLog (callLog base raw facts.used facts.emitted)) boundary (badCredit := bad.word ++ held (leaveState cut.loadedState cut.loaded))
    · have bits := facts.credited
      change bytesBits (base.input ++ raw.take facts.used) = facts.word ++
        natBits cut.loaded.bits.toNat cut.loaded.hold.toNat at bits
      rw [word] at bits
      simpa only [sourceLog, callLog, held, leaveState, List.append_assoc] using bits
    · intro future rest output
      have noParse := bad.no_symbols (held (leaveState cut.loadedState cut.loaded) ++ future) rest output
      simpa only [full.cut.pL, full.cut.pD, full.cut.pDict, full.cut.pStart,
        full.cut.pWords, List.nil_append, List.append_assoc, sourceLog, callLog] using noParse
  let phase : SourcePhase (sourceLog (callLog base raw facts.used facts.emitted))
      (leaveState cut.loadedState cut.loaded) facts.word := .rejected nextMode rejected
  exact ⟨.progress cut.loadedHeap cut.zNext cut.loadedState cut.loaded
    (cut.dispatch_run epoch.facts.env mode fast) ⟨facts, .legacy phase, True.intro, True.intro⟩⟩

#print axioms EpochCallCut4.fast_eob_progress
#print axioms EpochCallCut4.fast_bad_progress
end Zlib.Inflate.Proofs.WholeEpoch
