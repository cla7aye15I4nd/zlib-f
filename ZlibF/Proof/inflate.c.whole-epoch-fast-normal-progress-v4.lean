import ZlibF.Proof.«inflate.c.whole-epoch-fast-facts-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-fast-tables-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-compressed-segments»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch Zlib.Inflate.Proofs.FastCommittedLoop
open ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false

/-- An actual normal finite fast run extends the same block source word
and returns a complete revised call cut, with the actual emitted prefix. -/
theorem EpochCallCut4.fast_normal_progress
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).dictionary
      epoch.facts.word (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).output)
    (last : (leaveState s l).last = Int32.ofNat boundary.block.last)
    (mode : s.mode = LEN)
    (selected : epoch.phase = .legacy (.ready boundary (Or.inr mode) last))
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (full : FastCommittedCallCutV8 c h r zs z s l (raw.drop epoch.facts.used)
      boundary.L boundary.D boundary.block.wrapper.dictionary base.output epoch.facts.emitted)
    (normal : Tracked full.cut.p full.cut.loopHeap full.cut.result)
    (source : WordSource normal.toObservation)
    (nextMode : full.cut.loadedState.mode = LEN) : Nonempty (DispatchResult4 epoch) := by
  let cut := full.cut
  obtain ⟨facts, used, emitted, word⟩ := epoch.fast_observation_facts full normal.toObservation source mode fast
  have normalized : leaveState cut.loadedState cut.loaded = cut.loadedState := by
    simp only [leaveState, cut.loadedHold, cut.loadedBits]
  have segment : Committed boundary.L boundary.D boundary.block.wrapper.dictionary
      (base.output ++ epoch.facts.emitted) normal.word (base.output ++ normal.history) := by
    simpa only [full.cut.pL, full.cut.pD, full.cut.pDict, full.cut.pPast, full.cut.pStart, full.cut.pWords, List.nil_append] using normal.committed
  let advanced := boundary.advance_segment segment
  let nextBoundary : Compressed
      (sourceLog (callLog base raw facts.used facts.emitted)).dictionary facts.word
      (sourceLog (callLog base raw facts.used facts.emitted)).output := {
    advanced with
    committed := by rw [emitted]; exact advanced.committed
    anchor := by rw [word]; exact advanced.anchor }
  have nextLast : cut.loadedState.last = Int32.ofNat nextBoundary.block.last := by
    change cut.loadedState.last = Int32.ofNat boundary.block.last
    have frame := cut.fullState
    change cut.loadedState = {s with mode := cut.loadedState.mode, hold := cut.loadedState.hold, bits := cut.loadedState.bits, back := cut.loadedState.back} at frame
    rw [frame]
    exact last
  let phase : SourcePhase (sourceLog (callLog base raw facts.used facts.emitted))
      (leaveState cut.loadedState cut.loaded) facts.word :=
    .ready nextBoundary (Or.inr nextMode) nextLast
  have oldTables := epoch.materialized
  rw [selected] at oldTables
  have tables : TableBinding cut.loadedHeap cut.loadedState boundary.L boundary.D :=
    epoch.fast_tables cut oldTables.1 mode fast
  have materialized : phase.Materialized cut.loadedHeap := by
    change TableBinding cut.loadedHeap (leaveState cut.loadedState cut.loaded) nextBoundary.L nextBoundary.D
    exact tables
  have reversible : phase.Reversible := phase.reversible_of_not_codes (by change cut.loadedState.mode ≠ CODELENS; rw [nextMode]; decide)
  exact ⟨.progress cut.loadedHeap cut.zNext cut.loadedState cut.loaded
    (cut.dispatch_run epoch.facts.env mode fast) ⟨facts, .legacy phase, materialized, reversible⟩⟩

#print axioms EpochCallCut4.fast_normal_progress
end Zlib.Inflate.Proofs.WholeEpoch
