import ZlibF.Proof.«inflate.c.whole-epoch-ready-fast-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-fast-source-any»
import ZlibF.Proof.«inflate.c.whole-epoch-window-frame»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch Zlib.Inflate.Proofs.FunctionalTrailer
open Zlib.Inflate.Proofs.FastCommittedLoop ZlibF.Math.LZ77Copy
set_option autoImplicit false

theorem OutputCredit.observed_bytes
    {h : Heap} {z : ZStream} {s : InflateState} {l : IL}
    {prior emitted : List UInt8} {count : Nat}
    (ledger : OutputCredit h z s l prior emitted count) :
    ∀ dest off array, l.put = .ref dest off → Space.get h dest = some array →
      writtenBytes array off emitted.length = emitted := by
  obtain ⟨dest, off, array, pointer, get, _start, _bound, values⟩ := ledger.physical
  intro next index bytes nextPointer nextGet
  have same := pointer.symm.trans nextPointer
  cases same
  have sameArray := Option.some.inj (get.symm.trans nextGet)
  cases sameArray
  exact values

/-- A chosen actual fast observation produces every phase-free post-call
fact, even when BAD follows an already emitted prefix. No final source
phase or desired output is an input to this constructor. -/
theorem EpochCallCut4.fast_observation_facts
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    {L D : List Nat} {dict : List UInt8}
    (epoch : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (full : FastCommittedCallCutV8 c h r zs z s l (raw.drop epoch.facts.used)
      L D dict base.output epoch.facts.emitted)
    (observation : Observation full.cut.p full.cut.loopHeap full.cut.result)
    (source : WordSource observation)
    (mode : s.mode = LEN)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ facts : CallFacts c entryHeap full.cut.loadedHeap r zs entryZ full.cut.zNext
        full.cut.loadedState full.cut.loaded base raw,
      facts.used = epoch.facts.used + full.cut.used ∧ facts.emitted = observation.history ∧
      facts.word = epoch.facts.word ++ observation.word := by
  let cut := full.cut
  obtain ⟨trip, streamEq, stateEq, usedEq, madeEq⟩ := epoch.fast_trip cut mode fast
  have lower : TYPE ≤ s.mode := by rw [mode]; decide
  have active : s.mode < CHECK := by rw [mode]; decide
  have ledger := epoch.facts.payload_credit_zero lower active
  have restoredLedger : OutputCredit cut.restored (leaveStream z l) (leaveState s l) l
      base.output epoch.facts.emitted 0 := by
    rw [cut.restoreShape]
    exact ledger.restore
  obtain ⟨more, history, outputLedger⟩ := full.observation_credit observation restoredLedger epoch.facts.buffers.output.count
  obtain ⟨_more, moreLength, _moreBytes, sameHistory⟩ := full.observationSegment observation
  have equalMore : more = _more := List.append_cancel_left (history.symm.trans sameHistory)
  have length : observation.history.length = epoch.facts.emitted.length + cut.made := by
    rw [history, List.length_append, equalMore, moreLength]
  have sourceStep := cut.observation_source observation source
  have credited := epoch.facts.credited.append sourceStep
  have credit : CausalInput.Credited (base.input ++ raw.take (epoch.facts.used + cut.used))
      (epoch.facts.word ++ observation.word) cut.loaded.bits cut.loaded.hold := by
    simpa only [List.take_add, List.append_assoc] using credited
  have frame := cut.fullState
  change cut.loadedState = {s with mode := cut.loadedState.mode, hold := cut.loadedState.hold, bits := cut.loadedState.bits, back := cut.loadedState.back} at frame
  have window : cut.loadedState.window = s.window := by rw [frame]
  have size : cut.loadedState.wsize = s.wsize := by rw [frame]
  have count : cut.loadedState.whave = s.whave := by rw [frame]
  have nextWindow : cut.loadedState.wnext = s.wnext := by rw [frame]
  have wbits : cut.loadedState.wbits = s.wbits := by rw [frame]
  have stored := dictionary_caller_output_frame epoch.facts.origin.good epoch.facts.buffers.output.range
    trip.outputFrame window size count nextWindow (epoch.facts.window active)
  have modeFamily : cut.loadedState.mode = LEN ∨ cut.loadedState.mode = TYPE ∨ cut.loadedState.mode = BAD := by
    rcases cut.loaded_mode_cases with ⟨_normal, _source, current⟩ | ⟨_eob, _source, current⟩ | ⟨_bad, _source, current⟩
    · exact Or.inl (current.trans mode)
    · exact Or.inr (Or.inl current)
    · exact Or.inr (Or.inr current)
  have origins : WrapperOrigins cut.loadedState := by
    refine ⟨cut.sWrap.trans epoch.facts.wrapperOrigins.wrapped, ?_, ?_⟩
    · intro early
      rcases modeFamily with a | a | a <;> rcases early with b | b <;> rw [a] at b <;> contradiction
    · intro early
      rcases modeFamily with a | a | a <;> rcases early with b | b | b <;> rw [a] at b <;> contradiction
  have counters := trip.counters (Or.inr (Or.inl mode))
  have inputBase : cut.loaded.in_ = entryZ.avail_in :=
    cut.loadedIn.trans epoch.facts.registers.inputStart
  have noHeader : (cut.loadedState.mode = HEAD ∨ cut.loadedState.mode = DICTID ∨ cut.loadedState.mode = DICT) →
      cut.loaded.out_ = cut.loaded.left := by
    intro early
    rcases modeFamily with a | a | a <;> rcases early with b | b | b <;> rw [a] at b <;> contradiction
  have origin : DefaultOriginState cut.loadedHeap r zs cut.zNext cut.loadedState :=
    epoch.facts.origin.of_fields cut.finalJ cut.sFlags cut.sLenCode cut.sDistCode
  have publicLedger := trip.public_ledgers
  rw [usedEq, madeEq] at publicLedger
  refine ⟨{
    used := epoch.facts.used + cut.used
    usedBound := publicLedger.1
    emitted := observation.history
    word := epoch.facts.word ++ observation.word
    env := ⟨epoch.facts.env.strm, epoch.facts.env.st, cut.finalJ.good.live.hz, cut.finalJ.good.live.hs⟩
    origin := origin
    allocator := by rw [← streamEq]; exact trip.allocator
    wrapperOrigins := origins
    main := epoch.facts.advance_main
      ⟨epoch.facts.env.strm, epoch.facts.env.st, cut.finalJ.good.live.hz, cut.finalJ.good.live.hs⟩
      origin (by simpa only [List.drop_drop] using cut.loadedBuffers) (by change cut.loaded.bits.toNat ≤ 39; have := cut.bitsSmall; omega)
      (cut.dispatch_run epoch.facts.env mode fast)
    buffers := by simpa only [List.drop_drop] using cut.loadedBuffers
    bits := by change cut.loaded.bits.toNat ≤ 39; have := cut.bitsSmall; omega
    next := publicLedger.2.1
    haveCount := publicLedger.2.2.1
    put := by rw [length]; exact publicLedger.2.2.2.1
    leftCount := by rw [length]; exact publicLedger.2.2.2.2
    credited := credit
    window := by
      intro _
      change InflateDictionary cut.loadedHeap cut.loadedState ((base.dictionary ++ base.output).drop ((base.dictionary ++ base.output).length - 2 ^ cut.loadedState.wbits.toNat))
      rw [wbits]
      exact stored
    physical := WholeEpoch.OutputCredit.observed_bytes outputLedger
    checksum := fun _ _ => ⟨0, outputLedger⟩
    registers := ⟨inputBase, noHeader⟩
    outputStart := fun _ => cut.loadedOut.trans (epoch.facts.outputStart active)
    normalRet := fun _ => cut.loadedRet.trans (epoch.facts.normalRet (by rw [mode]; decide))
    allocationOracle := cut.allocOracle.trans epoch.facts.allocationOracle
  }, rfl, rfl, rfl⟩

#print axioms OutputCredit.observed_bytes
#print axioms EpochCallCut4.fast_observation_facts
end Zlib.Inflate.Proofs.WholeEpoch
