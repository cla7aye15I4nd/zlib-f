import ZlibF.Proof.«inflate.c.whole-slow-dispatch-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-matching-copy-math-v1»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken SlowArbitrarySource FunctionalTrailer
open ZlibF.Math.LZ77Copy ZlibF.Math.LZ77History
set_option autoImplicit false
set_option maxRecDepth 4096

/-- A pending emitted copy resumes its original accepted token. The
physical saved window supplies the remaining bytes; no remainder is
parsed as a fresh token or credited before it is emitted. -/
 theorem EpochCallCut4.matching_slow_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : (leaveState s l).mode = MATCH)
    (data : Matching (sourceLog (callLog base raw before.facts.used before.facts.emitted)) (leaveState s l) before.facts.word)
    (selected : before.phase = .legacy (.matching mode data)) :
    Nonempty (DispatchResult4 before) := by
  by_cases empty : l.left = 0
  · exact before.payload_output_wait (Or.inl mode) empty
  have attached := before.materialized
  rw [selected] at attached
  change TableBinding h s data.boundary.L data.boundary.D ∧ True at attached
  have dataMode : DataTableMode s.mode := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode)))))
  have actualMode : s.mode = MATCH := mode
  have noFast : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
    rintro (chosen | chosen) <;> rw [actualMode] at chosen <;> cases chosen
  obtain ⟨view, _queries⟩ := before.facts.slow_payload_view data.boundary.block.wrapper attached.1 dataMode
  have pending := before.facts.origin.pending.matching mode
  have originalFit := data.scalar_copy_fields.2.1
  have historyBound := data.emitted.length_le
  have distanceBound := data.token.distance_bounds.2
  have distanceField := data.registers.2.2.1
  have formatBound : s.offset.toNat ≤ 32768 := by
    change s.offset.toNat = _ at distanceField
    rw [distanceField]
    exact distanceBound
  have fullFit : s.offset.toNat ≤ (data.boundary.block.wrapper.dictionary ++ base.output ++ before.facts.emitted).length := by
    change s.offset.toNat ≤ (data.boundary.block.wrapper.dictionary ++ data.before).length at originalFit
    change data.before.length ≤ (base.output ++ before.facts.emitted).length at historyBound
    simp only [List.length_append] at originalFit historyBound ⊢
    omega
  have checks := window_distance_check_agrees data.boundary.block.wrapper.dictionary base.output before.facts.emitted 32768 s.offset.toNat formatBound
  have available : s.offset.toNat ≤ (retained data.boundary.block.wrapper.dictionary base.output).length + before.facts.emitted.length := by
    apply Nat.le_of_not_gt
    intro unavailable
    have tooFar : ((retained data.boundary.block.wrapper.dictionary base.output) ++ before.facts.emitted).length < s.offset.toNat := by
      simp only [List.length_append]; omega
    have fullTooFar := checks.mp tooFar
    omega
  rcases MATCH_current_source before.facts.env view.good view.tables view.dictionary view.buffers mode pending.1 pending.2.2.2 view.sane with wait | bad | emitted
  · exact (empty wait.1).elim
  · obtain ⟨_after, _stream, _state, unavailable, _rest⟩ := bad
    have oldCount := view.count
    have available' : s.offset.toNat ≤ (retained data.boundary.block.wrapper.dictionary base.output).length + (l.out_.toNat - l.left.toNat) := by omega
    exact (unavailable available').elim
  · obtain ⟨amount, dest, off, oldArray, regs, after, array, _fit, put, oldGet, matchRun,
      positive, _room, amountBound, good, _tables, _buffers, _dictionary, get, _size, _ro,
      _decodeFrame, regFrame, remain, modes, left, cursor, _stream, _static, _bits, bytes, _heap⟩ := emitted
    have actual := (inflate_dispatch_MATCH before.facts.env l mode).trans matchRun
    obtain ⟨trip, frame, afterTables, _in, _out, _ret, _oracle⟩ := before.facts.payload_slow_trip_observe dataMode noFast attached.1 actual
    have stateEq : trip.state = matchEmitState s amount := Option.some.inj (trip.origin.good.live.hs.symm.trans good.live.hs)
    have haveSame : regs.have_ = l.have_ := by rw [regFrame]
    have usedZero : trip.used = 0 := by have count := trip.haveCount; rw [haveSame] at count; omega
    have madeEq : trip.made = amount.toNat := by have count := trip.leftCount; omega
    have outSame : regs.out_ = l.out_ := by rw [regFrame]
    have actualCount : regs.out_.toNat - regs.left.toNat = l.out_.toNat - l.left.toNat + amount.toNat := by
      have oldCount := before.facts.buffers.output.count
      rw [outSame]
      omega
    rw [view.written dest off oldArray put oldGet] at bytes
    have physicalCopy : writtenBytes array (off + amount.toNat) (regs.out_.toNat - regs.left.toNat) =
        copyBack (retained data.boundary.block.wrapper.dictionary base.output) s.offset.toNat amount.toNat before.facts.emitted := by
      rw [actualCount]
      exact bytes
    obtain ⟨more, moreLength, output, physical, _fresh⟩ := trip.slow_output_ledger dataMode noFast
    have observed := OutputCredit.observed_unique output trip.buffers cursor get physicalCopy
    have agreement := retained_history_agrees data.boundary.block.wrapper.dictionary base.output before.facts.emitted
      (retained data.boundary.block.wrapper.dictionary base.output) s.offset.toNat amount.toNat
      (List.drop_suffix _ _) pending.2.2.2 available
    have logicalNew : base.output ++ (before.facts.emitted ++ more) =
        copyBack data.boundary.block.wrapper.dictionary s.offset.toNat amount.toNat (base.output ++ before.facts.emitted) := by
      rw [observed]
      exact agreement.symm
    obtain ⟨_effect, historyPrefix, fullPrefix, _length, debt⟩ := data.copy_advance amount.toNat amountBound
    change (base.output ++ before.facts.emitted) <+:
      copyBack data.boundary.block.wrapper.dictionary s.offset.toNat amount.toNat (base.output ++ before.facts.emitted) at historyPrefix
    change copyBack data.boundary.block.wrapper.dictionary s.offset.toNat amount.toNat (base.output ++ before.facts.emitted) <+: data.fullOutput at fullPrefix
    change data.fullOutput.length - (copyBack data.boundary.block.wrapper.dictionary s.offset.toNat amount.toNat
      (base.output ++ before.facts.emitted)).length = s.length.toNat - amount.toNat at debt
    rw [← logicalNew] at historyPrefix fullPrefix debt
    have modes' : trip.state.mode = LEN ∨ trip.state.mode = MATCH := by rw [stateEq]; exact modes
    have remaining : trip.state.length.toNat = s.length.toNat - amount.toNat := by rw [stateEq]; exact remain
    have heldSame : held (leaveState trip.state regs) = held (leaveState s l) := by
      change natBits regs.bits.toNat regs.hold.toNat = natBits l.bits.toNat l.hold.toNat
      rw [regFrame]
    have lastSame : (leaveState trip.state regs).last = (leaveState s l).last := by
      change trip.state.last = s.last
      rw [frame]
    have wasSame : trip.state.was = s.was := by rw [stateEq]; dsimp only [matchEmitState]; split <;> rfl
    have offsetSame : trip.state.offset = s.offset := by rw [stateEq]; dsimp only [matchEmitState]; split <;> rfl
    have backSame : trip.state.back = s.back := by rw [stateEq]; dsimp only [matchEmitState]; split <;> rfl
    have oldRegisters := copy_registers_unlocals data.registers
    have registers : SlowReverseTokenRegisters.CopyRegisters data.token (leaveState trip.state regs) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change trip.state.was.toNat = _
        rw [wasSame]; exact oldRegisters.1
      · change trip.state.length.toNat ≤ trip.state.was.toNat
        rw [remaining, wasSame]
        have old := oldRegisters.2.1
        omega
      · change trip.state.offset.toNat = _
        rw [offsetSame]; exact oldRegisters.2.2.1
      · change trip.state.back = _
        rw [backSame]; exact oldRegisters.2.2.2
    have savedTables : TableBinding after (leaveState trip.state regs) data.boundary.L data.boundary.D := afterTables
    have credit : CausalInput.Credited (base.input ++ raw.take (before.facts.used + trip.used))
        before.facts.word regs.bits regs.hold := by
      rw [usedZero, Nat.add_zero, regFrame]
      exact before.facts.credited
    have phase : Nonempty (Attached4 after
        (sourceLog (callLog base raw (before.facts.used + trip.used) (before.facts.emitted ++ more)))
        (leaveState trip.state regs) before.facts.word) := by
      rcases modes' with len | matching
      · have completed : amount.toNat = s.length.toNat :=
          (SlowReverseTokenComplete.matchEmit_completed actualMode amountBound).mp (by rw [← stateEq]; exact len)
        have equalLength : (base.output ++ (before.facts.emitted ++ more)).length = data.fullOutput.length := by
          have upper := fullPrefix.length_le
          rw [completed] at debt
          omega
        have full : base.output ++ (before.facts.emitted ++ more) = data.fullOutput := by
          rw [List.prefix_iff_eq_take.mp fullPrefix, equalLength, List.take_length]
        have result := data.complete_attached savedTables heldSame lastSame len
        simpa only [sourceLog, callLog, usedZero, Nat.add_zero, ← full] using result
      · have result := data.emit_attached savedTables heldSame lastSame registers
          (data.emitted.trans historyPrefix) fullPrefix (by
            change data.fullOutput.length - (base.output ++ (before.facts.emitted ++ more)).length = trip.state.length.toNat
            rw [remaining]
            exact debt) matching
        simpa only [sourceLog, callLog, usedZero, Nat.add_zero] using result
    obtain ⟨next⟩ := phase
    have lower : TYPE ≤ trip.state.mode := by rcases modes' with len | matching <;> first | rw [len]; decide | rw [matching]; decide
    have notStored : (leaveState trip.state regs).mode ≠ STORED := by
      change trip.state.mode ≠ STORED
      rcases modes' with len | matching <;> first | rw [len]; decide | rw [matching]; decide
    exact ⟨slow_dispatch_result before trip dataMode noFast lower (before.facts.emitted ++ more) before.facts.word
      (by simp only [List.length_append, moreLength]) credit physical output next.phase next.materialized
      (fun _ _ => next.phase.saved_of_not_stored notStored)⟩

#print axioms EpochCallCut4.matching_slow_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
