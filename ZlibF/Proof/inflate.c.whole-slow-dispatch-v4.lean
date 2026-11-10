import ZlibF.Proof.«inflate.c.whole-slow-event-phase»
import ZlibF.Proof.«inflate.c.whole-slow-output-wait»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken SlowRejectedToken FunctionalTrailer
set_option autoImplicit false

 theorem SlowTripSource.dispatch_result
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {wire prior : List Bool}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed base.dictionary wire (base.output ++ before.facts.emitted))
    (anchor : before.facts.word = wire ++ prior) (last : s.last = Int32.ofNat boundary.block.last)
    (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (source : SlowTripSource before.facts boundary.block.wrapper boundary.L boundary.D prior) :
    Nonempty (DispatchResult4 before) := by
  have event : SlowReverseTokenComplete.TokenEvent boundary.L boundary.D
      (retained boundary.block.wrapper.dictionary base.output) before.facts.emitted
      (prior ++ stream l (raw.drop before.facts.used)) r zs source.outcome source.regs source.after source.trip.stream source.trip.state
      ((raw.drop before.facts.used).drop source.trip.used) := by simpa only [List.drop_drop] using source.event
  have rejected : source.trip.state.mode = BAD → BadSource boundary.L boundary.D
      (retained boundary.block.wrapper.dictionary base.output) before.facts.emitted
      (prior ++ stream l (raw.drop before.facts.used)) source.regs ((raw.drop before.facts.used).drop source.trip.used) := by
    simpa only [List.drop_drop] using source.bad
  have buffers : DispatchBuffers source.after r source.regs ((raw.drop before.facts.used).drop source.trip.used) := by
    simpa only [List.drop_drop] using source.trip.buffers
  obtain ⟨word, wordSource, ⟨attached⟩⟩ := event_phase_attached before.facts boundary anchor last source.frame source.tables
    buffers source.output event rejected
  have oldCredit := before.facts.credited
  rw [anchor] at oldCredit
  have nextCredit := source_update_credit oldCredit wordSource
  have credit : CausalInput.Credited (base.input ++ raw.take (before.facts.used + source.trip.used))
      (wire ++ word) source.regs.bits source.regs.hold := by
    simpa only [List.take_add, List.append_assoc] using nextCredit
  have modes := complete_event_modes source.event
  exact ⟨slow_dispatch_result before source.trip mode slow modes.lower
    (before.facts.emitted ++ source.more) (wire ++ word)
    (by simp only [List.length_append, source.moreLength]) credit source.physical source.output
    attached.phase attached.materialized (fun _ _ => attached.phase.saved_of_not_stored modes.not_stored)⟩

/-- The actual slow LEN_/LEN branch produces the next finite epoch cut or
its genuine leave terminal, covering every arbitrary current input. -/
 theorem EpochCallCut4.ready_slow_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed (sourceLog (callLog base raw before.facts.used before.facts.emitted)).dictionary
      before.facts.word (sourceLog (callLog base raw before.facts.used before.facts.emitted)).output)
    (mode : (leaveState s l).mode = LEN_ ∨ (leaveState s l).mode = LEN)
    (last : (leaveState s l).last = Int32.ofNat boundary.block.last)
    (selected : before.phase = .legacy (.ready boundary mode last))
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Nonempty (DispatchResult4 before) := by
  have attached := before.materialized
  rw [selected] at attached
  change TableBinding h s boundary.L boundary.D ∧ True at attached
  have dataMode : DataTableMode s.mode := mode.elim Or.inl (fun len => Or.inr (Or.inl len))
  obtain ⟨source⟩ := before.facts.ready_slow_source boundary.block.wrapper attached.1 mode slow
  exact source.dispatch_result before boundary (by simp) last dataMode (fun _ => slow)

/-- Actual pending scalar reads and LIT retain their original pre-token
boundary and consumed-word anchor while advancing the same dispatch. -/
 theorem EpochCallCut4.reading_slow_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (modes : (leaveState s l).mode = LENEXT ∨ (leaveState s l).mode = DIST ∨ (leaveState s l).mode = DISTEXT ∨ (leaveState s l).mode = LIT)
    (data : Reading (sourceLog (callLog base raw before.facts.used before.facts.emitted)) (leaveState s l) before.facts.word)
    (selected : before.phase = .legacy (.reading modes data)) :
    Nonempty (DispatchResult4 before) := by
  have attached := before.materialized
  rw [selected] at attached
  change TableBinding h s data.boundary.L data.boundary.D ∧ True at attached
  have available := read_prefix_unlocals (data.available_phase l (raw.drop before.facts.used) rfl)
  obtain ⟨source⟩ := before.facts.reading_slow_source data.boundary.block.wrapper attached.1 available modes
  have mode : DataTableMode s.mode := by
    rcases modes with le | dist | de | lit
    · exact Or.inr (Or.inr (Or.inl le))
    · exact Or.inr (Or.inr (Or.inr (Or.inl dist)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl de))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr lit)))))
  have noFast : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
    intro chosen
    rcases modes with m | m | m | m <;> change s.mode = _ at m <;> rcases chosen with chosen | chosen <;> rw [m] at chosen <;> cases chosen
  exact source.dispatch_result before data.boundary data.anchor data.last mode noFast

/-- A fully parsed unchecked copy resumes the real MATCH guard. An
unavailable distance yields actual BAD rather than a fictitious accepted
copy; positive available output starts its original pending effect. -/
 theorem EpochCallCut4.unchecked_match_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : (leaveState s l).mode = MATCH)
    (data : UncheckedMatching (sourceLog (callLog base raw before.facts.used before.facts.emitted)) (leaveState s l) before.facts.word)
    (selected : before.phase = .uncheckedMatch mode data) :
    Nonempty (DispatchResult4 before) := by
  have attached := before.materialized
  rw [selected] at attached
  change TableBinding h s data.reading.boundary.L data.reading.boundary.D at attached
  obtain ⟨source⟩ := before.facts.unchecked_slow_source data.reading.boundary.block.wrapper attached data.token
    data.input data.rest (copy_registers_unlocals data.registers) data.untouched mode
  have dataMode : DataTableMode s.mode := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode)))))
  have noFast : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
    have actualMode : s.mode = MATCH := mode
    rintro (chosen | chosen) <;> rw [actualMode] at chosen <;> cases chosen
  exact source.dispatch_result before data.reading.boundary data.reading.anchor data.reading.last dataMode noFast

#print axioms SlowTripSource.dispatch_result
#print axioms EpochCallCut4.ready_slow_dispatch
#print axioms EpochCallCut4.reading_slow_dispatch
#print axioms EpochCallCut4.unchecked_match_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
