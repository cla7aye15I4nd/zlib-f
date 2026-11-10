import ZlibF.Proof.«inflate.c.whole-slow-source-packet»
import ZlibF.Proof.«inflate.c.whole-slow-facts-next»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken SlowRejectedToken FunctionalTrailer
set_option autoImplicit false

def retained (dictionary past : List UInt8) : List UInt8 :=
  (dictionary ++ past).drop ((dictionary ++ past).length - 32768)

/-- One complete source-generated slow dispatch and its exact structural,
physical, retained-history and rejected-source observations. -/
structure SlowTripSource {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (wrapper : Wrapper base.dictionary) (L D : List Nat) (prior : List Bool) where
  outcome : Except Ex Unit
  regs : IL
  after : Heap
  trip : PayloadTrip4 before after regs outcome
  frame : DecodeStateFrame s trip.state
  tables : TableBinding after trip.state L D
  event : SlowReverseTokenComplete.TokenEvent L D (retained wrapper.dictionary base.output) before.emitted
    (prior ++ stream l (raw.drop before.used)) r zs outcome regs after trip.stream trip.state (raw.drop (before.used + trip.used))
  bad : trip.state.mode = BAD → BadSource L D (retained wrapper.dictionary base.output) before.emitted
    (prior ++ stream l (raw.drop before.used)) regs (raw.drop (before.used + trip.used))
  more : List UInt8
  moreLength : more.length = trip.made
  output : OutputCredit after trip.stream trip.state regs base.output (before.emitted ++ more) 0
  physical : ∀ dest off array, regs.put = .ref dest off → Space.get after dest = some array →
    ZlibF.Math.LZ77Copy.writtenBytes array off (before.emitted ++ more).length = before.emitted ++ more

 theorem CallFacts.ready_slow_source
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {L D : List Nat}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (wrapper : Wrapper base.dictionary) (tables : TableBinding h s L D)
    (mode : s.mode = LEN_ ∨ s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Nonempty (SlowTripSource before wrapper L D []) := by
  have dataMode : DataTableMode s.mode := mode.elim Or.inl (fun len => Or.inr (Or.inl len))
  have noFast : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := fun _ => slow
  obtain ⟨view, queries⟩ := before.slow_payload_view wrapper tables dataMode
  obtain ⟨outcome, regs, after, streamZ, state, used, actual, bound, B, cursor, count, event⟩ :=
    SlowReverseTokenComplete.slow_token_dispatch_event before.env view mode slow
  obtain ⟨trip, frame, afterTables, _in, _out, _ret, _oracle⟩ := before.payload_slow_trip_observe dataMode noFast tables actual
  have good := ordinary_event_good event.forget
  have stateEq : state = trip.state := Option.some.inj (good.live.hs.symm.trans trip.origin.good.live.hs)
  have streamEq : streamZ = trip.stream := Option.some.inj (good.live.hz.symm.trans trip.origin.good.live.hz)
  have usedEq : used = trip.used := by have current := trip.haveCount; omega
  rw [stateEq, streamEq, usedEq] at event
  have rejected := (slow_token_outcome before.env view queries mode slow).bad_of_run actual trip.origin.good trip.haveCount
  obtain ⟨more, moreLength, output, physical, _fresh⟩ := trip.slow_output_ledger dataMode noFast
  refine ⟨⟨outcome, regs, after, trip, frame, afterTables, ?_, ?_, more, moreLength, output, physical⟩⟩
  · simpa only [retained, List.nil_append, List.drop_drop] using event
  · simpa only [retained, List.nil_append, List.drop_drop] using rejected

 theorem CallFacts.reading_slow_source
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {L D : List Nat} {prior : List Bool}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (wrapper : Wrapper base.dictionary) (tables : TableBinding h s L D)
    (phase : ReadPrefix L D (prior ++ stream l (raw.drop before.used)) s (stream l (raw.drop before.used)))
    (modes : s.mode = LENEXT ∨ s.mode = DIST ∨ s.mode = DISTEXT ∨ s.mode = LIT) :
    Nonempty (SlowTripSource before wrapper L D prior) := by
  have dataMode : DataTableMode s.mode := by
    rcases modes with le | dist | de | lit
    · exact Or.inr (Or.inr (Or.inl le))
    · exact Or.inr (Or.inr (Or.inr (Or.inl dist)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl de))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr lit)))))
  have noFast : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
    intro selected
    rcases modes with m | m | m | m <;> rcases selected with selected | selected <;> rw [m] at selected <;> cases selected
  obtain ⟨view, queries⟩ := before.slow_payload_view wrapper tables dataMode
  obtain ⟨outcome, regs, after, streamZ, state, used, actual, bound, B, cursor, count, event⟩ :=
    reading_complete_event before.env view phase rfl modes
  obtain ⟨trip, frame, afterTables, _in, _out, _ret, _oracle⟩ := before.payload_slow_trip_observe dataMode noFast tables actual
  have good := ordinary_event_good event.forget
  have stateEq : state = trip.state := Option.some.inj (good.live.hs.symm.trans trip.origin.good.live.hs)
  have streamEq : streamZ = trip.stream := Option.some.inj (good.live.hz.symm.trans trip.origin.good.live.hz)
  have usedEq : used = trip.used := by have current := trip.haveCount; omega
  rw [stateEq, streamEq, usedEq] at event
  have rejected := (pending_token_outcome before.env view queries phase rfl (fun selected => noFast (Or.inr selected))).bad_of_run actual trip.origin.good trip.haveCount
  obtain ⟨more, moreLength, output, physical, _fresh⟩ := trip.slow_output_ledger dataMode noFast
  refine ⟨⟨outcome, regs, after, trip, frame, afterTables, ?_, ?_, more, moreLength, output, physical⟩⟩
  · simpa only [retained, List.drop_drop] using event
  · simpa only [retained, List.drop_drop] using rejected

#print axioms CallFacts.ready_slow_source
#print axioms CallFacts.reading_slow_source
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken SlowRejectedToken FunctionalTrailer
set_option autoImplicit false

 theorem CallFacts.unchecked_slow_source
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {L D : List Nat} {prior : List Bool}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (wrapper : Wrapper base.dictionary) (tables : TableBinding h s L D) (p : CopySyntax L D)
    (input : p.input = prior ++ natBits l.bits.toNat l.hold.toNat)
    (rest : p.rest = natBits l.bits.toNat l.hold.toNat)
    (registers : SlowReverseTokenRegisters.CopyRegisters p s) (untouched : s.length = s.was) (mode : s.mode = MATCH) :
    Nonempty (SlowTripSource before wrapper L D prior) := by
  have dataMode : DataTableMode s.mode := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode)))))
  have noFast : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
    rintro (selected | selected) <;> rw [mode] at selected <;> cases selected
  obtain ⟨view, queries⟩ := before.slow_payload_view wrapper tables dataMode
  let q := append_copy_syntax p view.semantic.acceptable.1 view.semantic.acceptable.2 (bytesBits (raw.drop before.used))
  have qInput : q.input = prior ++ stream l (raw.drop before.used) := by
    simp only [q, append_copy_syntax, input, stream, List.append_assoc]
  have qRest : q.rest = stream l (raw.drop before.used) := by simp only [q, append_copy_syntax, rest, stream]
  have length : s.length.toNat = lengthBases.getD (q.symbol - 257) 0 + q.lengthValue := by
    rw [untouched]; exact registers.1
  have source := SlowReverseTokenComplete.MATCH_dispatch_event q before.env view mode length untouched.symm
    registers.2.2.1 qRest registers.2.2.2
  rw [qInput] at source
  obtain ⟨outcome, regs, after, streamZ, state, used, actual, bound, B, cursor, count, event⟩ := source
  obtain ⟨trip, frame, afterTables, _in, _out, _ret, _oracle⟩ := before.payload_slow_trip_observe dataMode noFast tables actual
  have good := ordinary_event_good event.forget
  have stateEq : state = trip.state := Option.some.inj (good.live.hs.symm.trans trip.origin.good.live.hs)
  have streamEq : streamZ = trip.stream := Option.some.inj (good.live.hz.symm.trans trip.origin.good.live.hz)
  have usedEq : used = trip.used := by have current := trip.haveCount; omega
  rw [stateEq, streamEq, usedEq] at event
  have observed := MATCH_outcome q before.env view mode length untouched.symm registers.2.2.1 qRest
  rw [qInput] at observed
  have rejected := observed.bad_of_run actual trip.origin.good trip.haveCount
  obtain ⟨more, moreLength, output, physical, _fresh⟩ := trip.slow_output_ledger dataMode noFast
  refine ⟨⟨outcome, regs, after, trip, frame, afterTables, ?_, ?_, more, moreLength, output, physical⟩⟩
  · simpa only [retained, List.drop_drop] using event
  · simpa only [retained, List.drop_drop] using rejected

#print axioms CallFacts.unchecked_slow_source
end Zlib.Inflate.Proofs.WholeEpoch
