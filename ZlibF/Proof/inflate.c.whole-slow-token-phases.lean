import ZlibF.Proof.«inflate.c.whole-epoch-source-spine-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-ready-payload»
import ZlibF.Proof.«inflate.c.whole-epoch-block-transitions»
import ZlibF.Proof.«inflate.c.slow-reverse-token-complete»
import ZlibF.Proof.«inflate.c.slow-bad-outcome»
import ZlibF.Math.«whole-epoch-compressed-rejection-v1»
import ZlibF.Proof.«inflate.c.token-retained-history-transport»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
open ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false

 theorem read_prefix_locals {L D : List Nat} {input residual : List Bool} {s : InflateState}
    (phase : ReadPrefix L D input s residual) (l : IL) : ReadPrefix L D input (leaveState s l) residual := by
  cases phase with
  | code mode => exact .code mode
  | literal decoded small mode length back => exact .literal decoded small mode length back
  | lenext decoded lower upper mode length extra back => exact .lenext decoded lower upper mode length extra back
  | dist decoded lower upper read mode length was back => exact .dist decoded lower upper read mode length was back
  | distext decoded lower upper read distanceDecoded distanceUpper mode length was offset extra back =>
    exact .distext decoded lower upper read distanceDecoded distanceUpper mode length was offset extra back
  | matching p inputEq mode length was distance => exact .matching p inputEq mode length was distance

 theorem copy_registers_locals {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    (registers : SlowReverseTokenRegisters.CopyRegisters p s) (l : IL) :
    SlowReverseTokenRegisters.CopyRegisters p (leaveState s l) := registers

/-- An emitted non-EOB token advances the exact committed finite word. -/
 theorem Compressed.advance {dictionary history next : List UInt8} {wire input rest : List Bool}
    (boundary : Compressed dictionary wire history)
    (step : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary history input rest next false) :
    ∃ word, input = word ++ rest ∧ ∃ after : Compressed dictionary (wire ++ word) next, after.block = boundary.block ∧ after.L = boundary.L ∧ after.D = boundary.D := by
  obtain ⟨word, source, committed⟩ := boundary.committed.advance boundary.validL boundary.validD step
  refine ⟨word, source, ⟨boundary.block, boundary.L, boundary.D, boundary.headerWord, boundary.header,
    boundary.validL, boundary.validD, boundary.tokenWord ++ word, committed, ?_⟩, rfl, rfl, rfl⟩
  simpa only [List.append_assoc] using congrArg (fun prior => prior ++ word) boundary.anchor

/-- A genuine accepted partial read becomes a Reading phase at precisely
its consumed word. No future completion is introduced. -/
 theorem Compressed.reading_phase {log : DataLog} {s : InflateState} {wire input : List Bool}
    (boundary : Compressed log.dictionary wire log.output)
    (phase : ReadPrefix boundary.L boundary.D input s (held s))
    (modes : s.mode = LENEXT ∨ s.mode = DIST ∨ s.mode = DISTEXT ∨ s.mode = LIT)
    (last : s.last = Int32.ofNat boundary.block.last) :
    ∃ word, input = word ++ held s ∧ Nonempty (SourcePhase log s (wire ++ word)) := by
  obtain ⟨word, source, parsed⟩ := phase.consumed_word boundary.validL boundary.validD
  exact ⟨word, source, ⟨.reading modes ⟨wire, boundary, word, rfl, last, parsed (held s)⟩⟩⟩

/-- An accepted copy with a real output prefix remains attached to its
original complete token while MATCH is pending. Its logical history is
advanced only after all output has physically been emitted. -/
 theorem Compressed.matching_phase {log : DataLog} {s : InflateState} {wire : List Bool} {before fullOutput : List UInt8}
    (boundary : Compressed log.dictionary wire before) (p : CopySyntax boundary.L boundary.D)
    (rest : p.rest = held s) (last : s.last = Int32.ofNat boundary.block.last)
    (registers : SlowReverseTokenRegisters.CopyRegisters p s)
    (step : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary before p.input p.rest fullOutput false)
    (beforePrefix : before <+: log.output) (effectPrefix : log.output <+: fullOutput)
    (debt : fullOutput.length - log.output.length = s.length.toNat) (mode : s.mode = MATCH) :
    ∃ word, p.input = word ++ held s ∧ Nonempty (SourcePhase log s (wire ++ word)) := by
  obtain ⟨word, source, _replay⟩ := ZlibF.Math.TokenSuffix.step_consumed_word boundary.validL boundary.validD step
  refine ⟨word, by simpa only [rest] using source, ⟨.matching mode ?_⟩⟩
  exact ⟨wire, before, boundary, word, p, by simpa only [rest] using source, rest, last, registers,
    fullOutput, by simpa only [source, rest] using step, beforePrefix, effectPrefix, debt, rfl⟩

#print axioms read_prefix_locals
#print axioms copy_registers_locals
#print axioms Compressed.advance
#print axioms Compressed.reading_phase
#print axioms Compressed.matching_phase
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

 theorem source_update_credit
    {received raw : List UInt8} {before pending consumed : List Bool} {l regs : IL} {used : Nat}
    (credit : CausalInput.Credited received (before ++ pending) l.bits l.hold)
    (source : (pending ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (raw.take used) =
      consumed ++ natBits regs.bits.toNat regs.hold.toNat) :
    CausalInput.Credited (received ++ raw.take used) (before ++ consumed) regs.bits regs.hold := by
  unfold CausalInput.Credited at credit ⊢
  rw [bytesBits_append, credit]
  simpa only [List.append_assoc] using congrArg (fun bits => before ++ bits) source

 theorem EpochCallCut.source_update_credit
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {before pending consumed : List Bool} {used : Nat}
    (epoch : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (word : epoch.framed.cut.word = before ++ pending)
    (source : (pending ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits ((raw.drop epoch.framed.cut.used).take used) =
      consumed ++ natBits regs.bits.toNat regs.hold.toNat) :
    CausalInput.Credited (base.input ++ raw.take (epoch.framed.cut.used + used))
      (before ++ consumed) regs.bits regs.hold := by
  have credit := epoch.framed.cut.credited
  rw [word] at credit
  have next := WholeEpoch.source_update_credit credit source
  simpa only [List.take_add, List.append_assoc] using next

 theorem Compressed.complete_token_phase {log : DataLog} {s : InflateState} {wire input : List Bool} {before : List UInt8}
    (boundary : Compressed log.dictionary wire before)
    (step : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary before input (held s) log.output false)
    (mode : s.mode = LEN) (last : s.last = Int32.ofNat boundary.block.last) :
    ∃ word, input = word ++ held s ∧ Nonempty (SourcePhase log s (wire ++ word)) := by
  obtain ⟨word, source, next, block, _lengths, _distances⟩ := boundary.advance step
  exact ⟨word, source, ⟨.ready next (Or.inr mode) (by rw [block]; exact last)⟩⟩

/-- The original held remainder is unchanged during a partial copy. Only
actual emission changes the pending output prefix and remaining debt. -/
 theorem Matching.emit_phase
    {log : DataLog} {s state : InflateState} {wire : List Bool} {output : List UInt8}
    (before : Matching log s wire) (source : held state = held s)
    (last : state.last = s.last)
    (registers : SlowReverseTokenRegisters.CopyRegisters before.token state)
    (historyPrefix : before.before <+: output) (effect : output <+: before.fullOutput)
    (debt : before.fullOutput.length - output.length = state.length.toNat)
    (mode : state.mode = MATCH) :
    Nonempty (SourcePhase {log with output := output} state wire) := by
  refine ⟨.matching mode ?_⟩
  refine ⟨before.beforeWire, before.before, before.boundary, before.pendingWord, before.token,
    ?_, ?_, last.trans before.last, registers, before.fullOutput, ?_, historyPrefix, effect, debt, before.anchor⟩
  · rw [source]; exact before.input
  · rw [source]; exact before.rest
  · rw [source]; exact before.accepted

 theorem Matching.complete_phase
    {log : DataLog} {s state : InflateState} {wire : List Bool}
    (before : Matching log s wire) (source : held state = held s)
    (last : state.last = s.last) (mode : state.mode = LEN) :
    Nonempty (SourcePhase {log with output := before.fullOutput} state wire) := by
  have accepted : Token.Step before.boundary.L before.boundary.D before.boundary.block.wrapper.dictionary
      before.before (before.pendingWord ++ held state) (held state) before.fullOutput false := by
    rw [source]; exact before.accepted
  obtain ⟨word, read, next, block, _lengths, _distances⟩ := before.boundary.advance accepted
  have same : word = before.pendingWord := List.append_cancel_right read.symm
  subst word
  have phase : SourcePhase {log with output := before.fullOutput} state (before.beforeWire ++ before.pendingWord) :=
    .ready next (Or.inr mode) (by rw [block]; exact last.trans before.last)
  rw [← before.anchor] at phase
  exact ⟨phase⟩

#print axioms source_update_credit
#print axioms EpochCallCut.source_update_credit
#print axioms Compressed.complete_token_phase
#print axioms Matching.emit_phase
#print axioms Matching.complete_phase
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

/-- Zero output can leave MATCH before distance checking. This phase
records the accepted reads without inventing an accepted copy effect. -/
 theorem Compressed.unchecked_match_phase {log : DataLog} {s : InflateState} {wire : List Bool}
    (boundary : Compressed log.dictionary wire log.output) (p : CopySyntax boundary.L boundary.D)
    (rest : p.rest = held s) (last : s.last = Int32.ofNat boundary.block.last)
    (registers : SlowReverseTokenRegisters.CopyRegisters p s) (untouched : s.length = s.was) (mode : s.mode = MATCH) :
    ∃ word, p.input = word ++ held s ∧ Nonempty (SourcePhase4 log s (wire ++ word)) := by
  have parsed : ReadPrefix boundary.L boundary.D p.input s p.rest :=
    .matching p rfl mode (by rw [untouched]; exact registers.1) untouched.symm registers.2.2.1
  obtain ⟨word, source, replay⟩ := parsed.consumed_word boundary.validL boundary.validD
  refine ⟨word, by simpa only [rest] using source, ⟨.uncheckedMatch mode ?_⟩⟩
  let reading : Reading log s (wire ++ word) :=
    ⟨wire, boundary, word, rfl, last, replay (held s)⟩
  exact ⟨reading, p, by simpa only [reading, rest] using source, rest, registers, untouched⟩

#print axioms Compressed.unchecked_match_phase
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

 theorem read_prefix_unlocals {L D : List Nat} {input residual : List Bool} {s : InflateState} {l : IL}
    (phase : ReadPrefix L D input (leaveState s l) residual) : ReadPrefix L D input s residual := by
  cases phase with
  | code mode => exact .code mode
  | literal decoded small mode length back => exact .literal decoded small mode length back
  | lenext decoded lower upper mode length extra back => exact .lenext decoded lower upper mode length extra back
  | dist decoded lower upper read mode length was back => exact .dist decoded lower upper read mode length was back
  | distext decoded lower upper read distanceDecoded distanceUpper mode length was offset extra back =>
    exact .distext decoded lower upper read distanceDecoded distanceUpper mode length was offset extra back
  | matching p inputEq mode length was distance => exact .matching p inputEq mode length was distance

 theorem copy_registers_unlocals {L D : List Nat} {p : CopySyntax L D} {s : InflateState} {l : IL}
    (registers : SlowReverseTokenRegisters.CopyRegisters p (leaveState s l)) :
    SlowReverseTokenRegisters.CopyRegisters p s := registers

#print axioms read_prefix_unlocals
#print axioms copy_registers_unlocals
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

 theorem prior_step_held_prefix
    {L D : List Nat} {dict history target : List UInt8} {prior : List Bool} {l regs : IL}
    {bs : List UInt8} {used : Nat} {last : Bool}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (step : Token.Step L D dict history (prior ++ stream l bs) (stream regs (bs.drop used)) target last) :
    Token.Step L D dict history ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used))
      (natBits regs.bits.toNat regs.hold.toNat) target last := by
  apply ZlibF.Math.TokenSuffix.step_cancel_suffix lengths distances (suffix := bytesBits (bs.drop used))
  have before : ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used)) ++ bytesBits (bs.drop used) =
      prior ++ stream l bs := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    simp only [stream, List.append_assoc]
  rw [before]
  exact step

 theorem prior_read_held_prefix
    {L D : List Nat} {prior : List Bool} {l regs : IL} {bs : List UInt8} {used : Nat} {state : InflateState}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (phase : ReadPrefix L D (prior ++ stream l bs) state (stream regs (bs.drop used))) :
    ReadPrefix L D ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used)) state
      (natBits regs.bits.toNat regs.hold.toNat) := by
  apply ReadPrefix.cancel_suffix lengths distances (suffix := bytesBits (bs.drop used))
  have before : ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used)) ++ bytesBits (bs.drop used) =
      prior ++ stream l bs := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    simp only [stream, List.append_assoc]
  rw [before]
  exact phase

 theorem prior_event_held
    {L D : List Nat} {dict history : List UInt8} {prior : List Bool} {l regs : IL} {bs : List UInt8} {used : Nat}
    {r : ZStreamRef} {zs : Nat} {outcome : Except Ex Unit} {after : Heap} {z : ZStream} {state : InflateState}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (event : SlowReverseToken.TokenEvent L D dict history (prior ++ stream l bs) r zs outcome regs after z state (bs.drop used)) :
    CausalEvent L D dict history ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used)) outcome state regs := by
  cases event with
  | wait _view phase empty => exact Or.inl ⟨rfl, prior_read_held_prefix lengths distances phase, empty⟩
  | bad _good _B mode => exact Or.inr (Or.inl ⟨rfl, mode⟩)
  | literalPending _view _phase _mode step _length _small =>
    exact Or.inr (Or.inr ⟨rfl, _, false, prior_step_held_prefix lengths distances step⟩)
  | eob _view _mode _back step =>
    exact Or.inr (Or.inr ⟨rfl, _, true, prior_step_held_prefix lengths distances step⟩)
  | literalDone _good _buffers _mode _get _put _physical step =>
    exact Or.inr (Or.inr ⟨rfl, _, false, prior_step_held_prefix lengths distances step⟩)
  | copy _p _made _dest _off _array _inputEq residual _good _buffers _dictionary _positive _bound
      _length _mode _get _put _physical _count _remaining step =>
    rw [residual] at step
    exact Or.inr (Or.inr ⟨rfl, _, false, prior_step_held_prefix lengths distances step⟩)

#print axioms prior_step_held_prefix
#print axioms prior_read_held_prefix
#print axioms prior_event_held
end Zlib.Inflate.Proofs.WholeEpoch
