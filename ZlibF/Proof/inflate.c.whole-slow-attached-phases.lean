import ZlibF.Proof.«inflate.c.whole-slow-event-helpers»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

structure Attached4 (h : Heap) (log : DataLog) (s : InflateState) (wire : List Bool) where
  phase : SourcePhase4 log s wire
  materialized : phase.Materialized h

 theorem Compressed.complete_attached
    {h : Heap} {log : DataLog} {s : InflateState} {wire input : List Bool} {before : List UInt8}
    (boundary : Compressed log.dictionary wire before)
    (tables : TableBinding h s boundary.L boundary.D)
    (step : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary before input (held s) log.output false)
    (mode : s.mode = LEN) (last : s.last = Int32.ofNat boundary.block.last) :
    ∃ word, input = word ++ held s ∧ Nonempty (Attached4 h log s (wire ++ word)) := by
  obtain ⟨word, source, next, block, lengths, distances⟩ := boundary.advance step
  have nextTables : TableBinding h s next.L next.D := by rw [lengths, distances]; exact tables
  exact ⟨word, source, ⟨.legacy (.ready next (Or.inr mode) (by rw [block]; exact last)), nextTables, True.intro⟩⟩

 theorem Compressed.reading_attached {h : Heap} {log : DataLog} {s : InflateState} {wire input : List Bool}
    (boundary : Compressed log.dictionary wire log.output)
    (tables : TableBinding h s boundary.L boundary.D)
    (phase : ReadPrefix boundary.L boundary.D input s (held s))
    (modes : s.mode = LENEXT ∨ s.mode = DIST ∨ s.mode = DISTEXT ∨ s.mode = LIT)
    (last : s.last = Int32.ofNat boundary.block.last) :
    ∃ word, input = word ++ held s ∧ Nonempty (Attached4 h log s (wire ++ word)) := by
  obtain ⟨word, source, replay⟩ := phase.consumed_word boundary.validL boundary.validD
  let data : Reading log s (wire ++ word) := ⟨wire, boundary, word, rfl, last, replay (held s)⟩
  exact ⟨word, source, ⟨.legacy (.reading modes data), tables, True.intro⟩⟩

 theorem Compressed.unchecked_attached {h : Heap} {log : DataLog} {s : InflateState} {wire : List Bool}
    (boundary : Compressed log.dictionary wire log.output) (p : CopySyntax boundary.L boundary.D)
    (tables : TableBinding h s boundary.L boundary.D)
    (rest : p.rest = held s) (last : s.last = Int32.ofNat boundary.block.last)
    (registers : SlowReverseTokenRegisters.CopyRegisters p s) (untouched : s.length = s.was) (mode : s.mode = MATCH) :
    ∃ word, p.input = word ++ held s ∧ Nonempty (Attached4 h log s (wire ++ word)) := by
  have parsed : ReadPrefix boundary.L boundary.D p.input s p.rest :=
    .matching p rfl mode (by rw [untouched]; exact registers.1) untouched.symm registers.2.2.1
  obtain ⟨word, source, replay⟩ := parsed.consumed_word boundary.validL boundary.validD
  let reading : Reading log s (wire ++ word) := ⟨wire, boundary, word, rfl, last, replay (held s)⟩
  let data : UncheckedMatching log s (wire ++ word) :=
    ⟨reading, p, by simpa only [reading, rest] using source, rest, registers, untouched⟩
  exact ⟨word, by simpa only [rest] using source, ⟨.uncheckedMatch mode data, tables⟩⟩

 theorem Compressed.matching_attached {h : Heap} {log : DataLog} {s : InflateState} {wire : List Bool} {before fullOutput : List UInt8}
    (boundary : Compressed log.dictionary wire before) (p : CopySyntax boundary.L boundary.D)
    (tables : TableBinding h s boundary.L boundary.D)
    (rest : p.rest = held s) (last : s.last = Int32.ofNat boundary.block.last)
    (registers : SlowReverseTokenRegisters.CopyRegisters p s)
    (step : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary before p.input p.rest fullOutput false)
    (beforePrefix : before <+: log.output) (effectPrefix : log.output <+: fullOutput)
    (debt : fullOutput.length - log.output.length = s.length.toNat) (mode : s.mode = MATCH) :
    ∃ word, p.input = word ++ held s ∧ Nonempty (Attached4 h log s (wire ++ word)) := by
  obtain ⟨word, source, _replay⟩ := ZlibF.Math.TokenSuffix.step_consumed_word boundary.validL boundary.validD step
  let data : Matching log s (wire ++ word) :=
    ⟨wire, before, boundary, word, p, by simpa only [rest] using source, rest, last, registers,
      fullOutput, by simpa only [source, rest] using step, beforePrefix, effectPrefix, debt, rfl⟩
  exact ⟨word, by simpa only [rest] using source, ⟨.legacy (.matching mode data), tables, True.intro⟩⟩

 theorem Compressed.eob_attached {h : Heap} {log : DataLog} {s : InflateState} {wire input : List Bool}
    (boundary : Compressed log.dictionary wire log.output) (mode : s.mode = TYPE)
    (last : s.last = Int32.ofNat boundary.block.last)
    (step : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary log.output input (held s) log.output true) :
    ∃ word, input = word ++ held s ∧ Nonempty (Attached4 h log s (wire ++ word)) := by
  obtain ⟨word, source, ⟨phase⟩⟩ := boundary.eob_phase (Or.inl mode) last step
  exact ⟨word, source, ⟨.legacy phase, WholeWrapper.low_materialized phase (by rw [mode]; decide),
    phase.reversible_of_not_codes (by rw [mode]; decide)⟩⟩

#print axioms Compressed.complete_attached
#print axioms Compressed.reading_attached
#print axioms Compressed.unchecked_attached
#print axioms Compressed.matching_attached
#print axioms Compressed.eob_attached
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

 theorem Matching.emit_attached
    {h : Heap} {log : DataLog} {s state : InflateState} {wire : List Bool} {output : List UInt8}
    (before : Matching log s wire) (tables : TableBinding h state before.boundary.L before.boundary.D)
    (source : held state = held s) (last : state.last = s.last)
    (registers : SlowReverseTokenRegisters.CopyRegisters before.token state)
    (historyPrefix : before.before <+: output) (effect : output <+: before.fullOutput)
    (debt : before.fullOutput.length - output.length = state.length.toNat) (mode : state.mode = MATCH) :
    Nonempty (Attached4 h {log with output := output} state wire) := by
  let data : Matching {log with output := output} state wire :=
    ⟨before.beforeWire, before.before, before.boundary, before.pendingWord, before.token,
      by rw [source]; exact before.input, by rw [source]; exact before.rest, last.trans before.last,
      registers, before.fullOutput, by rw [source]; exact before.accepted,
      historyPrefix, effect, debt, before.anchor⟩
  exact ⟨.legacy (.matching mode data), tables, True.intro⟩

 theorem Matching.complete_attached
    {h : Heap} {log : DataLog} {s state : InflateState} {wire : List Bool}
    (before : Matching log s wire) (tables : TableBinding h state before.boundary.L before.boundary.D)
    (source : held state = held s) (last : state.last = s.last) (mode : state.mode = LEN) :
    Nonempty (Attached4 h {log with output := before.fullOutput} state wire) := by
  have accepted : Token.Step before.boundary.L before.boundary.D before.boundary.block.wrapper.dictionary
      before.before (before.pendingWord ++ held state) (held state) before.fullOutput false := by
    rw [source]; exact before.accepted
  obtain ⟨word, read, next, block, lengths, distances⟩ := before.boundary.advance accepted
  have same : word = before.pendingWord := List.append_cancel_right read.symm
  subst word
  have nextTables : TableBinding h state next.L next.D := by rw [lengths, distances]; exact tables
  let phase : SourcePhase {log with output := before.fullOutput} state (before.beforeWire ++ before.pendingWord) :=
    .ready next (Or.inr mode) (by rw [block]; exact last.trans before.last)
  have attached : Nonempty (Attached4 h {log with output := before.fullOutput} state (before.beforeWire ++ before.pendingWord)) :=
    ⟨.legacy phase, nextTables, True.intro⟩
  simpa only [← before.anchor] using attached

#print axioms Matching.emit_attached
#print axioms Matching.complete_attached
end Zlib.Inflate.Proofs.WholeEpoch
