import ZlibF.Proof.«inflate.c.whole-slow-read-attachment»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken SlowRejectedToken FunctionalEpoch FunctionalTrailer
open ZlibF.Math.LZ77Copy ZlibF.Math.LZ77History
set_option autoImplicit false
set_option maxRecDepth 4096

/-- Interpret the actual ordinary slow token packet at the exact credited
source and physical output. Waiting MATCH receives the unchecked phase;
only fully emitted accepted output commits a token to the boundary. -/
 theorem event_phase_attached
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z streamZ : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {wire prior : List Bool} {outcome : Except Ex Unit} {used : Nat} {more : List UInt8}
    (before : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed base.dictionary wire (base.output ++ before.emitted))
    (anchor : before.word = wire ++ prior) (last : s.last = Int32.ofNat boundary.block.last)
    (frame : DecodeStateFrame s state) (tables : TableBinding after state boundary.L boundary.D)
    (buffers : DispatchBuffers after r regs ((raw.drop before.used).drop used))
    (output : OutputCredit after streamZ state regs base.output (before.emitted ++ more) 0)
    (event : SlowReverseTokenComplete.TokenEvent boundary.L boundary.D
      (retained boundary.block.wrapper.dictionary base.output) before.emitted
      (prior ++ stream l (raw.drop before.used)) r zs outcome regs after streamZ state ((raw.drop before.used).drop used))
    (bad : state.mode = BAD → BadSource boundary.L boundary.D
      (retained boundary.block.wrapper.dictionary base.output) before.emitted
      (prior ++ stream l (raw.drop before.used)) regs ((raw.drop before.used).drop used)) :
    ∃ word, ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits ((raw.drop before.used).take used)) =
      word ++ natBits regs.bits.toNat regs.hold.toNat ∧
      Nonempty (Attached4 after (sourceLog (callLog base raw (before.used + used) (before.emitted ++ more)))
        (leaveState state regs) (wire ++ word)) := by
  have savedLast : (leaveState state regs).last = Int32.ofNat boundary.block.last := by
    change state.last = _
    rw [frame]
    exact last
  have savedTables : TableBinding after (leaveState state regs) boundary.L boundary.D := tables
  cases event with
  | wait view phase _empty pending =>
    have empty := no_output_more_empty view output
    subst more
    simp only [List.append_nil] at output ⊢
    exact boundary.read_prefix_attached
      (log := sourceLog (callLog base raw (before.used + used) before.emitted)) savedTables phase pending savedLast
  | literalPending view phase mode _step _length _small =>
    have empty := no_output_more_empty view output
    subst more
    simp only [List.append_nil] at output ⊢
    exact boundary.read_prefix_attached
      (log := sourceLog (callLog base raw (before.used + used) before.emitted)) savedTables phase
      (fun matching => ((by decide : LIT ≠ MATCH) (mode.symm.trans matching)).elim) savedLast
  | eob view mode _back step =>
    have empty := no_output_more_empty view output
    subst more
    simp only [List.append_nil] at output ⊢
    have heldStep := prior_step_held_prefix boundary.validL boundary.validD step
    have logical := token_expand_retained_context (dict := boundary.block.wrapper.dictionary) (past := base.output) (history := before.emitted) heldStep
    exact boundary.eob_attached (s := leaveState state regs) (log := sourceLog (callLog base raw (before.used + used) before.emitted)) mode savedLast logical
  | literalDone _good _buffers mode get put bytes step =>
    have observed := OutputCredit.observed_unique output buffers put get bytes
    have heldStep := prior_step_held_prefix boundary.validL boundary.validD step
    have logical := token_expand_retained_context (dict := boundary.block.wrapper.dictionary) (past := base.output) (history := before.emitted) heldStep
    rw [← observed] at logical
    exact boundary.complete_attached
      (log := sourceLog (callLog base raw (before.used + used) (before.emitted ++ more))) savedTables logical mode savedLast
  | bad _good _B mode =>
    have rejected := bad mode
    obtain ⟨word, source, invalid⟩ := bad_source_prior_credit
      (l := l) (bs := raw.drop before.used) (used := used) (prior := prior) rfl rejected
    have creditedBytes : bytesBits (base.input ++ raw.take (before.used + used)) =
        wire ++ (prior ++ SlowRejectedLength.credited l (raw.drop before.used) used) := by
      have join : (base.input ++ raw.take before.used) ++ (raw.drop before.used).take used =
          base.input ++ raw.take (before.used + used) := by rw [List.take_add, List.append_assoc]
      rw [← join, bytesBits_append, before.credited, anchor]
      simp only [SlowRejectedLength.credited, List.append_assoc]
    have logicalInvalid : ∀ future rest target, ¬ Symbols boundary.L boundary.D boundary.block.wrapper.dictionary
        (base.output ++ before.emitted) ((prior ++ SlowRejectedLength.credited l (raw.drop before.used) used) ++ future) rest target := by
      intro future rest target parsed
      obtain ⟨physicalTarget, _target, physical⟩ := symbols_retained_context parsed
      exact invalid future rest physicalTarget physical
    have rejects : Rejects (sourceLog (callLog base raw (before.used + used) (before.emitted ++ more))) :=
      boundary.rejects_credited (log := sourceLog (callLog base raw (before.used + used) (before.emitted ++ more))) creditedBytes logicalInvalid
    exact ⟨word, by simpa only [SlowRejectedLength.credited, List.append_assoc] using source,
      ⟨.legacy (.rejected mode rejects), True.intro, True.intro⟩⟩
  | copy p amount dest off array inputEq residual _good _buffers _dictionary positive amountBound
      remaining modes get put physical count _rest step was offset back completed =>
    have bytes : writtenBytes array off (regs.out_.toNat - regs.left.toNat) =
        (copyBack (retained boundary.block.wrapper.dictionary base.output)
          (distBases.getD p.distanceSymbol 0 + p.distanceValue)
          (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) before.emitted).take (before.emitted.length + amount) := by
      rw [count]
      exact physical
    have observed := OutputCredit.observed_unique output buffers put get bytes
    rw [residual] at step
    have heldStep := prior_step_held_prefix boundary.validL boundary.validD step
    have logical := token_expand_retained_context (dict := boundary.block.wrapper.dictionary) (past := base.output) (history := before.emitted) heldStep
    let full := copyBack (retained boundary.block.wrapper.dictionary base.output)
      (distBases.getD p.distanceSymbol 0 + p.distanceValue)
      (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) before.emitted
    have fullSize : full.length = before.emitted.length + (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) :=
      (copy_back_extends_history _ _ _ _).2
    have actualCopy : before.emitted ++ more =
        copyBack (retained boundary.block.wrapper.dictionary base.output)
          (distBases.getD p.distanceSymbol 0 + p.distanceValue) amount before.emitted := by
      rw [observed]
      exact (copy_prefix_take _ _ _ _ _ amountBound).symm
    have actualSize : (before.emitted ++ more).length = before.emitted.length + amount := by
      rw [actualCopy]
      exact (copy_back_extends_history _ _ _ _).2
    have actualPrefix : before.emitted <+: before.emitted ++ more := by
      rw [actualCopy]
      exact (copy_back_extends_history _ _ _ _).1
    have effectPrefix : before.emitted ++ more <+: full := by
      rw [observed]
      exact List.take_prefix _ _
    have registers : SlowReverseTokenRegisters.CopyRegisters p state := ⟨was, by omega, offset, back⟩
    obtain ⟨q, qInput, qRest, qRegisters⟩ := held_copy_registers p boundary.validL boundary.validD inputEq residual registers
    rcases modes with len | matching
    · have equal := completed.mp len
      have fullObserved : before.emitted ++ more = full := by
        change before.emitted ++ more = full.take (before.emitted.length + amount) at observed
        rw [equal, ← fullSize, List.take_length] at observed
        exact observed
      dsimp only [full] at fullObserved
      rw [← fullObserved] at logical
      exact boundary.complete_attached
        (log := sourceLog (callLog base raw (before.used + used) (before.emitted ++ more))) savedTables logical len savedLast
    · have accepted : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary (base.output ++ before.emitted)
          q.input q.rest (base.output ++ full) false := by
        rw [qInput, qRest]
        exact logical
      have beforePrefix : base.output ++ before.emitted <+: base.output ++ (before.emitted ++ more) :=
        (List.prefix_append_right_inj base.output).mpr actualPrefix
      have fullPrefix : base.output ++ (before.emitted ++ more) <+: base.output ++ full :=
        (List.prefix_append_right_inj base.output).mpr effectPrefix
      have debt : (base.output ++ full).length - (base.output ++ (before.emitted ++ more)).length = state.length.toNat := by
        simp only [List.length_append, fullSize, actualSize]
        omega
      obtain ⟨word, source, attached⟩ := boundary.matching_attached
        (log := sourceLog (callLog base raw (before.used + used) (before.emitted ++ more))) q savedTables qRest savedLast qRegisters
        accepted beforePrefix fullPrefix debt matching
      exact ⟨word, qInput.symm.trans source, attached⟩

#print axioms event_phase_attached
end Zlib.Inflate.Proofs.WholeEpoch
