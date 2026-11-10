import ZlibF.Proof.«inflate.c.whole-slow-attached-phases»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

 theorem prior_input_split (prior : List Bool) (l : IL) (bs : List UInt8) (used : Nat) :
    (((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used)) ++ bytesBits (bs.drop used)) =
      prior ++ stream l bs := by
  rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
  simp only [stream, List.append_assoc]

 theorem held_copy_registers
    {L D : List Nat} {s : InflateState} {prior : List Bool} {l regs : IL} {bs : List UInt8} {used : Nat}
    (p : CopySyntax L D) (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (input : p.input = prior ++ stream l bs) (rest : p.rest = stream regs (bs.drop used))
    (registers : SlowReverseTokenRegisters.CopyRegisters p s) :
    ∃ q : CopySyntax L D,
      q.input = (prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used) ∧
      q.rest = natBits regs.bits.toNat regs.hold.toNat ∧
      SlowReverseTokenRegisters.CopyRegisters q (leaveState s regs) := by
  obtain ⟨q, before, after, values⟩ := registers.cancel_suffix p lengths distances
    (suffix := bytesBits (bs.drop used))
    (input.trans (prior_input_split prior l bs used).symm) rest
  exact ⟨q, before, after, copy_registers_locals values regs⟩

/-- A real no-output parser result attaches its finite accepted reads to
v4, including the separate not-yet-distance-checked MATCH case. -/
 theorem Compressed.read_prefix_attached
    {h : Heap} {log : DataLog} {state : InflateState} {wire prior : List Bool} {l regs : IL} {bs : List UInt8} {used : Nat}
    (boundary : Compressed log.dictionary wire log.output)
    (tables : TableBinding h (leaveState state regs) boundary.L boundary.D)
    (phase : ReadPrefix boundary.L boundary.D (prior ++ stream l bs) state (stream regs (bs.drop used)))
    (pending : state.mode = MATCH → ∃ p : CopySyntax boundary.L boundary.D,
      p.input = prior ++ stream l bs ∧ p.rest = stream regs (bs.drop used) ∧ SlowReverseTokenRegisters.CopyRegisters p state)
    (last : (leaveState state regs).last = Int32.ofNat boundary.block.last) :
    ∃ word, ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used)) =
      word ++ natBits regs.bits.toNat regs.hold.toNat ∧
      Nonempty (Attached4 h log (leaveState state regs) (wire ++ word)) := by
  have heldPhase := read_prefix_locals (prior_read_held_prefix boundary.validL boundary.validD phase) regs
  generalize inputEq : ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used)) = tokenInput at heldPhase
  generalize restEq : natBits regs.bits.toNat regs.hold.toNat = tokenRest at heldPhase
  cases heldPhase with
  | code mode =>
    refine ⟨[], by simp only [List.nil_append], ?_⟩
    have attached : Attached4 h log (leaveState state regs) wire := ⟨.legacy (.ready boundary (Or.inr mode) last), tables, True.intro⟩
    simpa only [List.append_nil] using Nonempty.intro attached
  | literal decoded small mode length back =>
    have parsed : ReadPrefix boundary.L boundary.D tokenInput (leaveState state regs) (held (leaveState state regs)) := by
      change ReadPrefix _ _ _ _ (natBits regs.bits.toNat regs.hold.toNat)
      rw [restEq]
      exact .literal decoded small mode length back
    obtain ⟨word, source, attached⟩ := boundary.reading_attached tables parsed (Or.inr (Or.inr (Or.inr mode))) last
    have source' : tokenInput = word ++ natBits regs.bits.toNat regs.hold.toNat := source
    rw [restEq] at source'
    exact ⟨word, source', attached⟩
  | lenext decoded lower upper mode length extra back =>
    have parsed : ReadPrefix boundary.L boundary.D tokenInput (leaveState state regs) (held (leaveState state regs)) := by
      change ReadPrefix _ _ _ _ (natBits regs.bits.toNat regs.hold.toNat)
      rw [restEq]
      exact .lenext decoded lower upper mode length extra back
    obtain ⟨word, source, attached⟩ := boundary.reading_attached tables parsed (Or.inl mode) last
    have source' : tokenInput = word ++ natBits regs.bits.toNat regs.hold.toNat := source
    rw [restEq] at source'
    exact ⟨word, source', attached⟩
  | dist decoded lower upper read mode length was back =>
    have parsed : ReadPrefix boundary.L boundary.D tokenInput (leaveState state regs) (held (leaveState state regs)) := by
      change ReadPrefix _ _ _ _ (natBits regs.bits.toNat regs.hold.toNat)
      rw [restEq]
      exact .dist decoded lower upper read mode length was back
    obtain ⟨word, source, attached⟩ := boundary.reading_attached tables parsed (Or.inr (Or.inl mode)) last
    have source' : tokenInput = word ++ natBits regs.bits.toNat regs.hold.toNat := source
    rw [restEq] at source'
    exact ⟨word, source', attached⟩
  | distext decoded lower upper read distanceDecoded distanceUpper mode length was offset extra back =>
    have parsed : ReadPrefix boundary.L boundary.D tokenInput (leaveState state regs) (held (leaveState state regs)) := by
      change ReadPrefix _ _ _ _ (natBits regs.bits.toNat regs.hold.toNat)
      rw [restEq]
      exact .distext decoded lower upper read distanceDecoded distanceUpper mode length was offset extra back
    obtain ⟨word, source, attached⟩ := boundary.reading_attached tables parsed (Or.inr (Or.inr (Or.inl mode))) last
    have source' : tokenInput = word ++ natBits regs.bits.toNat regs.hold.toNat := source
    rw [restEq] at source'
    exact ⟨word, source', attached⟩
  | matching _p _input mode _length was _distance =>
    obtain ⟨p, input, rest, registers⟩ := pending mode
    obtain ⟨q, qInput, qRest, qRegisters⟩ := held_copy_registers p boundary.validL boundary.validD input rest registers
    obtain ⟨word, source, attached⟩ := boundary.unchecked_attached q tables qRest last qRegisters was.symm mode
    have source' : ((prior ++ natBits l.bits.toNat l.hold.toNat) ++ bytesBits (bs.take used)) =
        word ++ natBits regs.bits.toNat regs.hold.toNat := qInput.symm.trans source
    rw [inputEq, restEq] at source'
    exact ⟨word, source', attached⟩

#print axioms prior_input_split
#print axioms held_copy_registers
#print axioms Compressed.read_prefix_attached
end Zlib.Inflate.Proofs.WholeEpoch
