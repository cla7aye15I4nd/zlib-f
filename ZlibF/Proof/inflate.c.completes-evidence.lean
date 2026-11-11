import ZlibF.Proof.«inflate.c.completes-meaning»
import ZlibF.Proof.«inflate.c.completes-evidence-grammar»

/-!
# inflate.c: output evidence after every protocol history

`TraceEvidence` from `MeaningStep` and `StepEvidence` (both open, the side of
`meaning_step`). `EvidenceInv` (the output so far is the output of a grammar
stage reached on a prefix of the consumed bits) holds after every protocol
history:

* initially and whenever no output was delivered (`evidence_of_empty`);
* after a call that does not leave `BAD` or `MEM`, from `ParseMeaning`
  (`evidence_of_meaning`); after one that does, by `StepEvidence`;
* after a dictionary call: an unsuccessful one changes nothing it reads, a
  successful one is made before any output.

The heap-free part (`trace_evidence_of_stage`) turns the stage into
`OutputEvidence` and `Determined`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- No output yet: the start of the header is a stage. -/
theorem evidence_of_empty {wb : Int32} {wrap : Api.Wrap} {bits : Nat} {log : DataLog}
    (params : Api.inflWbits wb.toInt = some (wrap, bits)) (empty : log.output = []) :
    EvidenceInv wb log := by
  intro _
  exact ⟨wrap, bits, [], .header [], params, List.nil_prefix,
    ⟨by simp [bytesToBits], wrapHeader_exists _ (inflWbits_bits params)⟩, empty⟩

/-- Outside `BAD` and `MEM` the format meaning gives the evidence invariant. -/
theorem evidence_of_meaning {wb : Int32} {r : ZStreamRef} {h : Heap} {log : DataLog}
    {pending : Bool} (current : ParseMeaning wb r h log pending) :
    EvidenceInv wb log ∨
      ∃ i z s, Zlib.Inflate.Spec.Good h r i z s ∧ (s.mode = BAD ∨ s.mode = MEM) := by
  obtain ⟨wrap, configured, i, z, s, params, inv, config, _, _, _, _, stageClause⟩ := current
  by_cases bad : s.mode = BAD
  · exact Or.inr ⟨i, z, s, inv.good, Or.inl bad⟩
  by_cases mem : s.mode = MEM
  · exact Or.inr ⟨i, z, s, inv.good, Or.inr mem⟩
  left
  intro single
  obtain ⟨consumed, held, stage, inputBits, _, parsed, _, _, outputEq, _⟩ :=
    stageClause single bad mem config.2.2.2.2.2
  exact ⟨wrap, configured, consumed, stage, params, ⟨held, inputBits.symm⟩, parsed, outputEq⟩

/-- A successful dictionary call of a zlib (or detected) history comes before any output. -/
theorem dictionary_before_output {wb : Int32} {r : ZStreamRef} {h after : Heap} {log : DataLog}
    {p : BPtr} {n : UInt32} {bytes : List UInt8}
    (current : ParseMeaning wb r h log true) (single : log.singleDictionary = true)
    (arguments : StreamArguments h r (.inflateSetDictionary (some r) p n))
    (read : Bytes h p n.toNat bytes)
    (run : C.run (inflateSetDictionary (some r) p n) h = .ok (Z_OK, after))
    (notRaw : ¬ wb.toInt < 0) : log.output = [] := by
  obtain ⟨wrap, configured, i, z, s, params, inv, config, _, _, _, _, stageClause⟩ := current
  have wrapped : s.wrap ≠ 0 := by
    intro zero
    rw [config.1] at zero
    exact notRaw ((inflWbits_raw_iff params).mpr (wrapCode_zero zero))
  have dictMode : s.mode = DICT := by
    rcases setDictionary_cases inv arguments read run with ⟨_, notOk, _⟩ | ⟨bad, _⟩ |
        ⟨_, allowed, _⟩
    · exact absurd rfl notOk
    · exact absurd bad (by decide)
    · exact allowed.resolve_left wrapped
  obtain ⟨_, _, stage, _, _, _, _, _, outputEq, request⟩ :=
    stageClause single (by rw [dictMode]; decide) (by rw [dictMode]; decide)
      (by rw [dictMode]; decide)
  obtain ⟨header, rfl, _⟩ := request.mp rfl
  exact outputEq

/-- The evidence invariant after every protocol history. -/
theorem evidence_of_protocol (step : MeaningStep) (stepEvidence : StepEvidence) {wb : Int32}
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace wb r h log pending) : EvidenceInv wb log := by
  induction trace with
  | init domain run =>
    obtain ⟨_, _, _, _, _, params, _⟩ := meaning_init domain run
    exact evidence_of_empty params rfl
  | caller _ _ _ ih => exact ih
  | step prev fit observation ih =>
    have before := meaning_of_protocol step prev
    rcases evidence_of_meaning (step _ _ _ _ _ _ _ _ _ _ _ before fit observation) with
        evidence | ⟨i, z, s, good, mode⟩
    · exact evidence
    · exact stepEvidence _ _ _ _ _ _ _ _ _ _ _ i z s before fit observation good mode ih
  | @dictionary h after log pending p n bytes rc prev fit arguments read run admitted ih =>
    have before := meaning_of_protocol step prev
    obtain ⟨wrap, bits, _, _, _, params, _⟩ := before
    intro single'
    by_cases ok : rc = Z_OK
    · subst ok
      by_cases raw : wb.toInt < 0
      · have empty : log.input = [] ∧ log.output = [] := by
          simp [raw] at single'
          exact ⟨single'.2.1, single'.2.2⟩
        exact evidence_of_empty params empty.2 single'
      · have pendingTrue : pending = true := by
          rcases admitted with neg | notOk | yes
          · exact absurd neg raw
          · exact absurd rfl notOk
          · exact yes
        subst pendingTrue
        have single : log.singleDictionary = true := by simpa [raw] using single'
        have empty : log.output = [] :=
          dictionary_before_output (log := log) (meaning_of_protocol step prev) single arguments read
            run raw
        exact evidence_of_empty params empty single'
    · have single : log.singleDictionary = true := by simpa [ok] using single'
      obtain ⟨wrap', bits', consumed, stage, params', pre, parsed, outputEq⟩ := ih single
      refine ⟨wrap', bits', consumed, stage, params', pre, ?_, outputEq⟩
      simpa [ok] using parsed

/-- `TraceEvidence`, from `MeaningStep` and `StepEvidence`. -/
theorem trace_evidence (step : MeaningStep) (stepEvidence : StepEvidence) : TraceEvidence := by
  intro wb wrap bits r h log pending params trace single window
  obtain ⟨wrap', bits', consumed, stage, params', pre, parsed, outputEq⟩ :=
    evidence_of_protocol step stepEvidence trace single
  rw [params] at params'
  obtain ⟨rfl, rfl⟩ : wrap = wrap' ∧ bits = bits' := by
    cases params'
    exact ⟨rfl, rfl⟩
  exact trace_evidence_of_stage (inflWbits_bits params) window parsed pre outputEq

#print axioms evidence_of_protocol
#print axioms trace_evidence
end Zlib.Inflate.Proofs
