import ZlibF.Proof.«inflate.c.meaning-accept»

/-!
# inflate.c: the format clauses from the format meaning

The two format clauses of `Goal.inflate_sequence` that hold for every
protocol trace: a finished single-dictionary epoch consumed an accepted
stream (`accepted_of_meaning`), and on a beginning of a valid stream the
output begins the decoding, there is no data error, and the end comes
exactly at the end of the stream (`prefix_of_meaning`). Statements as on
`skeleton/inflate`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Only the end stage is represented in `DONE`. -/
theorem stage_done_of_mode {h : Heap} {s : InflateState} {wrap : Api.Wrap} {dict : List UInt8}
    {stage : WrapStage} (stageMatches : StageMatches h s wrap dict stage) (done : s.mode = DONE) :
    ∃ out, stage = .done out := by
  cases stage with
  | header bytes =>
    obtain ⟨_, high⟩ := stageMatches
    rw [done] at high
    exact absurd high (by decide)
  | needDict header =>
    have mode : s.mode = DICT := stageMatches
    rw [done] at mode
    exact absurd mode (by decide)
  | body header pos =>
    obtain ⟨body, _, _⟩ := stageMatches
    obtain ⟨out, final, blockStage⟩ := pos
    cases blockStage with
    | boundary =>
      obtain ⟨mode | mode, _⟩ := body <;> rw [done] at mode <;> exact absurd mode (by decide)
    | storedHeader =>
      obtain ⟨mode, _⟩ := body
      rw [done] at mode
      exact absurd mode (by decide)
    | stored remaining =>
      obtain ⟨mode | mode, _⟩ := body <;> rw [done] at mode <;> exact absurd mode (by decide)
    | dynamicHeader header =>
      obtain ⟨dynamic, _⟩ := body
      rcases dynamic with ⟨mode, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨mode, _⟩ | ⟨mode, _⟩⟩ <;>
        rw [done] at mode <;> exact absurd mode (by decide)
    | codes L D pending =>
      obtain ⟨_, _, _, modes⟩ := body
      cases pending with
      | none => rcases modes with mode | mode <;> rw [done] at mode <;> exact absurd mode (by decide)
      | lengthExtra _ =>
        obtain ⟨mode, _⟩ := modes
        rw [done] at mode
        exact absurd mode (by decide)
      | distance _ =>
        obtain ⟨mode, _⟩ := modes
        rw [done] at mode
        exact absurd mode (by decide)
      | distanceExtra _ _ =>
        obtain ⟨mode, _⟩ := modes
        rw [done] at mode
        exact absurd mode (by decide)
      | copy _ _ =>
        obtain ⟨mode, _⟩ := modes
        rw [done] at mode
        exact absurd mode (by decide)
      | literal _ =>
        obtain ⟨mode, _⟩ := modes
        rw [done] at mode
        exact absurd mode (by decide)
    | finished =>
      obtain ⟨mode | mode, _⟩ := body <;> rw [done] at mode <;> exact absurd mode (by decide)
  | trailer header out bytes =>
    obtain ⟨mode | mode, _⟩ := stageMatches <;> rw [done] at mode <;> exact absurd mode (by decide)
  | done out => exact ⟨out, rfl⟩

/-- Nothing is held at the end. -/
theorem held_empty_of_done {h : Heap} {s : InflateState} {wrap : Api.Wrap} {configured : Nat}
    {dict out : List UInt8} {held : List Bool} (wrapMatches : WrapMatches h s wrap configured dict
      (.done out)) (heldBits : HeldBits s held) : held = [] := by
  have zero : s.bits = 0 := wrapMatches
  have := heldBits.1
  rw [zero] at this
  exact List.eq_nil_of_length_eq_zero (by simpa using this)

/-- A finished single-dictionary epoch consumed an accepted stream. -/
theorem meaning_accepted {wb : Int32} {wrap : Api.Wrap} {bits : Nat} {r : ZStreamRef}
    {h : Heap} {log : DataLog} {pending : Bool}
    (params : Api.inflWbits wb.toInt = some (wrap, bits))
    (current : ParseMeaning wb r h log pending)
    (single : log.singleDictionary = true) (finished : log.result = Z_STREAM_END) :
    Api.Layer.InflateAccepted wrap bits log.dictionary log.input log.output := by
  obtain ⟨wrap', bits', i, z, s, params', inv, config, _, ended, _, memory, stageClause⟩ :=
    current
  rw [params] at params'
  obtain ⟨rfl, rfl⟩ : wrap = wrap' ∧ bits = bits' := by
    cases params'
    exact ⟨rfl, rfl⟩
  rcases ended finished with done | mem
  · obtain ⟨consumed, held, stage, inputBits, heldBits, parsed, stageMatches, wrapMatches,
      outputEq, _⟩ := stageClause single (by rw [done]; decide) (by rw [done]; decide)
        (by rw [done]; decide)
    obtain ⟨out, rfl⟩ := stage_done_of_mode stageMatches done
    have empty := held_empty_of_done wrapMatches heldBits
    subst empty
    rw [outputEq]
    exact wrapParsed_accepted parsed (by simpa using inputBits)
  · exact (memory single mem).1 finished

/-- On a beginning of a valid stream: the output begins the decoding, there
is no data error, and the end comes exactly at the end of the stream. -/
theorem meaning_prefix {wb : Int32} {wrap : Api.Wrap} {bits : Nat} {r : ZStreamRef}
    {h : Heap} {log : DataLog} {pending : Bool} {source decoded : List UInt8}
    (params : Api.inflWbits wb.toInt = some (wrap, bits))
    (current : ParseMeaning wb r h log pending)
    (valid : Api.Layer.Decodes wrap bits log.dictionary source decoded)
    (single : log.singleDictionary = true) (full : Api.FullWindow wrap bits source)
    (started : log.input <+: source) :
    log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
      (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded) := by
  obtain ⟨wrap', bits', i, z, s, params', inv, config, dataError, ended, bad, memory,
    stageClause⟩ :=
    current
  rw [params] at params'
  obtain ⟨rfl, rfl⟩ : wrap = wrap' ∧ bits = bits' := by
    cases params'
    exact ⟨rfl, rfl⟩
  by_cases isBad : s.mode = BAD
  · exact absurd started (bad single isBad source decoded valid full)
  by_cases isMem : s.mode = MEM
  · exact (memory single isMem).2 source decoded valid full started
  obtain ⟨consumed, held, stage, inputBits, heldBits, parsed, stageMatches, wrapMatches,
    outputEq, _⟩ := stageClause single isBad isMem config.2.2.2.2.2
  obtain ⟨output, ending⟩ := wrapParsed_prefix parsed inputBits valid started
  refine ⟨by rw [outputEq]; exact output, fun error => isBad (dataError error), fun finished => ?_⟩
  rcases ended finished with done | mem
  · obtain ⟨out, rfl⟩ := stage_done_of_mode stageMatches done
    obtain ⟨inputEq, outEq⟩ := ending out rfl (held_empty_of_done wrapMatches heldBits)
    exact ⟨inputEq, by rw [outputEq, ← outEq]; rfl⟩
  · exact absurd mem isMem

#print axioms stage_done_of_mode
#print axioms meaning_accepted
#print axioms meaning_prefix

end Zlib.Inflate.Proofs
