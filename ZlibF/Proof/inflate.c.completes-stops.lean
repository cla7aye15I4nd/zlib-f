import ZlibF.Proof.«inflate.c.completes-meaning»
import ZlibF.Proof.«inflate.c.completes-due»
import ZlibF.Spec.Functional.Sequences
import ZlibF.Spec.Functional.Streams

/-!
# inflate.c: a call blocked on a valid stream has output still due

`StopsWhenBlocked` from `MeaningStep`, `ConsumesWithinStream` and `BlockedLeave`.
A call that returns `Z_OK` or `Z_BUF_ERROR` with input left stopped with a full
output in `LIT`, `MATCH` or `COPY` with bytes left (`BlockedLeave`). The format
meaning after the call puts the decoder at a body stage with output still due
(`due_of_mode`), on a beginning of the valid stream (`ConsumesWithinStream`), so
the output delivered so far is strictly shorter than the decoding
(`wrapParsed_due`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The stage of a decoder that holds output to write is a body stage with output due. -/
theorem due_of_mode {h : Heap} {s : InflateState} {wrap : Api.Wrap} {dict : List UInt8}
    {stage : WrapStage} (stageMatches : StageMatches h s wrap dict stage)
    (copies : ∀ header out final L D remaining dist,
      stage = .body header ⟨out, final, .codes L D (.copy remaining dist)⟩ → 0 < remaining)
    (holding : s.mode = LIT ∨ s.mode = MATCH ∨ (s.mode = COPY ∧ s.length ≠ 0)) :
    ∃ header pos, stage = .body header pos ∧ Due pos.stage := by
  have modeIn : s.mode = LIT ∨ s.mode = MATCH ∨ s.mode = COPY := by
    rcases holding with e | e | ⟨e, _⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  have notMode : ∀ m : UInt32, m ≠ LIT → m ≠ MATCH → m ≠ COPY → s.mode = m → False := by
    intro m a b c e
    rcases modeIn with x | x | x <;> rw [e] at x
    · exact a x
    · exact b x
    · exact c x
  cases stage with
  | header bytes =>
    exfalso
    have range : HEAD ≤ s.mode ∧ s.mode ≤ DICTID := stageMatches
    rcases modeIn with e | e | e <;> rw [e] at range <;> exact absurd range (by decide)
  | needDict header =>
    exact absurd stageMatches (fun e => notMode DICT (by decide) (by decide) (by decide) e)
  | trailer header out bytes =>
    exfalso
    rcases stageMatches.1 with e | e
    · exact notMode CHECK (by decide) (by decide) (by decide) e
    · exact notMode LENGTH (by decide) (by decide) (by decide) e
  | done out =>
    exact absurd stageMatches (fun e => notMode DONE (by decide) (by decide) (by decide) e)
  | body header pos =>
    refine ⟨header, pos, rfl, ?_⟩
    have body := stageMatches.1
    obtain ⟨out, final, st⟩ := pos
    cases st with
    | boundary =>
      exfalso
      rcases body.1 with e | e
      · exact notMode TYPE (by decide) (by decide) (by decide) e
      · exact notMode TYPEDO (by decide) (by decide) (by decide) e
    | storedHeader => exact absurd body.1 (notMode STORED (by decide) (by decide) (by decide))
    | stored remaining =>
      obtain ⟨mode, length, _⟩ := body
      cases remaining with
      | succ k => trivial
      | zero =>
        exfalso
        rcases holding with e | e | ⟨e, nonzero⟩
        · rcases mode with m | m <;> rw [e] at m <;> exact absurd m (by decide)
        · rcases mode with m | m <;> rw [e] at m <;> exact absurd m (by decide)
        · exact nonzero (UInt32.toNat_inj.mp (by simpa using length))
    | dynamicHeader bits =>
      exfalso
      rcases body.1 with ⟨e, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, (⟨e, _⟩ | ⟨e, _⟩)⟩
      · exact notMode TABLE (by decide) (by decide) (by decide) e
      · exact notMode LENLENS (by decide) (by decide) (by decide) e
      · exact notMode CODELENS (by decide) (by decide) (by decide) e
    | codes L D p =>
      obtain ⟨_, _, _, pending⟩ := body
      cases p with
      | none =>
        exfalso
        rcases pending.1 with e | e
        · exact notMode LEN_ (by decide) (by decide) (by decide) e
        · exact notMode LEN (by decide) (by decide) (by decide) e
      | lengthExtra _ => exact absurd pending.1 (notMode LENEXT (by decide) (by decide) (by decide))
      | distance _ => exact absurd pending.1 (notMode DIST (by decide) (by decide) (by decide))
      | distanceExtra _ _ =>
        exact absurd pending.1 (notMode DISTEXT (by decide) (by decide) (by decide))
      | copy remaining dist =>
        have positive := copies header out final L D remaining dist rfl
        cases remaining with
        | succ k => trivial
        | zero => exact absurd positive (by decide)
      | literal _ => trivial
    | finished =>
      exfalso
      rcases body.1 with e | e
      · exact notMode TYPE (by decide) (by decide) (by decide) e
      · exact notMode TYPEDO (by decide) (by decide) (by decide) e

/-- `StopsWhenBlocked`, from `MeaningStep`, `ConsumesWithinStream` and `BlockedLeave`. -/
theorem stops_when_blocked (call : Goal.inflate) (step : MeaningStep) (within : ConsumesWithinStream)
    (blocked : BlockedLeave) : StopsWhenBlocked := by
  intro wb wrap bits r h after log pending flush rc input output used source decoded z' params trace
    single fit valid full started comparable dstep flushes codes hz' left
  have before := meaning_of_protocol step trace
  have saved := before
  obtain ⟨_, _, i0, z0, s0, _, inv0, _⟩ := saved
  have observed := dstep
  obtain ⟨zb, _, getb, _, buffers, active, _, _, _, run⟩ := observed
  obtain ⟨wrap', configured, i, z, s, params', inv, config, _, _, _, _, stageClause⟩ :=
    step wb r h after log pending flush rc input output used before fit dstep
  rw [params] at params'
  obtain ⟨rfl, rfl⟩ : wrap = wrap' ∧ bits = configured := by
    cases params'
    exact ⟨rfl, rfl⟩
  have sameZ : z = z' := Option.some.inj (inv.good.live.hz.symm.trans hz')
  subst sameZ
  have notBlock : flush ≠ Z_BLOCK := by rcases flushes with f | f | f <;> rw [f] <;> decide
  have notTrees : flush ≠ Z_TREES := by rcases flushes with f | f | f <;> rw [f] <;> decide
  obtain ⟨full', s', get', holding⟩ :=
    blocked h r i0 z0 s0 flush rc after z inv0 fit buffers active run hz' notBlock notTrees codes left
  -- the decoder record after the call is the one before it
  have sameIndex : i = i0 := by
    have zb0 : zb = z0 := Option.some.inj (getb.symm.trans inv0.good.live.hz)
    subst zb0
    obtain ⟨rc2, after2, z2, s2, used2, out2, run2, good2, accounting, -⟩ :=
      call h r i0 zb s0 flush (InflateProtocolTrace.reachable trace) inv0.good fit inv0.alloc
        buffers active
    have same : (rc, after) = (rc2, after2) := Except.ok.inj (run.symm.trans run2)
    cases same
    have zSame : z2 = z := Option.some.inj (good2.live.hz.symm.trans hz')
    subst zSame
    have st1 := inv.good.live.zst
    have st2 := inv0.good.live.zst
    rw [accounting.2.2.2.2.2.2.1, st2] at st1
    cases st1
    rfl
  subst sameIndex
  have sameS : s' = s := Option.some.inj (get'.symm.trans inv.good.live.hs)
  subst sameS
  have notBad : s'.mode ≠ BAD := by
    rcases holding with e | e | ⟨e, _⟩ <;> rw [e] <;> decide
  have notMem : s'.mode ≠ MEM := by
    rcases holding with e | e | ⟨e, _⟩ <;> rw [e] <;> decide
  obtain ⟨consumed, held, stage, inputBits, _, parsed, stageMatches, _, outputEq, _⟩ :=
    stageClause single notBad notMem config.2.2.2.2.2
  have copies : ∀ header out final L D remaining dist,
      stage = .body header ⟨out, final, .codes L D (.copy remaining dist)⟩ → 0 < remaining := by
    intro header out final L D remaining dist e
    subst e
    obtain ⟨_, _, _, _, dparsed⟩ := parsed
    exact copy_remaining_pos dparsed
  obtain ⟨header, pos, rfl, due⟩ := due_of_mode stageMatches copies holding
  have onStream := (within wb wrap bits r h after log pending flush rc input output used source decoded
    params trace single fit valid full started comparable dstep).1
  have shorter := wrapParsed_due parsed due inputBits valid onStream
  refine ⟨full', ?_⟩
  have lengths := congrArg List.length outputEq
  simp only [List.length_append, WrapStage.output] at lengths
  omega

#print axioms stops_when_blocked
end Zlib.Inflate.Proofs
