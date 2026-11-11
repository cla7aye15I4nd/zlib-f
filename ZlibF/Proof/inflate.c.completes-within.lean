import ZlibF.Proof.«inflate.c.completes-meaning»
import ZlibF.Proof.«inflate.c.meaning-held-within»

/-!
# inflate.c: a call reads only bytes of a valid stream it is given

`ConsumesWithinStream` from `MeaningStep` and three facts of batch 1:

* clause 1, the consumed input stays a beginning of the stream: after a call that
  leaves `BAD` or `MEM` by `FailWithin`; otherwise the format meaning after the call
  gives a stage whose consumed and held bits are the bits of the consumed input,
  and `HeldWithin` keeps them inside the stream;
* clause 2, no `Z_OK` or `Z_BUF_ERROR` after the whole stream: `StopShort`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `HeldWithin`, from batch 1's `heldWithin` (which needs no full window). -/
theorem held_within : HeldWithin :=
  fun wrap configured dict h s consumed held stage S decoded parsed heldBits stageMatches wrapMatches
    aligned valid _ comparable =>
    heldWithin wrap configured dict h s consumed held stage S decoded parsed heldBits stageMatches
      wrapMatches valid aligned comparable

theorem consumes_within_stream (step : MeaningStep) (held : HeldWithin) (fail : FailWithin)
    (short : StopShort) : ConsumesWithinStream := by
  intro wb wrap bits r h after log pending flush rc input output used source decoded params trace
    single fit valid full started comparable dstep
  have before := meaning_of_protocol step trace
  have comparable' : log.input ++ input.take used <+: source ∨
      source <+: log.input ++ input.take used := by
    have takePre : log.input ++ input.take used <+: log.input ++ input :=
      (List.prefix_append_right_inj _).mpr (List.take_prefix _ _)
    rcases comparable with p | p
    · exact Or.inl (takePre.trans p)
    · exact List.prefix_or_prefix_of_prefix takePre p
  refine ⟨?_, ?_⟩
  · obtain ⟨wrap', configured, i, z, s, params', inv, config, _, _, _, _, stageClause⟩ :=
      step wb r h after log pending flush rc input output used before fit dstep
    rw [params] at params'
    obtain ⟨rfl, rfl⟩ : wrap = wrap' ∧ bits = configured := by
      cases params'
      exact ⟨rfl, rfl⟩
    by_cases failed : s.mode = BAD ∨ s.mode = MEM
    · exact fail wb r h after log pending flush rc input output used i z s wrap bits source decoded
        before fit dstep inv.good failed single params valid full started comparable
    · have notBad : s.mode ≠ BAD := fun e => failed (Or.inl e)
      have notMem : s.mode ≠ MEM := fun e => failed (Or.inr e)
      obtain ⟨consumed, heldBits, stage, inputBits, heldMatch, parsed, stageMatches, wrapMatches, _, _⟩ :=
        stageClause single notBad notMem config.2.2.2.2.2
      have aligned : (consumed ++ heldBits).length % 8 = 0 := by
        have := congrArg List.length inputBits
        simp only [bytesToBits_length'] at this
        omega
      have bitsComparable : bytesToBits source <+: consumed ++ heldBits ∨
          consumed ++ heldBits <+: bytesToBits source := by
        rw [← inputBits]
        rcases comparable' with p | p
        · exact Or.inr (bytesToBits_prefix_iff.mpr p)
        · exact Or.inl (bytesToBits_prefix_iff.mpr p)
      have inside := held wrap bits log.dictionary after s consumed heldBits stage source decoded
        parsed heldMatch stageMatches wrapMatches aligned valid full bitsComparable
      rw [← inputBits] at inside
      exact bytesToBits_prefix_iff.mp inside
  · intro whole condition
    exact ⟨fun ok => short wb r h after log pending flush rc input output used wrap bits source decoded
        before fit dstep single params valid full condition (Or.inl ok) whole,
      fun buf => short wb r h after log pending flush rc input output used wrap bits source decoded
        before fit dstep single params valid full condition (Or.inr buf) whole⟩

#print axioms consumes_within_stream
end Zlib.Inflate.Proofs
