import ZlibF.Proof.«inflate.c.whole-epoch-source-spine»
import ZlibF.Proof.«inflate.c.slow-reverse-token-base»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
open ZlibF.Math.LZ77History
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- The independently accepted Step and the retained parse have identical
symbol and extra reads. Distance fit is a consequence of that accepted
Step, rather than a new pending-state premise. -/
theorem SlowInputFragment.CopySyntax.accepted_copy_fields
    {L D : List Nat} (p : SlowInputFragment.CopySyntax L D)
    {dict before output : List UInt8}
    (accepted : Token.Step L D dict before p.input p.rest output false) :
    output = copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
      (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) before ∧
    distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (dict ++ before).length := by
  cases accepted with
  | literal decoded small =>
    rw [p.lengthDecode] at decoded
    obtain ⟨same, _⟩ := Prod.mk.inj (Option.some.inj decoded)
    have lower := p.lengthLower
    omega
  | copy decoded _lower _upper readLen decodedDist _upperDist readDist fit =>
    rw [p.lengthDecode] at decoded
    obtain ⟨sameSymbol, sameRest⟩ := Prod.mk.inj (Option.some.inj decoded)
    subst sameSymbol
    subst sameRest
    rw [p.lengthRead] at readLen
    obtain ⟨sameLength, sameRest⟩ := Prod.mk.inj (Option.some.inj readLen)
    subst sameLength
    subst sameRest
    rw [p.distanceDecode] at decodedDist
    obtain ⟨sameDistance, sameRest⟩ := Prod.mk.inj (Option.some.inj decodedDist)
    subst sameDistance
    subst sameRest
    rw [p.distanceRead] at readDist
    obtain ⟨sameExtra, _⟩ := Prod.mk.inj (Option.some.inj readDist)
    subst sameExtra
    exact ⟨rfl, fit⟩

namespace WholeEpoch

/-- The full logical copy and its original distance bound follow from
the accepted token already carried by the actual pending phase. -/
theorem Matching.copy_fields
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (matching : Matching log s wire) :
    matching.fullOutput = copyBack matching.boundary.block.wrapper.dictionary
      (distBases.getD matching.token.distanceSymbol 0 + matching.token.distanceValue)
      (lengthBases.getD (matching.token.symbol - 257) 0 + matching.token.lengthValue)
      matching.before ∧
    distBases.getD matching.token.distanceSymbol 0 + matching.token.distanceValue ≤
      (matching.boundary.block.wrapper.dictionary ++ matching.before).length := by
  apply matching.token.accepted_copy_fields
  simpa only [matching.input, matching.rest] using matching.accepted

/-- Persistent was/offset identify that same complete independent match. -/
theorem Matching.scalar_copy_fields
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (matching : Matching log s wire) :
    matching.fullOutput = copyBack matching.boundary.block.wrapper.dictionary
      s.offset.toNat s.was.toNat matching.before ∧
    s.offset.toNat ≤ (matching.boundary.block.wrapper.dictionary ++ matching.before).length ∧
    s.length.toNat ≤ s.was.toNat := by
  obtain ⟨full, fit⟩ := matching.copy_fields
  obtain ⟨was, remaining, offset, _back⟩ := matching.registers
  exact ⟨by simpa only [was, offset] using full,
    by simpa only [offset] using fit, remaining⟩

/-- Output prefix plus exact debt recovers the already emitted part of
this one token. No nested-copy history is supplied by the caller. -/
theorem Matching.output_copy
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (matching : Matching log s wire) :
    log.output = copyBack matching.boundary.block.wrapper.dictionary s.offset.toNat
      (s.was.toNat - s.length.toNat) matching.before := by
  obtain ⟨full, _fit, remaining⟩ := matching.scalar_copy_fields
  have size := (copy_back_extends_history matching.boundary.block.wrapper.dictionary
    matching.before s.offset.toNat s.was.toNat).2
  rw [← full] at size
  have lower := matching.emitted.length_le
  have upper := matching.remaining.length_le
  have debt := matching.debt
  have currentSize : log.output.length = matching.before.length +
      (s.was.toNat - s.length.toNat) := by omega
  rw [List.prefix_iff_eq_take.mp matching.remaining, full, currentSize]
  exact (SlowReverseToken.copy_prefix_take _ _ _ _ _ (by omega)).symm

/-- Any next physical portion extends exactly the original match prefix.
Its byte count and remaining debt are exact, including the zero-amount
and completed cases. -/
theorem Matching.copy_advance
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (matching : Matching log s wire) (amount : Nat) (bound : amount ≤ s.length.toNat) :
    let next := copyBack matching.boundary.block.wrapper.dictionary s.offset.toNat amount log.output
    next = matching.fullOutput.take (log.output.length + amount) ∧
    log.output <+: next ∧ next <+: matching.fullOutput ∧
    next.length = log.output.length + amount ∧
    matching.fullOutput.length - next.length = s.length.toNat - amount := by
  dsimp only
  obtain ⟨full, _fit, remaining⟩ := matching.scalar_copy_fields
  have oldSize := (copy_back_extends_history matching.boundary.block.wrapper.dictionary
    matching.before s.offset.toNat (s.was.toNat - s.length.toNat)).2
  rw [← matching.output_copy] at oldSize
  have exactPrefix :
      copyBack matching.boundary.block.wrapper.dictionary s.offset.toNat amount log.output =
      matching.fullOutput.take (log.output.length + amount) := by
    conv => lhs; rw [matching.output_copy, ← copy_back_compose]
    rw [full, oldSize]
    have prefixEq := SlowReverseToken.copy_prefix_take matching.boundary.block.wrapper.dictionary
      matching.before s.offset.toNat s.was.toNat
      (s.was.toNat - s.length.toNat + amount) (by omega)
    simpa only [Nat.add_assoc] using prefixEq
  have extension := copy_back_extends_history matching.boundary.block.wrapper.dictionary
    log.output s.offset.toNat amount
  refine ⟨exactPrefix, extension.1, ?_, extension.2, ?_⟩
  · rw [exactPrefix]
    exact List.take_prefix _ _
  · have debt := matching.debt
    have upper := matching.remaining.length_le
    rw [extension.2]
    omega

#print axioms SlowInputFragment.CopySyntax.accepted_copy_fields
#print axioms Matching.copy_fields
#print axioms Matching.scalar_copy_fields
#print axioms Matching.output_copy
#print axioms Matching.copy_advance
end WholeEpoch
end Zlib.Inflate.Proofs
