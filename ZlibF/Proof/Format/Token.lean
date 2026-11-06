import ZlibF.Spec.Format.Token

/-!
# Local tokens and the original Huffman-block grammar

Successful tokens compose with, and are exposed by, the original Symbols
constructors. Every token rejection contradicts that grammar using only
determinism of the independent symbol and extra-bit functions.
-/

namespace ZlibF.Spec.Token

/-- Each local success supplies exactly the corresponding original
constructor, without requiring the unread suffix to be valid. -/
theorem step_composes_symbols : Goal.step_composes_symbols := by
  intro L D dict history input rest next finished token
  cases token with
  | literal decoded small =>
    refine ⟨?_, ?_⟩
    · intro impossible; cases impossible
    · intro _ tail output continuation
      exact Symbols.lit decoded small continuation
  | copy decoded lower upper lengthRead distanceDecoded distanceBound distanceRead fits =>
    refine ⟨?_, ?_⟩
    · intro impossible; cases impossible
    · intro _ tail output continuation
      exact Symbols.copy decoded lower upper lengthRead distanceDecoded distanceBound distanceRead
        (by simpa only [Nat.add_comm] using fits) continuation
  | eob decoded =>
    refine ⟨fun _ => ⟨rfl, Symbols.eob decoded⟩, ?_⟩
    intro impossible; cases impossible

/-- An original block derivation always begins with the same local token
and either ends there or has the original grammar as its continuation. -/
theorem symbols_exposes_step : Goal.symbols_exposes_step := by
  intro L D dict history input tail output parsed
  cases parsed with
  | eob decoded =>
    exact ⟨_, _, true, Step.eob decoded, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | lit decoded small continuation =>
    exact ⟨_, _, false, Step.literal decoded small, Or.inr ⟨rfl, continuation⟩⟩
  | copy decoded lower upper lengthRead distanceDecoded distanceBound distanceRead fits continuation =>
    exact ⟨_, _, false,
      Step.copy decoded lower upper lengthRead distanceDecoded distanceBound distanceRead
        (by simpa only [Nat.add_comm] using fits), Or.inr ⟨rfl, continuation⟩⟩

/-- The stated invalid-code and distance-bound reasons exclude every
original block derivation, without a heap or table assumption. -/
theorem rejected_has_no_symbols : Goal.rejected_has_no_symbols := by
  intro L D dict history input rejected rest output parsed
  cases rejected with
  | length invalid =>
    apply invalid []
    cases parsed with
    | eob decoded =>
      exact ⟨256, _, by simpa only [List.append_nil] using decoded, by decide⟩
    | lit decoded small continuation =>
      exact ⟨_, _, by simpa only [List.append_nil] using decoded, by omega⟩
    | copy decoded lower upper lengthRead distanceDecoded distanceBound distanceRead fits continuation =>
      exact ⟨_, _, by simpa only [List.append_nil] using decoded, upper⟩
  | distance decoded lower upper lengthRead invalid =>
    cases parsed with
    | eob decoded' =>
      have same := (Prod.mk.inj (Option.some.inj (decoded.symm.trans decoded'))).1
      omega
    | lit decoded' small continuation =>
      have same := (Prod.mk.inj (Option.some.inj (decoded.symm.trans decoded'))).1
      omega
    | copy decoded' lower' upper' lengthRead' distanceDecoded' distanceBound' distanceRead' fits continuation =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (decoded.symm.trans decoded'))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lengthRead.symm.trans lengthRead'))
      apply invalid []
      exact ⟨_, _, by simpa only [List.append_nil] using distanceDecoded', distanceBound'⟩
  | tooFar decoded lower upper lengthRead distanceDecoded distanceBound distanceRead far =>
    cases parsed with
    | eob decoded' =>
      have same := (Prod.mk.inj (Option.some.inj (decoded.symm.trans decoded'))).1
      omega
    | lit decoded' small continuation =>
      have same := (Prod.mk.inj (Option.some.inj (decoded.symm.trans decoded'))).1
      omega
    | copy decoded' lower' upper' lengthRead' distanceDecoded' distanceBound' distanceRead' fits continuation =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (decoded.symm.trans decoded'))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lengthRead.symm.trans lengthRead'))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (distanceDecoded.symm.trans distanceDecoded'))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (distanceRead.symm.trans distanceRead'))
      omega

end ZlibF.Spec.Token
