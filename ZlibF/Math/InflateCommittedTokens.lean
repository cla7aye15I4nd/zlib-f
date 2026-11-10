import ZlibF.Math.InflateTokenContext
import ZlibF.Proof.«inflate.c.token-suffix-cancel»

namespace ZlibF.Math.InflateCommittedTokens
open ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-- The committed token word replays against every future suffix. Actual
held/raw input is tracked separately by the source Origin identity, so
fast suffix rollback does not have to remove fixed bytes from this ghost. -/
def Committed (L D : List Nat) (dict before : List UInt8) (word : List Bool)
    (current : List UInt8) : Prop :=
  InflateTokenContext.Context L D dict before word current []

theorem Committed.initial (L D : List Nat) (dict history : List UInt8) :
    Committed L D dict history [] history := InflateTokenContext.Context.initial _ _ _ _ _

/-- Every actual accepted non-EOB token contributes its generated finite
word. The grammar assumption remains independent of later validity. -/
theorem Committed.advance {L D : List Nat} {dict before history next : List UInt8}
    {word input rest : List Bool}
    (committed : Committed L D dict before word history)
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (step : Token.Step L D dict history input rest next false) :
    ∃ consumed, input = consumed ++ rest ∧
      Committed L D dict before (word ++ consumed) next := by
  obtain ⟨consumed, source, replay⟩ := TokenSuffix.step_consumed_word lengths distances step
  refine ⟨consumed, source, ?_⟩
  have extended := InflateTokenContext.Context.extend committed consumed
  have exactStep : Token.Step L D dict history consumed [] next false := by
    simpa only [List.append_nil] using replay []
  exact extended.advance (ext_acceptable lengths) (ext_acceptable distances)
    (by simpa only [List.nil_append] using exactStep)

/-- Real EOB reconstructs the independent complete Symbols parse of the
concatenated accepted words, before any physical unread-byte rollback. -/
theorem Committed.finish {L D : List Nat} {dict before history next : List UInt8}
    {word input rest : List Bool}
    (committed : Committed L D dict before word history)
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (step : Token.Step L D dict history input rest next true) :
    ∃ consumed, input = consumed ++ rest ∧ next = history ∧
      Symbols L D dict before (word ++ consumed) [] next := by
  obtain ⟨consumed, source, replay⟩ := TokenSuffix.step_consumed_word lengths distances step
  have extended := InflateTokenContext.Context.extend committed consumed
  have exactStep : Token.Step L D dict history ([] ++ consumed) [] next true := by
    simpa only [List.append_nil, List.nil_append] using replay []
  obtain ⟨same, symbols⟩ := extended.finish exactStep
  exact ⟨consumed, source, same, symbols⟩

theorem Committed.future {L D : List Nat} {dict before history : List UInt8} {word : List Bool}
    (committed : Committed L D dict before word history) (future rest : List Bool) (output : List UInt8) :
    Symbols L D dict before (word ++ future) rest output ↔ Symbols L D dict history future rest output := by
  simpa only [List.nil_append] using committed future rest output

end ZlibF.Math.InflateCommittedTokens
