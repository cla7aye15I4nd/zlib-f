import ZlibF.Proof.Format.Token
import ZlibF.Proof.Format.Deflate
import ZlibF.Math.InflateBlockContext

namespace ZlibF.Math.InflateTokenContext
open ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-- A committed token prefix is equivalent for every unread bit suffix.
No valid completion is required to exist. -/
def Context (L D : List Nat) (dict originalOutput : List UInt8)
    (originalInput : List Bool) (currentOutput : List UInt8) (currentInput : List Bool) : Prop :=
  ∀ (future rest : List Bool) (output : List UInt8),
    Symbols L D dict originalOutput (originalInput ++ future) rest output ↔
      Symbols L D dict currentOutput (currentInput ++ future) rest output

theorem Context.initial (L D : List Nat) (dict history : List UInt8) (input : List Bool) :
    Context L D dict history input history input := by intro _ _ _; rfl

theorem Context.trans {L D : List Nat} {dict original middle current : List UInt8}
    {input middleBits currentBits : List Bool}
    (first : Context L D dict original input middle middleBits)
    (second : Context L D dict middle middleBits current currentBits) :
    Context L D dict original input current currentBits := by
  intro future rest output
  exact (first future rest output).trans (second future rest output)

theorem Context.extend {L D : List Nat} {dict original current : List UInt8}
    {input currentBits : List Bool}
    (context : Context L D dict original input current currentBits) (bits : List Bool) :
    Context L D dict original (input ++ bits) current (currentBits ++ bits) := by
  intro future rest output
  simpa only [List.append_assoc] using context (bits ++ future) rest output

theorem step_append {L D : List Nat} {dict history next : List UInt8}
    {input rest : List Bool} {ended : Bool} (hL : Ext L) (hD : Ext D)
    (step : Token.Step L D dict history input rest next ended) (future : List Bool) :
    Token.Step L D dict history (input ++ future) (rest ++ future) next ended := by
  cases step with
  | literal decoded small => exact .literal (hL _ _ _ _ decoded) small
  | copy decoded lower upper lengthRead distanceDecoded bound distanceRead fits =>
    exact .copy (hL _ _ _ _ decoded) lower upper (readBits_append _ _ _ _ _ lengthRead)
      (hD _ _ _ _ distanceDecoded) bound (readBits_append _ _ _ _ _ distanceRead) fits
  | eob decoded => exact .eob (hL _ _ _ _ decoded)

/-- Deterministic accepted reads permit removing a committed non-EOB token
from the original Symbols relation, even if the remaining input is invalid. -/
theorem nonfinal_step_iff {L D : List Nat} {dict history next output : List UInt8}
    {input nextBits rest : List Bool}
    (step : Token.Step L D dict history input nextBits next false) :
    Symbols L D dict history input rest output ↔ Symbols L D dict next nextBits rest output := by
  constructor
  · intro parsed
    cases step with
    | literal decoded small =>
      cases parsed with
      | eob other =>
        have same := (Prod.mk.inj (Option.some.inj (decoded.symm.trans other))).1
        omega
      | lit other _ continuation =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (decoded.symm.trans other))
        exact continuation
      | copy other lower _ _ _ _ _ _ _ =>
        have same := (Prod.mk.inj (Option.some.inj (decoded.symm.trans other))).1
        omega
    | copy decoded lower upper lengthRead distanceDecoded bound distanceRead fits =>
      cases parsed with
      | eob other =>
        have same := (Prod.mk.inj (Option.some.inj (decoded.symm.trans other))).1
        omega
      | lit other small _ =>
        have same := (Prod.mk.inj (Option.some.inj (decoded.symm.trans other))).1
        omega
      | copy other _ _ otherLength otherDistance _ otherExtra _ continuation =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (decoded.symm.trans other))
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (lengthRead.symm.trans otherLength))
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (distanceDecoded.symm.trans otherDistance))
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (distanceRead.symm.trans otherExtra))
        exact continuation
  · intro continuation
    exact (Token.step_composes_symbols _ _ _ _ _ _ _ _ step).2 rfl _ _ continuation

theorem Context.advance {L D : List Nat} {dict original current next : List UInt8}
    {input currentBits nextBits : List Bool}
    (context : Context L D dict original input current currentBits)
    (hL : Ext L) (hD : Ext D)
    (step : Token.Step L D dict current currentBits nextBits next false) :
    Context L D dict original input next nextBits := by
  intro future rest output
  exact (context future rest output).trans (nonfinal_step_iff (step_append hL hD step future))

theorem Context.finish {L D : List Nat} {dict original current next : List UInt8}
    {input currentBits rest : List Bool}
    (context : Context L D dict original input current currentBits)
    (step : Token.Step L D dict current currentBits rest next true) :
    next = current ∧ Symbols L D dict original input rest next := by
  obtain ⟨same, parsed⟩ := (Token.step_composes_symbols _ _ _ _ _ _ _ _ step).1 rfl
  have currentParsed : Symbols L D dict current (currentBits ++ []) rest next := by
    simpa only [List.append_nil] using parsed
  exact ⟨same, by simpa only [List.append_nil] using (context [] rest next).mpr currentParsed⟩

theorem Context.valid_source {L D : List Nat} {dict original current output : List UInt8}
    {input currentBits future rest : List Bool}
    (context : Context L D dict original input current currentBits)
    (parsed : Symbols L D dict original (input ++ future) rest output) :
    Symbols L D dict current (currentBits ++ future) rest output ∧ current <+: output := by
  have remaining := (context future rest output).mp parsed
  exact ⟨remaining, InflateBlockContext.symbols_history_prefix remaining⟩

end ZlibF.Math.InflateTokenContext
