import ZlibF.Proof.«inflate.c.return-default-dispatch»
import ZlibF.Proof.«inflate.c.return-retained»
import ZlibF.Proof.«inflate.c.check-return-shape»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Only a continuing BAD boundary may retain a constructor error code. -/
def ContinuingReturn (regs : IL) (state : InflateState) : Prop :=
  regs.ret = Z_OK ∨ state.mode = BAD

/-- Ordinary leave codes retain their corresponding decoder modes. -/
def LeaveReturnMeaning (regs : IL) (state : InflateState) : Prop :=
  regs.ret = Z_OK ∨ (regs.ret = Z_STREAM_END ∧ state.mode = DONE) ∨
    (regs.ret = Z_DATA_ERROR ∧ state.mode = BAD)

/-- Direct API mode links are a separate obligation. -/
def StepReturnMeaning (outcome : Except Ex Unit) (regs : IL) (state : InflateState) : Prop :=
  match outcome with
  | .ok _ => ContinuingReturn regs state
  | .error .leave => LeaveReturnMeaning regs state
  | .error (.ret _) => True

theorem stepReturnMeaning_zero {outcome : Except Ex Unit} {regs : IL} {state : InflateState}
    (zero : regs.ret = Z_OK) : StepReturnMeaning outcome regs state := by
  cases outcome with
  | ok value => exact Or.inl zero
  | error exit => cases exit <;> first | exact Or.inl zero | trivial

theorem ReturnPhase.return_meaning {outcome : Except Ex Unit} {regs : IL} {state : InflateState}
    (phase : ReturnPhase (fun code => code = Z_OK) outcome regs state) :
    StepReturnMeaning outcome regs state := by
  rcases phase with zero | ⟨normal, bad⟩
  · exact stepReturnMeaning_zero zero
  · rw [normal]
    exact Or.inr bad

theorem CheckReturnShape.return_meaning {s state : InflateState} {l regs : IL}
    {outcome : Except Ex Unit} (shape : CheckReturnShape s l outcome regs state)
    (zero : l.ret = Z_OK) : StepReturnMeaning outcome regs state := by
  rcases shape with ⟨_, ret, _, _⟩ | ⟨_, ret, _, _⟩ | ⟨leave, ret, done, _⟩
  · exact stepReturnMeaning_zero (ret.trans zero)
  · exact stepReturnMeaning_zero (ret.trans zero)
  · rw [leave]
    exact Or.inr (Or.inl ⟨ret, done⟩)

/-- Actual default dispatch establishes the continuing return invariant
and the END/DATA_ERROR mode links on ordinary leave. -/
theorem inflate_dispatch_default_return_meaning
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : ContinuingReturn l s)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) : StepReturnMeaning outcome regs state := by
  by_cases bad : s.mode = BAD
  · have source := inflate_dispatch_terminal_run E l (Or.inr (Or.inl bad))
    have literal : runX (inflate_dispatch c) l h =
        .ok ((.error Ex.leave, { l with ret := Z_DATA_ERROR }), h) := by
      simpa [terminalRegs, terminalExit, bad, DONE, BAD] using source
    have same := Except.ok.inj (literal.symm.trans run)
    have outcomeEq : (.error Ex.leave : Except Ex Unit) = outcome := congrArg (fun pair => pair.1.1) same
    have regsEq : { l with ret := Z_DATA_ERROR } = regs := congrArg (fun pair => pair.1.2) same
    have heapEq : h = after := congrArg Prod.snd same
    have stateEq : s = state := Option.some.inj ((heapEq ▸ E.hs).symm.trans getAfter)
    rw [← outcomeEq, ← regsEq, ← stateEq]
    exact Or.inr (Or.inr ⟨rfl, bad⟩)
  have zero : l.ret = Z_OK := incoming.resolve_right bad
  by_cases done : s.mode = DONE
  · have source := inflate_dispatch_terminal_run E l (Or.inl done)
    have literal : runX (inflate_dispatch c) l h =
        .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), h) := by
      simpa [terminalRegs, terminalExit, done, DONE, BAD] using source
    have same := Except.ok.inj (literal.symm.trans run)
    have outcomeEq : (.error Ex.leave : Except Ex Unit) = outcome := congrArg (fun pair => pair.1.1) same
    have regsEq : { l with ret := Z_STREAM_END } = regs := congrArg (fun pair => pair.1.2) same
    have heapEq : h = after := congrArg Prod.snd same
    have stateEq : s = state := Option.some.inj ((heapEq ▸ E.hs).symm.trans getAfter)
    rw [← outcomeEq, ← regsEq, ← stateEq]
    exact Or.inr (Or.inl ⟨rfl, done⟩)
  by_cases check : s.mode = CHECK
  · exact (inflate_CHECK_default_return_shape E invariant buffers check
      ((inflate_dispatch_CHECK E l check).symm.trans run) getAfter).return_meaning zero
  by_cases length : s.mode = LENGTH
  · obtain ⟨source, final, _, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
    have same := Except.ok.inj (((inflate_dispatch_LENGTH E l length).trans source).symm.trans run)
    have outcomeEq : (.error Ex.leave : Except Ex Unit) = outcome := congrArg (fun pair => pair.1.1) same
    have regsEq : { l with ret := Z_STREAM_END } = regs := congrArg (fun pair => pair.1.2) same
    have heapEq : setI h zs { s with mode := DONE } = after := congrArg Prod.snd same
    have stateEq : { s with mode := DONE } = state :=
      Option.some.inj ((heapEq ▸ final.good.live.hs).symm.trans getAfter)
    rw [← outcomeEq, ← regsEq, ← stateEq]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  by_cases codes : s.mode = CODELENS
  · exact (inflate_CODELENS_return_phase (allowed := fun code => code = Z_OK) rfl E invariant.toDefaultDecodeJ buffers codes zero
      ((inflate_dispatch_CODELENS E l codes).symm.trans run) getAfter).return_meaning
  by_cases lengths : s.mode = LENLENS
  · exact (inflate_LENLENS_return_phase (allowed := fun code => code = Z_OK) rfl E invariant.toDefaultDecodeJ buffers lengths zero
      ((inflate_dispatch_LENLENS E l lengths).symm.trans run) getAfter).return_meaning
  by_cases table : s.mode = TABLE
  · exact (inflate_TABLE_return_phase (allowed := fun code => code = Z_OK) rfl E invariant.toDefaultDecodeJ buffers table zero
      ((inflate_dispatch_TABLE E l table).symm.trans run) getAfter).return_meaning
  have retained := inflate_dispatch_regular_retained E table lengths codes check length done bad run
  exact stepReturnMeaning_zero (retained.trans zero)

end Zlib.Inflate.Proofs
