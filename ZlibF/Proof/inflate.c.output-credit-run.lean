import ZlibF.Proof.«inflate.c.output-credit-shape»
import ZlibF.Proof.«inflate.c.output-account-dispatch»
import ZlibF.Proof.«inflate.c.default-view-run»
import ZlibF.Proof.«inflate.c.loop-control-post»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- If output credit already occurred, the only remaining real dispatch
is terminal BAD/DONE with the zero-sized rebased suffix unchanged. -/
theorem inflate_dispatch_output_credit_shape
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {original : UInt64}
    {z stream : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (current : OutputCreditShape original z s l)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (streamGet : r.get after = some stream) (get : after.istates zs = some returned) :
    OutputCreditShape original stream returned regs := by
  rcases current with uncredited | ⟨terminal, zero⟩
  · by_cases check : s.mode = CHECK
    · have result := inflate_CHECK_output_credit_shape E invariant buffers check incoming
        ((inflate_dispatch_CHECK E l check).symm.trans run) streamGet get
      rcases result with unchanged | credited
      · exact Or.inl (unchanged.trans uncredited)
      · exact Or.inr credited
    · have frame := OutputCounter.inflate_dispatch_output_total_noncheck E check run
      exact Or.inl ((frame.total_out E.hz streamGet).trans uncredited)
  · by_cases length : s.mode = LENGTH
    · obtain ⟨_, regs2, _, stream2, state2, _, _, source2, final2, _, _, _, _, _, left2, _, _, _,
        ⟨_, out2, streamFrame, _, _, modes3, _⟩⟩ := inflate_LENGTH_state_rank E invariant buffers length incoming
      have source := (inflate_dispatch_LENGTH E l length).trans source2
      have sameStream := xrun_stream_eq source run final2.good.live.hz streamGet
      have sameState := xrun_state_eq source run final2.good.live.hs get
      have sameRegs := xrun_regs_eq source run
      rw [← sameStream, ← sameState, ← sameRegs]
      right
      refine ⟨?_, ?_⟩
      · rcases modes3 with m | m | m
        · exact Or.inr (Or.inr m)
        · exact Or.inl m
        · exact Or.inr (Or.inl m)
      · rw [out2, left2]
        exact zero
    have mode : TerminalMode s.mode := by
      rcases terminal with bad | done | length'
      · exact Or.inr (Or.inl bad)
      · exact Or.inl done
      · exact absurd length' length
    have source := inflate_dispatch_terminal_run E l mode
    have sameState := xrun_state_eq source run invariant.good.live.hs get
    have sameRegs := xrun_regs_eq source run
    right
    constructor
    · rw [← sameState]
      exact terminal
    · rw [← sameRegs]
      unfold terminalRegs
      split
      · exact zero
      · split <;> exact zero

def OutputCreditLoopInv (c : Ctx) (r : ZStreamRef) (zs : Nat) (original : UInt64) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ HeaderLocal c h r s l ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39 ∧
    OutputCreditShape original z s l

def OutputCreditExit (r : ZStreamRef) (zs : Nat) (original : UInt64) (l : IL) (h : Heap) : Prop :=
  ∃ z s, r.get h = some z ∧ h.istates zs = some s ∧ OutputCreditShape original z s l

theorem inflate_dispatch_output_credit_step
    {c : Ctx} {r : ZStreamRef} {zs : Nat} {original : UInt64}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : OutputCreditLoopInv c r zs original l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => OutputCreditLoopInv c r zs original regs after
    | .error _ => OutputCreditExit r zs original regs after := by
  obtain ⟨z, s, bs, invariant, local_, buffers, incoming, shape⟩ := current
  have E : Env c h r zs z s := ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  obtain ⟨otherOutcome, otherRegs, otherHeap, stream, privateState, used, _, _, source,
    final, ⟨rest, _, packet⟩, _, _, _, _, _, bits, finalLocal, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers local_ incoming
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  have next := inflate_dispatch_output_credit_shape E invariant buffers incoming shape run final.good.live.hz final.good.live.hs
  cases outcome with
  | ok value =>
    cases value
    exact ⟨stream, privateState, rest, final, finalLocal, packet, bits, next⟩
  | error exit => exact ⟨stream, privateState, final.good.live.hz, final.good.live.hs, next⟩

/-- On every actual complete body exit, total_out is original or its CHECK
credit has left a zero-sized terminal suffix. No earlier-call or desired
memory-error contract is assumed. -/
theorem inflate_run_output_credit_shape
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s returned : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after))
    (streamGet : r.get after = some stream) (get : after.istates zs = some returned) :
    OutputCreditShape z.total_out stream returned regs := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, entrySizes, entryFrame, entryHeapEq,
    entryStateEq⟩ := inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant current entrySizes entryFrame entryHeapEq entryStateEq local_
  have start : OutputCreditLoopInv c r zs z.total_out (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, entryLocal, packet, bits, Or.inl rfl⟩
  rw [cut] at run
  have step : ∀ before heap outcome finalRegs finalHeap, OutputCreditLoopInv c r zs z.total_out before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => OutputCreditLoopInv c r zs z.total_out finalRegs finalHeap
      | .error _ => OutputCreditExit r zs z.total_out finalRegs finalHeap := by
    intro before heap outcome finalRegs finalHeap valid source
    have result := inflate_dispatch_output_credit_step E.strm E.st before heap outcome finalRegs finalHeap valid source
    cases outcome with
    | ok value => cases value; exact result
    | error stopped => exact result
  obtain ⟨candidateZ, candidateS, candidateGet, candidateState, shape⟩ :=
    xwhile_success_control_post _ _ step start run
  have sameZ : candidateZ = stream := Option.some.inj (candidateGet.symm.trans streamGet)
  have sameS : candidateS = returned := Option.some.inj (candidateState.symm.trans get)
  rw [sameZ, sameS] at shape
  exact shape

#print axioms inflate_run_output_credit_shape
end Zlib.Inflate.Proofs
