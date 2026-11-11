import ZlibF.Proof.«inflate.c.return-mode-direct»
import ZlibF.Proof.«inflate.c.return-mode-leave»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Mode correspondence is attached to the actual private record at exit.
The existing state proof supplies its live heap witness. -/
def InflateExitModes (zs : Nat) (exit : Ex) (l : IL) (h : Heap) : Prop :=
  ∃ state, h.istates zs = some state ∧
    (exit = .ret Z_NEED_DICT → state.mode = DICT) ∧
    (exit = .ret Z_MEM_ERROR → state.mode = MEM) ∧
    (exit = .leave → (l.ret = Z_STREAM_END → state.mode = DONE) ∧
      (l.ret = Z_DATA_ERROR → state.mode = BAD))

theorem inflate_dispatch_return_mode_step
    {c : Ctx} {r : ZStreamRef} {zs : Nat}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : RetLoopInv r zs l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => RetLoopInv r zs regs after
    | .error exit => InflateExitModes zs exit regs after := by
  obtain ⟨z, s, bs, invariant, buffers, incoming, initial⟩ := current
  have E : Env c h r zs z s := ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  obtain ⟨otherOutcome, otherRegs, otherHeap, stream, privateState, used, _, _, source,
    final, packet, _, _, _, _, _, bits, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers incoming
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  cases outcome with
  | ok value =>
    cases value
    have normal := (inflate_dispatch_ret_classification E invariant buffers initial run final.good.live.hs).1 rfl
    exact ⟨stream, privateState, bs.drop used, final, packet, bits, normal⟩
  | error exit =>
    refine ⟨privateState, final.good.live.hs, ?_, ?_, ?_⟩
    · intro selected
      subst exit
      exact inflate_dispatch_need_mode E invariant buffers incoming run final.good.live.hs
    · intro selected
      subst exit
      exact inflate_dispatch_memory_mode E invariant buffers incoming run final.good.live.hs
    · intro selected
      subst exit
      exact ⟨fun ended => inflate_dispatch_end_mode E invariant buffers initial run ended final.good.live.hs incoming,
        fun error => inflate_dispatch_data_error_mode E invariant buffers initial run error final.good.live.hs⟩

/-- The complete actual default mode loop returns with the requested
terminal mode correspondence. No mode postcondition is a callee premise. -/
theorem inflate_run_return_modes
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after)) :
    InflateExitModes zs exit regs after := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : RetLoopInv r zs (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits, Or.inl rfl⟩
  rw [cut] at run
  have step : ∀ before heap outcome finalRegs finalHeap, RetLoopInv r zs before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => RetLoopInv r zs finalRegs finalHeap
      | .error exit => InflateExitModes zs exit finalRegs finalHeap := by
    intro before heap outcome finalRegs finalHeap valid source
    have result := inflate_dispatch_return_mode_step E.strm E.st before heap outcome finalRegs finalHeap valid source
    cases outcome with
    | ok value => cases value; exact result
    | error stopped => exact result
  exact xwhile_success_control_post _ _ step start run

#print axioms inflate_run_return_modes
end Zlib.Inflate.Proofs
