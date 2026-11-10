import ZlibF.Proof.«inflate.c.default-dispatch-result-not-length»
import ZlibF.Proof.«inflate.c.return-mode-run»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual default mode loop never exits with a LENGTH record. This
observer applies to any actual returning loop, not to an invented phase.
It does not assert a complete public history preservation theorem. -/
theorem inflate_run_result_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : RetLoopInv r zs (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits, Or.inl rfl⟩
  rw [cut] at run
  let post : Ex → IL → Heap → Prop := fun _ _ heap =>
    ∃ state, heap.istates zs = some state ∧ state.mode ≠ LENGTH
  have step : ∀ before heap outcome finalRegs finalHeap, RetLoopInv r zs before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => RetLoopInv r zs finalRegs finalHeap
      | .error stopped => post stopped finalRegs finalHeap := by
    intro before heap outcome finalRegs finalHeap valid source
    have classified := inflate_dispatch_return_mode_step E.strm E.st before heap outcome finalRegs finalHeap valid source
    cases outcome with
    | ok value => cases value; exact classified
    | error stopped =>
      obtain ⟨stream, state, input, scope, buffers, incoming, _ret⟩ := valid
      have env : Env c heap r zs stream state := ⟨E.strm, E.st, scope.good.live.hz, scope.good.live.hs⟩
      obtain ⟨otherOutcome, otherRegs, otherHeap, nextZ, nextS, used, made, _, actual,
        final, _packet, _sizes, _next, _have, _put, _left, _bits, _rank⟩ :=
        inflate_dispatch_default_view_state_rank env scope buffers incoming
      have eq := Except.ok.inj (actual.symm.trans source)
      have getS : finalHeap.istates zs = some nextS := by
        have heaps : otherHeap = finalHeap := congrArg Prod.snd eq
        rw [← heaps]
        exact final.good.live.hs
      exact ⟨nextS, getS, inflate_dispatch_result_not_length env scope buffers incoming source getS⟩
  obtain ⟨state, stateGet, excluded⟩ := xwhile_success_control_post _ post step start run
  have same := Option.some.inj (stateGet.symm.trans get)
  simpa only [same] using excluded

#print axioms inflate_run_result_not_length
end Zlib.Inflate.Proofs
