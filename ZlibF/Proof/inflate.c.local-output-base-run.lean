import ZlibF.Proof.«inflate.c.local-output-base-dispatch»
import ZlibF.Proof.«inflate.c.local-run»
import ZlibF.Proof.«inflate.c.loop-control-post»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def OutputBaseLoopInv (cutoff : Nat) (r : ZStreamRef) (zs : Nat) (base : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, LocalStateJ h cutoff r zs z s ∧ DispatchBuffers h r l bs ∧
    l.bits.toNat ≤ 39 ∧ l.out_.toNat ≤ base

/-- Actual dispatch keeps the current output base between the remaining
output count and the original caller capacity. -/
theorem inflate_dispatch_output_base_loop_step
    {c : Ctx} {cutoff : Nat} {r : ZStreamRef} {zs base : Nat}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : OutputBaseLoopInv cutoff r zs base l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => OutputBaseLoopInv cutoff r zs base regs after
    | .error _ => regs.left.toNat ≤ regs.out_.toNat ∧ regs.out_.toNat ≤ base := by
  obtain ⟨z, s, bs, invariant, buffers, incoming, initialBound⟩ := current
  have E : Env c h r zs z s := ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  have lowered := inflate_dispatch_output_base_bound E invariant buffers incoming run
  obtain ⟨otherOutcome, otherRegs, otherHeap, stream, privateState, used, _, _, source,
    final, packet, _, _, _, _, _, bits, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers incoming
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  cases outcome with
  | ok value =>
    cases value
    exact ⟨stream, privateState, bs.drop used, final, packet, bits, by omega⟩
  | error exit => exact ⟨packet.output.count, by omega⟩

/-- The real LOAD saves the original capacity. CHECK's rebases never
increase it, and every actual loop exit retains the lower cursor bound. -/
theorem inflate_run_default_view_output_base
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after)) :
    regs.left.toNat ≤ regs.out_.toNat ∧ regs.out_.toNat ≤ z.avail_out.toNat := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : OutputBaseLoopInv cutoff r zs z.avail_out.toNat (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits, Nat.le_refl _⟩
  rw [cut] at run
  apply xwhile_success_control_post (OutputBaseLoopInv cutoff r zs z.avail_out.toNat)
    (fun _ l _ => l.left.toNat ≤ l.out_.toNat ∧ l.out_.toNat ≤ z.avail_out.toNat) ?_ start run
  intro before heap outcome finalRegs finalHeap valid source
  have result := inflate_dispatch_output_base_loop_step E.strm E.st before heap outcome
    finalRegs finalHeap valid source
  cases outcome with
  | ok value => cases value; exact result
  | error stopped => exact result

#print axioms inflate_run_default_view_output_base
end Zlib.Inflate.Local
