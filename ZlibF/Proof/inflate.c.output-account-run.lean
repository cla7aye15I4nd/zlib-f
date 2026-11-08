import ZlibF.Proof.«inflate.c.output-account-dispatch»
import ZlibF.Proof.«inflate.c.default-view-run»
import ZlibF.Proof.«inflate.c.loop-control-post»

namespace Zlib.Inflate.Proofs.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A ghost account for the actual stream total and its saved output base.
All arithmetic is the source's wrapping 64-bit arithmetic. -/
def OutputAccountLoopInv (r : ZStreamRef) (zs : Nat) (total : UInt64) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39 ∧
    z.total_out + l.out_.toUInt64 = total

def OutputAccountExit (r : ZStreamRef) (total : UInt64) (l : IL) (h : Heap) : Prop :=
  ∃ z, r.get h = some z ∧ z.total_out + l.out_.toUInt64 = total

theorem inflate_dispatch_output_account_step
    {c : Ctx} {r : ZStreamRef} {zs : Nat} {total : UInt64}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : OutputAccountLoopInv r zs total l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => OutputAccountLoopInv r zs total regs after
    | .error _ => OutputAccountExit r total regs after := by
  obtain ⟨z, s, bs, invariant, buffers, incoming, account⟩ := current
  have E : Env c h r zs z s := ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  obtain ⟨otherOutcome, otherRegs, otherHeap, stream, privateState, used, _, _, source,
    final, packet, _, _, _, _, _, bits, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers incoming
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  have next := (inflate_dispatch_output_account E invariant buffers incoming run final.good.live.hz).trans account
  cases outcome with
  | ok value =>
    cases value
    exact ⟨stream, privateState, bs.drop used, final, packet, bits, next⟩
  | error exit => exact ⟨stream, final.good.live.hz, next⟩

/-- The real entry saves the original caller capacity. Every source mode,
including early DICT return and CHECK credit, preserves this same account. -/
theorem inflate_run_output_account
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after))
    (get : r.get after = some stream) :
    stream.total_out + regs.out_.toUInt64 = z.total_out + z.avail_out.toUInt64 := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : OutputAccountLoopInv r zs (z.total_out + z.avail_out.toUInt64)
      (dispatchRegs z entryState) entryHeap := ⟨z, entryState, bs, current, packet, bits, rfl⟩
  rw [cut] at run
  have step : ∀ before heap outcome finalRegs finalHeap,
      OutputAccountLoopInv r zs (z.total_out + z.avail_out.toUInt64) before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => OutputAccountLoopInv r zs (z.total_out + z.avail_out.toUInt64) finalRegs finalHeap
      | .error _ => OutputAccountExit r (z.total_out + z.avail_out.toUInt64) finalRegs finalHeap := by
    intro before heap outcome finalRegs finalHeap valid source
    have result := inflate_dispatch_output_account_step E.strm E.st before heap outcome
      finalRegs finalHeap valid source
    cases outcome with
    | ok value => cases value; exact result
    | error stopped => exact result
  obtain ⟨candidate, candidateGet, account⟩ := xwhile_success_control_post _ _ step start run
  have same : candidate = stream := Option.some.inj (candidateGet.symm.trans get)
  rw [same] at account
  exact account

#print axioms inflate_run_output_account
end Zlib.Inflate.Proofs.OutputCounter
