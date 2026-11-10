import ZlibF.Proof.«inflate.c.output-charge-loop»
import ZlibF.Proof.«inflate.c.default-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real entry and complete mode loop preserve the early-charge phase.
The original lifetime total is retained unless CHECK leaves an empty
terminal segment. No counter contract is assumed. -/
theorem inflate_run_default_output_charge_phase
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (raw : RawFastIO (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((outcome, regs), after))
    (getAfter : r.get after = some stream) (getState : after.istates zs = some state) :
    OutputChargePhase z.total_out regs stream state := by
  obtain ⟨heap0, state0, bs, entry, current, env0, packet, bits, sizes, frame, heapEq⟩ :=
    inflate_run_default_state_entry E invariant buffers nonnull inputValid
  have currentRaw : RawFastIO (dispatchRegs z state0) := raw
  obtain ⟨exit, regs2, heap2, stream2, state2, used, made, bound, loopRun,
    final, finalPacket, finalRaw, finalBits, finalSizes, next, count, put, left, phase⟩ :=
    inflate_default_raw_output_charge_loop env0 current packet currentRaw bits
  have executed := entry.symm.trans run
  have same := Except.ok.inj (loopRun.symm.trans executed)
  have sameRegs : regs2 = regs := congrArg (fun pair => pair.1.2) same
  have sameHeap : heap2 = after := congrArg Prod.snd same
  have get2 : r.get after = some stream2 := by
    rw [← sameHeap]
    exact final.good.live.hz
  have sameStream : stream2 = stream := Option.some.inj (get2.symm.trans getAfter)
  have stateGet : after.istates zs = some state2 := by
    rw [← sameHeap]
    exact final.good.live.hs
  have sameState : state2 = state := Option.some.inj (stateGet.symm.trans getState)
  rwa [sameRegs, sameStream, sameState] at phase

end Zlib.Inflate.Proofs
