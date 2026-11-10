import ZlibF.Proof.«inflate.c.return-meaning-loop»
import ZlibF.Proof.«inflate.c.default-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual entry initializes the continuing phase at ret = OK. The
complete actual loop ties each ordinary terminal code to its decoder mode. -/
theorem inflate_run_default_return_meaning
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (raw : RawFastIO (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) : StepReturnMeaning outcome regs state := by
  obtain ⟨heap0, state0, bs, entry, current, env0, packet, bits, sizes, frame, heapEq⟩ :=
    inflate_run_default_state_entry E invariant buffers nonnull inputValid
  have currentRaw : RawFastIO (dispatchRegs z state0) := raw
  obtain ⟨exit, regs2, heap2, stream2, state2, used, made, bound, loopRun,
    final, finalPacket, finalRaw, finalBits, finalSizes, next, count, put, left, code⟩ :=
    inflate_default_raw_meaning_loop env0 current packet currentRaw bits (Or.inl rfl)
  have executed := entry.symm.trans run
  have same := Except.ok.inj (loopRun.symm.trans executed)
  have sameRegs : regs2 = regs := congrArg (fun pair => pair.1.2) same
  have outcomeEq : (.error exit : Except Ex Unit) = outcome := congrArg (fun pair => pair.1.1) same
  have heapEq : heap2 = after := congrArg Prod.snd same
  have currentGet : after.istates zs = some state2 := by rw [← heapEq]; exact final.good.live.hs
  have stateEq : state2 = state := Option.some.inj (currentGet.symm.trans getAfter)
  simpa only [sameRegs, outcomeEq, stateEq] using code

end Zlib.Inflate.Proofs
