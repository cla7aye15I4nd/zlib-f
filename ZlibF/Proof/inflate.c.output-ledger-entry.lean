import ZlibF.Proof.«inflate.c.output-ledger-loop»
import ZlibF.Proof.«inflate.c.default-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real entry establishes the original public output base. The
complete real mode loop conserves total_out plus its changing segment
base, including CHECK's early charging. No counter contract is assumed. -/
theorem inflate_run_default_output_ledger
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (raw : RawFastIO (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((outcome, regs), after))
    (getAfter : r.get after = some stream) :
    stream.total_out + regs.out_.toUInt64 = z.total_out + z.avail_out.toUInt64 := by
  obtain ⟨heap0, state0, bs, entry, current, env0, packet, bits, sizes, frame, heapEq⟩ :=
    inflate_run_default_state_entry E invariant buffers nonnull inputValid
  have currentRaw : RawFastIO (dispatchRegs z state0) := raw
  obtain ⟨exit, regs2, heap2, stream2, state2, used, made, bound, loopRun,
    final, finalPacket, finalRaw, finalBits, finalSizes, next, count, put, left, ledger⟩ :=
    inflate_default_raw_output_loop env0 current packet currentRaw bits
  have executed := entry.symm.trans run
  have same := Except.ok.inj (loopRun.symm.trans executed)
  have sameRegs : regs2 = regs := congrArg (fun pair => pair.1.2) same
  have sameHeap : heap2 = after := congrArg Prod.snd same
  have get2 : r.get after = some stream2 := by
    rw [← sameHeap]
    exact final.good.live.hz
  have sameStream : stream2 = stream := Option.some.inj (get2.symm.trans getAfter)
  rw [sameRegs, sameStream] at ledger
  exact ledger

end Zlib.Inflate.Proofs
