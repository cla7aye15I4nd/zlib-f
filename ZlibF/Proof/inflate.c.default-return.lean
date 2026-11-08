import ZlibF.Proof.«inflate.c.stream-frame-run»
import ZlibF.Proof.«inflate.c.leave-all-wrappers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete default inflate body and its return selection avoid
runtime faults. Direct returns and the full inf_leave path are both covered,
including window allocation failure. Default allocator identity at the return
boundary is proved from actual source execution. This internal result requires
distinct raw input/output blocks. The public entry's local allocation/free,
whole-call frame, ownership and complete history relation remain separate. -/
theorem inflate_default_raw_return {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (raw : RawFastIO (dispatchRegs z s)) :
    ∃ rc after stream state,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ state.hold.toNat < 2 ^ state.bits.toNat := by
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used, made, bound, run, current,
    packet, currentRaw, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_raw_framed E invariant allocator buffers nonnull inputValid raw
  cases exit with
  | ret value =>
    refine ⟨value, heap0, stream0, state0, ?_, current.good, current.tables,
      current.pending, current.held⟩
    rw [bind_app, run]
    rfl
  | leave =>
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have statics : Zlib.Crc32.Proofs.StaticsOK heap0 := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [current.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rc, after, stream, state, leaveRun, finalGood, finalTables,
      finalPending, held, ret, static⟩ :=
      inflate_leave_all_wrappers_boundary currentEnv current.good currentAllocator.1
        statics packet current.tables current.pending bits
    refine ⟨rc, after, stream, state, ?_, finalGood, finalTables, finalPending, held⟩
    rw [bind_app, run]
    exact leaveRun

end Zlib.Inflate.Proofs
