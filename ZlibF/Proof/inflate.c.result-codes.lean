import ZlibF.Proof.«inflate.c.return-entry»
import ZlibF.Proof.«inflate.c.counter-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The four ordinary inf_leave results and the three actual direct/error
results of the public source. This is a proved range, not a caller premise. -/
def InflateResultCode (code : Int32) : Prop :=
  (code = Z_OK ∨ code = Z_STREAM_END ∨ code = Z_DATA_ERROR ∨ code = Z_BUF_ERROR) ∨
    DirectInflateCode code

/-- The complete actual body has one of the seven public return codes.
The actual entry/loop establishes its local register range; direct exits
and window allocation failure are handled by their source theorems. -/
theorem inflate_body_default_return_code
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (bodyRun : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after)) : InflateResultCode rc := by
  obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw
  have nonnull : z.next_out ≠ .null := by
    change z.next_out = .ref (.blk ob) oo at output
    rw [output]
    simp
  have inputValid : z.next_in = .null → z.avail_in = 0 := by
    change z.next_in = .ref (.blk ib) io at input
    rw [input]
    intro impossible
    cases impossible
  have raw : RawFastIO (dispatchRegs z s) := ⟨ib, io, ob, oo, input, output, different⟩
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used, made, bound, run, current,
    packet, currentRaw, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_raw_framed E invariant allocator buffers nonnull inputValid raw
  cases exit with
  | ret value =>
    rw [bind_app, run] at bodyRun
    have codeEq : value = rc := congrArg Prod.fst (Except.ok.inj bodyRun)
    rw [← codeEq]
    exact Or.inr (inflate_run_direct_codes run)
  | leave =>
    have register := inflate_run_default_return_codes E invariant buffers nonnull inputValid raw run
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨code, heap1, stream, state, leaveRun, final, finalAllocator, accounting, counters⟩ :=
      inflate_leave_accounting currentEnv current currentAllocator packet bits fixed invariant.good.live.hz
        next count put left
    rw [bind_app, run] at bodyRun
    have codeEq : code = rc := congrArg Prod.fst (Except.ok.inj (leaveRun.symm.trans bodyRun))
    rw [← codeEq]
    rcases counters with ⟨inputTotal, outputTotal, mode, selected⟩ | ⟨memory, rest⟩
    · exact Or.inl (leaveReturn_code_range (snapshot := leaveStream stream0 regs) register selected)
    · exact Or.inr (Or.inr (Or.inl memory))

end Zlib.Inflate.Proofs
