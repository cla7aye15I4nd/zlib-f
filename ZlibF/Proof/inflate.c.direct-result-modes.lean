import ZlibF.Proof.«inflate.c.default-terminal»
import ZlibF.Proof.«inflate.c.direct-mode-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- NEED_DICT and MEM_ERROR retain DICT and MEM on the actual body run.
The latter includes failure in the real inf_leave window update. -/
theorem inflate_body_default_direct_modes
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (bodyRun : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (getAfter : after.istates zs = some state) :
    (rc = Z_NEED_DICT → state.mode = DICT) ∧ (rc = Z_MEM_ERROR → state.mode = MEM) := by
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
    have direct := inflate_run_default_direct_mode E invariant buffers nonnull inputValid raw run current.good.live.hs
    rw [bind_app, run] at bodyRun
    have same := Except.ok.inj bodyRun
    have codeEq : value = rc := congrArg Prod.fst same
    have heapEq : heap0 = after := congrArg Prod.snd same
    have currentGet : after.istates zs = some state0 := by rw [← heapEq]; exact current.good.live.hs
    have stateEq : state0 = state := Option.some.inj (currentGet.symm.trans getAfter)
    constructor
    · intro needed
      rw [← stateEq]
      exact direct.1 (codeEq.trans needed)
    · intro memory
      rw [← stateEq]
      exact direct.2 (codeEq.trans memory)
  | leave =>
    have register := inflate_run_default_return_codes E invariant buffers nonnull inputValid raw run
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨code, heap1, stream, actualState, leaveRun, final, finalAllocator, accounting, counters⟩ :=
      inflate_leave_accounting currentEnv current currentAllocator packet bits fixed invariant.good.live.hz
        next count put left
    rw [bind_app, run] at bodyRun
    have same := Except.ok.inj (leaveRun.symm.trans bodyRun)
    have codeEq : code = rc := congrArg Prod.fst same
    have heapEq : heap1 = after := congrArg Prod.snd same
    have actualGet : after.istates zs = some actualState := by rw [← heapEq]; exact final.good.live.hs
    have stateEq : actualState = state := Option.some.inj (actualGet.symm.trans getAfter)
    rcases counters with ⟨inputTotal, outputTotal, mode, selected⟩ | ⟨memory, mode, inputTotal, outputTotal⟩
    · have normal := leaveReturn_code_range (snapshot := leaveStream stream0 regs) register selected
      have excluded := normalInflateCode_not_direct normal
      exact ⟨fun needed => False.elim (excluded.1 (codeEq.trans needed)),
        fun memory => False.elim (excluded.2.1 (codeEq.trans memory))⟩
    · constructor
      · intro needed
        have different : Z_MEM_ERROR ≠ Z_NEED_DICT := by decide
        exact False.elim (different (memory.symm.trans (codeEq.trans needed)))
      · intro _
        rw [← stateEq]
        exact mode

end Zlib.Inflate.Proofs
