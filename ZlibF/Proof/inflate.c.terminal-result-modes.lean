import ZlibF.Proof.«inflate.c.default-progress»
import ZlibF.Proof.«inflate.c.return-meaning-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem DirectInflateCode.not_terminal {rc : Int32} (direct : DirectInflateCode rc) :
    rc ≠ Z_STREAM_END ∧ rc ≠ Z_DATA_ERROR := by
  rcases direct with equal | equal | equal
  all_goals subst rc; decide

theorem LeaveReturnMeaning.end_mode {regs : IL} {state : InflateState}
    (meaning : LeaveReturnMeaning regs state) (ended : regs.ret = Z_STREAM_END) : state.mode = DONE := by
  rcases meaning with zero | finish | bad
  · have different : Z_STREAM_END ≠ Z_OK := by decide
    exact False.elim (different (ended.symm.trans zero))
  · exact finish.2
  · have different : Z_STREAM_END ≠ Z_DATA_ERROR := by decide
    exact False.elim (different (ended.symm.trans bad.1))

theorem LeaveReturnMeaning.data_mode {regs : IL} {state : InflateState}
    (meaning : LeaveReturnMeaning regs state) (failed : regs.ret = Z_DATA_ERROR) : state.mode = BAD := by
  rcases meaning with zero | finish | bad
  · have different : Z_DATA_ERROR ≠ Z_OK := by decide
    exact False.elim (different (failed.symm.trans zero))
  · have different : Z_DATA_ERROR ≠ Z_STREAM_END := by decide
    exact False.elim (different (failed.symm.trans finish.1))
  · exact bad.2

/-- The real selector introduces only BUF_ERROR, so END/DATA_ERROR must
come from the original local register. -/
theorem terminal_selector_register {rc ret : Int32} {test : Prop} [Decidable test]
    (selected : rc = (if test then Z_BUF_ERROR else ret))
    (terminal : rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR) : rc = ret := by
  split at selected
  · rcases terminal with ended | failed
    · have different : Z_STREAM_END ≠ Z_BUF_ERROR := by decide
      exact False.elim (different (ended.symm.trans selected))
    · have different : Z_DATA_ERROR ≠ Z_BUF_ERROR := by decide
      exact False.elim (different (failed.symm.trans selected))
  · exact selected

/-- The complete actual body ties STREAM_END to DONE and DATA_ERROR to
BAD, through the real source loop and the entire inf_leave continuation.
Allocation failure and all direct API returns are accounted separately. -/
theorem inflate_body_default_terminal_modes
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
    (rc = Z_STREAM_END → state.mode = DONE) ∧ (rc = Z_DATA_ERROR → state.mode = BAD) := by
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
    have excluded := DirectInflateCode.not_terminal (codeEq ▸ inflate_run_direct_codes run)
    exact ⟨fun ended => False.elim (excluded.1 ended), fun failed => False.elim (excluded.2 failed)⟩
  | leave =>
    have meaning : LeaveReturnMeaning regs state0 :=
      inflate_run_default_return_meaning E invariant buffers nonnull inputValid raw run current.good.live.hs
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
    rcases counters with ⟨inputTotal, outputTotal, mode, selected⟩ | ⟨memory, rest⟩
    · constructor
      · intro ended
        have ret := terminal_selector_register selected (Or.inl (codeEq.trans ended))
        rw [← stateEq]
        exact mode.trans (meaning.end_mode (ret.symm.trans (codeEq.trans ended)))
      · intro failed
        have ret := terminal_selector_register selected (Or.inr (codeEq.trans failed))
        rw [← stateEq]
        exact mode.trans (meaning.data_mode (ret.symm.trans (codeEq.trans failed)))
    · have direct : DirectInflateCode rc := codeEq ▸ Or.inr (Or.inl memory)
      have excluded := direct.not_terminal
      exact ⟨fun ended => False.elim (excluded.1 ended), fun failed => False.elim (excluded.2 failed)⟩

end Zlib.Inflate.Proofs
