import ZlibF.Proof.«inflate.c.default-mode-result»
import ZlibF.Proof.«inflate.c.output-charge-entry»
import ZlibF.Proof.«inflate.c.leave-memory-source»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete body retains both original lifetime counters on
MEM_ERROR. CHECK's possible early output charge is derived from execution;
its empty terminal segment cannot subsequently fail to allocate a window.
Direct MEM mode is included. No bound on lifetime totals is imposed. -/
theorem inflate_body_default_memory_accounting
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (executed : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (Z_MEM_ERROR, after))
    (getAfter : r.get after = some stream) :
    stream.total_in = z.total_in ∧ stream.total_out = z.total_out := by
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
  have phase := inflate_run_default_output_charge_phase E invariant buffers nonnull inputValid raw run
    current.good.live.hz current.good.live.hs
  cases exit with
  | ret value =>
    rw [bind_app, run] at executed
    have same := Except.ok.inj executed
    have codeEq : value = Z_MEM_ERROR := congrArg Prod.fst same
    have heapEq : heap0 = after := congrArg Prod.snd same
    have currentGet : r.get after = some stream0 := by rw [← heapEq]; exact current.good.live.hz
    have streamEq : stream0 = stream := Option.some.inj (currentGet.symm.trans getAfter)
    have unchanged := inflate_run_input_total E.strm invariant.good.live.hz current.good.live.hz run (by
      intro impossible
      have need : value = Z_NEED_DICT := Ex.ret.inj (Except.error.inj impossible)
      have different : Z_MEM_ERROR ≠ Z_NEED_DICT := by decide
      exact different (codeEq.symm.trans need))
    have direct := inflate_run_default_direct_mode E invariant buffers nonnull inputValid raw run current.good.live.hs
    have mode : state0.mode = MEM := direct.2 codeEq
    have outputTotal : stream0.total_out = z.total_out := by
      rcases phase with unchanged | ⟨_, bad | done⟩
      · exact unchanged
      · have different : MEM ≠ BAD := by decide
        exact False.elim (different (mode.symm.trans bad))
      · have different : MEM ≠ DONE := by decide
        exact False.elim (different (mode.symm.trans done))
    rw [← streamEq]
    exact ⟨unchanged, outputTotal⟩
  | leave =>
    have unchanged := inflate_run_input_total E.strm invariant.good.live.hz current.good.live.hz run
      (by intro impossible; cases impossible)
    have register := inflate_run_default_return_codes E invariant buffers nonnull inputValid raw run
    have notMem : regs.ret ≠ Z_MEM_ERROR := by
      rcases register with equal | equal | equal
      all_goals rw [equal]; decide
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    rw [bind_app, run] at executed
    have nonempty := inflate_leave_memory_nonempty currentEnv current currentAllocator packet bits notMem executed
    have outputTotal : stream0.total_out = z.total_out := by
      rcases phase with unchanged | ⟨empty, _⟩
      · exact unchanged
      · exact False.elim (nonempty empty)
    obtain ⟨rc, heap1, finalStream, state, leaveRun, final, finalAllocator, accounting, counters⟩ :=
      inflate_leave_accounting currentEnv current currentAllocator packet bits fixed invariant.good.live.hz
        next count put left
    have same := Except.ok.inj (leaveRun.symm.trans executed)
    have codeEq : rc = Z_MEM_ERROR := congrArg Prod.fst same
    have heapEq : heap1 = after := congrArg Prod.snd same
    have finalGet : r.get after = some finalStream := by rw [← heapEq]; exact final.good.live.hz
    have streamEq : finalStream = stream := Option.some.inj (finalGet.symm.trans getAfter)
    rcases counters with ⟨_, _, _, selected⟩ | ⟨_, _, inputTotal, finalOutput⟩
    · exact False.elim (leave_selector_not_memory notMem selected codeEq)
    · rw [← streamEq]
      exact ⟨inputTotal.trans unchanged, finalOutput.trans outputTotal⟩

end Zlib.Inflate.Proofs
