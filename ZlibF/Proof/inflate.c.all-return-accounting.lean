import ZlibF.Proof.«inflate.c.direct-cursor-entry»
import ZlibF.Proof.«inflate.c.default-memory»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Published local cursors and the actual fixed-field source frame give
the full public accounting relation, including direct dictionary exits. -/
theorem restoredCursors_accounting
    {h after : Heap} {r : ZStreamRef} {before stream : ZStream} {regs : IL} {used made : Nat}
    (frame : StreamRootFrame r h after) (beforeGet : r.get h = some before)
    (currentGet : r.get after = some stream) (restored : RestoredCursors stream regs)
    (next : regs.next = inputAdvance before.next_in used)
    (input : regs.have_.toNat + used = before.avail_in.toNat)
    (put : regs.put = inputAdvance before.next_out made)
    (output : regs.left.toNat + made = before.avail_out.toNat) :
    StreamAccounting before stream used made := by
  obtain ⟨state, alloc, free, opaqueArg, reserved⟩ := frame.fields beforeGet currentGet
  obtain ⟨cursorIn, countIn, cursorOut, countOut⟩ := restored
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, state, alloc, free, opaqueArg, reserved⟩
  · rw [countIn]
    exact input
  · rw [countOut]
    exact output
  · exact cursorIn.trans next
  · exact cursorOut.trans put

/-- A direct terminal entry accepts and publishes no bytes. -/
theorem streamAccounting_self (z : ZStream) : StreamAccounting z z 0 0 := by
  exact ⟨by omega, by omega, by omega, by omega,
    (inputAdvance_zero z.next_in).symm, (inputAdvance_zero z.next_out).symm,
    rfl, rfl, rfl, rfl, rfl⟩

/-- The actual complete default body has public cursor/count accounting
on every return code. DICT publishes its final local cursors. Other direct
entries retain the original stream. Window allocation failure still runs
RESTORE and therefore retains the loop's exact consumed/produced counts.
No lifetime counter conclusion is asserted by this separate lemma. -/
theorem inflate_body_default_all_return_accounting
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s)) :
    ∃ rc after stream state, ∃ used made : Nat,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ StreamAccounting z stream used made := by
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
    have published := inflate_run_default_direct_cursors E invariant buffers nonnull inputValid raw run current.good.live.hz
    by_cases needed : value = Z_NEED_DICT
    · refine ⟨value, heap0, stream0, state0, used, made, ?_, current, currentAllocator, ?_⟩
      · rw [bind_app, run]
        rfl
      · exact restoredCursors_accounting fixed invariant.good.live.hz current.good.live.hz
          (published.1 needed) next count put left
    · refine ⟨value, heap0, stream0, state0, 0, 0, ?_, current, currentAllocator, ?_⟩
      · rw [bind_app, run]
        rfl
      · rw [published.2 needed]
        exact streamAccounting_self z
  | leave =>
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨rc, after, stream, state, leaveRun, final, finalAllocator, accounting, counters⟩ :=
      inflate_leave_accounting currentEnv current currentAllocator packet bits fixed invariant.good.live.hz
        next count put left
    refine ⟨rc, after, stream, state, used, made, ?_, final, finalAllocator, accounting⟩
    rw [bind_app, run]
    exact leaveRun

end Zlib.Inflate.Proofs
