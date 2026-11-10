import ZlibF.Proof.«inflate.c.default-result»
import ZlibF.Proof.«inflate.c.output-base-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An actual OK body return has original-call input or output progress
and a non-FINISH flush. The source entry supplies the input base, and the
entire actual loop supplies the upper bound on CHECK's output base. The
accounting argument is the already proved result on this same execution. -/
theorem inflate_body_default_ok_progress
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {used made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (bodyRun : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (Z_OK, after))
    (getAfter : r.get after = some stream) (accounting : StreamAccounting z stream used made) :
    (used ≠ 0 ∨ made ≠ 0) ∧ c.flush ≠ Z_FINISH := by
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
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used0, made0, bound, run, current,
    packet, currentRaw, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_raw_framed E invariant allocator buffers nonnull inputValid raw
  cases exit with
  | ret value =>
    rw [bind_app, run] at bodyRun
    have codeEq : value = Z_OK := congrArg Prod.fst (Except.ok.inj bodyRun)
    have direct : DirectInflateCode Z_OK := codeEq ▸ inflate_run_direct_codes run
    obtain ⟨noNeed, noMem, noStream⟩ := normalInflateCode_not_direct (rc := Z_OK) (Or.inl rfl)
    rcases direct with needed | memory | streamError
    · exact False.elim (noNeed needed)
    · exact False.elim (noMem memory)
    · exact False.elim (noStream streamError)
  | leave =>
    have base := inflate_run_default_input_base E invariant buffers nonnull inputValid run
    have upper := inflate_run_default_output_base_le E invariant buffers nonnull inputValid raw run
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨code, heap1, actual, state, leaveRun, final, finalAllocator, actualAccounting, counters⟩ :=
      inflate_leave_accounting currentEnv current currentAllocator packet bits fixed invariant.good.live.hz
        next count put left
    rw [bind_app, run] at bodyRun
    have same := Except.ok.inj (leaveRun.symm.trans bodyRun)
    have codeEq : code = Z_OK := congrArg Prod.fst same
    have heapEq : heap1 = after := congrArg Prod.snd same
    have actualGet : r.get after = some actual := by rw [← heapEq]; exact final.good.live.hz
    have streamEq : actual = stream := Option.some.inj (actualGet.symm.trans getAfter)
    rw [streamEq] at actualAccounting
    have usedEq : used0 = used := by
      have realCount := actualAccounting.2.2.1
      have callerCount := accounting.2.2.1
      omega
    have madeEq : made0 = made := by
      have realCount := actualAccounting.2.2.2.1
      have callerCount := accounting.2.2.2.1
      omega
    rcases counters with ⟨inputTotal, outputTotal, mode, selected⟩ | ⟨memory, rest⟩
    · obtain ⟨retOK, nonFinish, progress⟩ :=
        leaveReturn_ok_facts (snapshot := leaveStream stream0 regs) selected codeEq
      refine ⟨?_, nonFinish⟩
      rcases progress with inputProgress | outputProgress
      · left
        intro usedZero
        have remaining : regs.have_ = z.avail_in := UInt32.toNat_inj.mp (by omega)
        change regs.in_ - regs.have_ ≠ 0 at inputProgress
        apply inputProgress
        rw [base, remaining, UInt32.sub_self]
      · right
        intro madeZero
        have remaining := packet.output.count
        have sameBase : regs.out_ = regs.left := UInt32.toNat_inj.mp (by omega)
        change regs.out_ - regs.left ≠ 0 at outputProgress
        apply outputProgress
        rw [sameBase, UInt32.sub_self]
    · have different : Z_OK ≠ Z_MEM_ERROR := by decide
      exact False.elim (different (codeEq.symm.trans memory))

end Zlib.Inflate.Proofs
