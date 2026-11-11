import ZlibF.Proof.«inflate.c.default-view-input-accounting»
import ZlibF.Proof.«inflate.c.output-base-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual returning body has exact public byte accounting.
Ordinary returned input totals are relative to the original caller stream,
including the source's distinct immediate dictionary-request exit.
An OK return has consumed input or produced output, even after CHECK rebase. -/
theorem inflate_default_view_local_input_progress
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes used made,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧ StreamAccounting z stream used made ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used) ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) := by
  obtain ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals⟩ :=
    inflate_default_view_local_input_accounting E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, ?_⟩
  intro ok
  obtain ⟨otherRc, otherHeap, otherZ, otherS, _, exit, regs, loopHeap, loopZ, loopS,
    used2, made2, source, otherFinal, _, _, _, _, run, current, _, _, _, _, _, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  have same := Except.ok.inj (source.symm.trans bodyRun)
  cases same
  have sameZ : otherZ = stream :=
    Option.some.inj (otherFinal.good.live.hz.symm.trans final.good.live.hz)
  subst otherZ
  cases exit with
  | ret value =>
    obtain ⟨sameRc, _, _, _, allowed⟩ := trace
    have valueEq : value = Z_OK := sameRc.symm.trans ok
    rw [valueEq] at allowed
    exact False.elim (by unfold DirectInflateCode at allowed; revert allowed; decide)
  | leave =>
    obtain ⟨_, availIn, _, availOut, outcome⟩ := trace
    rcases outcome with success | failure
    · have returned := ok.symm.trans success.1
      by_cases inputZero : used = 0
      · right
        intro outputZero
        have savedInput := inflate_run_default_view_input_base E invariant buffers nonnull inputValid run
        obtain ⟨lower, upper⟩ := inflate_run_default_view_output_base E invariant buffers nonnull inputValid local_ run
        have haveEq : regs.have_ = z.avail_in := by
          apply UInt32.toNat_inj.mp
          have count := accounting.2.2.1
          rw [availIn] at count
          omega
        have leftEq : regs.left.toNat = z.avail_out.toNat := by
          have count := accounting.2.2.2.1
          rw [availOut] at count
          omega
        have savedInEq : regs.in_ = regs.have_ := savedInput.trans haveEq.symm
        have savedOutEq : regs.out_ = regs.left := UInt32.toNat_inj.mp (by omega)
        rw [savedInEq, savedOutEq] at returned
        simp only [UInt32.sub_self, beq_self_eq_true, Bool.true_and, Bool.true_or] at returned
        by_cases retEq : regs.ret = Z_OK
        · simp [retEq, Z_OK, Z_BUF_ERROR] at returned
        · have sameRet : Z_OK = regs.ret := by simpa only [retEq, beq_iff_eq, ↓reduceIte] using returned
          exact retEq sameRet.symm
      · exact Or.inl inputZero
    · exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_OK) (failure.1.symm.trans ok))

#print axioms inflate_default_view_local_input_progress
end Zlib.Inflate.Proofs
