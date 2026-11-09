import ZlibF.Proof.«inflate.c.local-return-codes»
import ZlibF.Proof.«inflate.c.local-output-account-run»
import ZlibF.Math.InflateOutputAccount

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete returning body has both original-caller totals on
ordinary returns. CHECK's real earlier credit is included exactly once.
Memory-error output timing remains a separate clause to establish. -/
theorem inflate_default_view_local_output_accounting
    {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes used made,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧ StreamAccounting z stream used made ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used ∧
        stream.total_out = z.total_out + UInt64.ofNat made) ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧ PublicInflateCode rc ∧
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in) := by
  obtain ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, inputTotals, progress, codes, memoryInput⟩ :=
    inflate_default_view_local_return_codes E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, ?_, progress, codes, memoryInput⟩
  intro ordinary
  refine ⟨inputTotals ordinary, ?_⟩
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
    rw [sameRc] at ordinary
    rcases ordinary with rfl | rfl | rfl | rfl
    all_goals exact False.elim (by unfold DirectInflateCode at allowed; revert allowed; decide)
  | leave =>
    obtain ⟨_, _, _, availOut, outcome⟩ := trace
    have account := OutputCounter.inflate_run_output_account E invariant buffers nonnull inputValid run
      current.good.live.hz
    obtain ⟨lower, _⟩ := inflate_run_default_view_output_base E invariant buffers nonnull inputValid run
    have count : regs.left.toNat + made = z.avail_out.toNat := by
      rw [← availOut]
      exact accounting.2.2.2.1
    rcases outcome with success | failure
    · have suffix : stream.total_out = loopZ.total_out + (regs.out_ - regs.left).toUInt64 := by
        rw [success.2.1]
        rfl
      rw [suffix]
      exact ZlibF.Math.InflateOutputAccount.suffix_credit account lower count
    · rw [failure.1] at ordinary
      exact False.elim (by revert ordinary; decide)

#print axioms inflate_default_view_local_output_accounting
end Zlib.Inflate.Local
