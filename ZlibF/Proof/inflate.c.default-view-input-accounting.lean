import ZlibF.Proof.«inflate.c.default-view-complete-accounting»
import ZlibF.Proof.«inflate.c.input-counter-run»
import ZlibF.Proof.«inflate.c.input-base-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual returning body has exact public byte accounting.
Ordinary returned input totals are relative to the original caller stream,
including the source's distinct immediate dictionary-request exit. -/
theorem inflate_default_view_local_input_accounting
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
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
        stream.total_in = z.total_in + UInt64.ofNat used) := by
  obtain ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting⟩ :=
    inflate_default_view_local_complete_accounting E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, ?_⟩
  intro ordinary
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
    obtain ⟨_, availIn, _, _, outcome⟩ := trace
    have loopInput := InputCounter.inflate_run_leave_input_total E.strm E.st
      invariant.good.live.hz current.good.live.hz run
    have saved := inflate_run_default_view_input_base E invariant buffers nonnull inputValid run
    have count : regs.have_.toNat + used = z.avail_in.toNat := by
      rw [← availIn]
      exact accounting.2.2.1
    have credit : (regs.in_ - regs.have_).toUInt64 = UInt64.ofNat used := by
      rw [saved]
      have cast (value : UInt32) : value.toUInt64 = UInt64.ofNat value.toNat := by simp
      rw [cast, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]
      congr 1
      omega
    rcases outcome with success | failure
    · have credited : stream.total_in = loopZ.total_in + (regs.in_ - regs.have_).toUInt64 := by
        rw [success.2.1]
        rfl
      rw [credited, loopInput, credit]
    · rw [failure.1] at ordinary
      exact False.elim (by revert ordinary; decide)

#print axioms inflate_default_view_local_input_accounting
end Zlib.Inflate.Proofs
