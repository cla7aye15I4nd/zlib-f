import ZlibF.Proof.«inflate.c.default-view-return-modes»
import ZlibF.Proof.«inflate.c.default-view-finish-code»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflate(z_streamp strm, int flush)`.
The complete public call returns with J and exact byte accounting on all
public caller byte views and all API returns, including entry refusals,
dictionary requests and memory failure. Ordinary total_in updates are
relative to the original caller, and OK means actual input/output progress. All returned codes belong to the public set, and MEM_ERROR retains the
original input total. The corresponding terminal modes are proved on the actual returned
state. Output totals, frame, ownership and history are separate obligations. -/
theorem inflate_default_view_public_return_modes
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state used made,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧
      StreamAccounting z stream used made ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used) ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧ PublicInflateCode rc ∧
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in) ∧ ReturnedModes rc state := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s, 0, 0,
      ?_, final, allocator, ?_, Nat.zero_le _, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    · simp only [syncBuf, freeWin, upd_same]
    · cases input : z.next_in <;> cases output : z.next_out <;>
        simp [StreamAccounting, advance, input, output]
    · intro _
      simp
    · intro impossible
      exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_OK) impossible)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · intro _
      rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      all_goals intro impossible; exact False.elim (by revert impossible; decide)
  · have accepted : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by
      intro null
      apply rejected
      simp [null]
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    obtain ⟨rc, heap1, stream, state, bytes, used, made, bodyRun, current, finalAllocator,
      localGet, localSize, localRo, usedBound, madeBound, accounting, totals, progress, codes, memoryInput, modes⟩ :=
      inflate_default_view_local_return_modes env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, used, made, ?_, final, finalAllocator, ?_,
      usedBound, madeBound, accounting, totals, progress, codes, memoryInput, modes⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
      rw [bind_app] at bodyRun
      unfold runX at bodyRun
      dsimp only [c] at bodyRun
      erw [bodyRun]
      simp only []
      change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
      rw [bind_app]
      dsimp only [syncBuf]
      rw [freeBuf_run localGet localRo]
      rfl
    · simp only [syncBuf, freeWin, upd_same]

/-- One complete actual default public result: all returned codes and
terminal modes, exact cursors/input totals, memory-error input timing,
OK progress and FINISH exclusion. Output totals/frame/history stay open. -/
theorem inflate_default_view_public_results
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state used made,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧ used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧
      StreamAccounting z stream used made ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used) ∧
      (rc = Z_OK → (used ≠ 0 ∨ made ≠ 0) ∧ flush ≠ Z_FINISH) ∧
      PublicInflateCode rc ∧ (rc = Z_MEM_ERROR → stream.total_in = z.total_in) ∧ ReturnedModes rc state := by
  obtain ⟨rc, after, stream, state, used, made, run, current, finalAllocator,
    localFree, usedBound, madeBound, accounting, inputTotals, progress, codes, memoryInput, modes⟩ :=
    inflate_default_view_public_return_modes invariant allocator buffers flush
  obtain ⟨finishRc, finishHeap, _, _, finishRun, _, _, _, noFinish⟩ :=
    inflate_default_view_finish_code invariant allocator buffers flush
  have sameRc : rc = finishRc := congrArg Prod.fst (Except.ok.inj (run.symm.trans finishRun))
  exact ⟨rc, after, stream, state, used, made, run, current, finalAllocator,
    localFree, usedBound, madeBound, accounting, inputTotals,
    fun ok => ⟨progress ok, noFinish (sameRc.symm.trans ok)⟩, codes, memoryInput, modes⟩

#print axioms inflate_default_view_public_return_modes
#print axioms inflate_default_view_public_results
end Zlib.Inflate.Proofs
