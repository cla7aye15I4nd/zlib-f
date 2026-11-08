import ZlibF.Proof.«inflate.c.default-view-return-accounting»
import ZlibF.Proof.«inflate.c.default-view-finish-code»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflate(z_streamp strm, int flush)`.
The complete public call returns with J and bounded byte counts on all
public caller byte views. Every ordinary leave has full StreamAccounting;
the separate direct API exits remain explicitly classified. This does not
close direct-exit accounting, public totals, frame, ownership or history. -/
theorem inflate_default_view_public_accounting
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state used made,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧
      (DirectInflateCode rc ∨ StreamAccounting z stream used made) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s, 0, 0,
      ?_, final, allocator, ?_, Nat.zero_le _, Nat.zero_le _, Or.inl (Or.inr (Or.inr rfl))⟩
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
      localGet, localSize, localRo, usedBound, madeBound, accounting⟩ :=
      inflate_default_view_local_accounting env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, used, made, ?_, final, finalAllocator, ?_,
      usedBound, madeBound, accounting⟩
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

/-- `int inflate(z_streamp strm, int flush)`.
For all admitted default states and caller byte views, the complete actual
call preserves J and local cleanup. OK, END, DATA_ERROR and BUF_ERROR have
exact public byte accounting. OK cannot occur with Z_FINISH. Accounting for
NEED_DICT, STREAM_ERROR and direct MEM exits remains open. -/
theorem inflate_default_view_ordinary_accounting
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state used made,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧ used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        StreamAccounting z stream used made) ∧ (rc = Z_OK → flush ≠ Z_FINISH) := by
  obtain ⟨rc, after, stream, state, used, made, run, final, finalAllocator,
    freeLocal, usedBound, madeBound, partialAccounting⟩ :=
    inflate_default_view_public_accounting invariant allocator buffers flush
  obtain ⟨finishRc, finishHeap, _, _, finishRun, _, _, _, noFinish⟩ :=
    inflate_default_view_finish_code invariant allocator buffers flush
  have sameRc : rc = finishRc :=
    congrArg Prod.fst (Except.ok.inj (run.symm.trans finishRun))
  refine ⟨rc, after, stream, state, used, made, run, final, finalAllocator,
    freeLocal, usedBound, madeBound, ?_, fun ok => noFinish (sameRc.symm.trans ok)⟩
  intro ordinary
  rcases partialAccounting with direct | accounting
  · rcases ordinary with rfl | rfl | rfl | rfl
    all_goals exact False.elim (by revert direct; unfold DirectInflateCode; decide)
  · exact accounting

#print axioms inflate_default_view_public_accounting
#print axioms inflate_default_view_ordinary_accounting
end Zlib.Inflate.Proofs
