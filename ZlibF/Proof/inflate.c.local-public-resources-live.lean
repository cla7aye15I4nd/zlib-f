import ZlibF.Proof.«inflate.c.local-public-resources-live-body»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflate(z_streamp strm, int flush)`.
The complete actual default call preserves every previously live allocation.
Every new live allocation is precisely a returned owned decoder object.
The real four-byte temporary allocation and free cancel from that ledger.
This is the allocation clause, not the exact memory-content frame or history theorem. -/
theorem inflate_default_view_public_live
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧
      LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
  have stateLive : h.live zs := by simp [Heap.live, invariant.good.live.hs]
  have localAge : cutoff ≤ h.nextBlk := Nat.le_trans invariant.roots.state (Nat.le_of_lt (invariant.good.fresh.lt stateLive))
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s,
      ?_, final, allocator, ?_, ?_⟩
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
    · have ledger : LiveChange (syncAlloc h) (syncAlloc h)
          (fun b => InflateOwned zs s b ∧ ¬ (syncAlloc h).live b) (fun _ => False) :=
        local_live_change_of_eq allocated.good rfl
      exact public_live_cancel_local invariant.good.fresh localAge allocated
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) ledger
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
    obtain ⟨rc, heap1, stream, state, bytes, bodyRun, current, finalAllocator,
      localGet, localSize, localRo⟩ :=
      inflate_default_view_local_state_return env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have ledger := inflate_default_view_local_live_public env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid bodyRun current.good
    have publicLedger := public_live_cancel_local invariant.good.fresh localAge current localGet localSize ledger
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, ?_, final, finalAllocator, ?_, publicLedger⟩
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

#print axioms inflate_default_view_public_live
end Zlib.Inflate.Local
