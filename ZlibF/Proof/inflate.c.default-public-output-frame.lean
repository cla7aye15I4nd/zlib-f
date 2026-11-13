import ZlibF.Proof.«inflate.c.entry-header»
import ZlibF.Proof.«inflate.c.output-frame-local-cleanup»
import ZlibF.Proof.«inflate.c.call-frame-facts»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual default public call has the exact memory-content
frame of its produced output prefix, including entry refusals, all direct
returns, genuine memory failure and the real temporary allocation/free.
The strong invariant is an explicit incoming premise; legal-history
closure and independent format refinement remain separate obligations. -/
theorem inflate_default_view_public_exact_frame
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z)
    (record : HeaderMemory h r s.head true) (flush : Int32) :
    ∃ rc after stream state used made,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧
      StreamAccounting z stream used made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b ∨ s.head = some (.tab b))
        (⟨z.next_out, made⟩ :: HeaderRegions h s.head) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have local_ : HeaderLocal c (syncAlloc h) r s (dispatchRegs z s) := entry_header_local invariant.good.fresh entry flush
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s, 0, 0,
      ?_, final, allocator, ?_, Nat.zero_le _, Nat.zero_le _, ?_,
      tmp_freed_buffer_frame invariant.good.fresh _ _⟩
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
      inflate_default_view_local_complete_accounting env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid local_
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have facts := call_frame_facts invariant buffers record flush
    have localFrame := inflate_default_view_local_exact_frame env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid local_ facts
      bodyRun current.good.live.hz accounting
    rw [HeaderRegions.of_headers _ (syncAlloc_gzheaders h)] at localFrame
    have publicFrame : BufferFrame h (freeWin heap1 (syncBuf h))
        (fun b => StreamRoot r b ∨ InflateOwned zs s b ∨ s.head = some (.tab b))
        (⟨z.next_out, made⟩ :: HeaderRegions h s.head) := by
      apply BufferFrame.mono_live (buffer_frame_cancel_local_regions invariant.good.fresh localFrame)
      intro b live inside
      rcases inside with (root | state | local_ | head) | owned
      · exact Or.inl root
      · exact Or.inr (Or.inl (Or.inl state))
      · change Ptr.ref (BRef.blk h.nextBlk) 0 = .ref (.blk b) 0 at local_
        cases local_
        exact False.elim (invariant.good.fresh h.nextBlk (Nat.le_refl _) live)
      · exact Or.inr (Or.inr head)
      · exact Or.inr (Or.inl owned)
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, used, made, ?_, final, finalAllocator, ?_,
      usedBound, madeBound, accounting, publicFrame⟩
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


#print axioms inflate_default_view_public_exact_frame
end Zlib.Inflate.Proofs
