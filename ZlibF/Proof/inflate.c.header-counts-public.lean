import ZlibF.Proof.«inflate.c.header-counts-wait»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual public waiting call retains the three TABLE counts. -/
theorem inflate_LENLENS_header_wait_counts
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {received : List Bool}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (input : BitInv h (dispatchRegs z s) bs)
    (mode : s.mode = LENLENS) (progress : LenlensProgress s s.hold s.bits received)
    (short : (stream (dispatchRegs z s) bs).length / 3 < s.ncode.toNat - s.«have».toNat)
    (flush : Int32) :
    ∃ rc after stream state used,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧ used ≤ bs.length ∧
      (state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist) ∧
      ((used = 0 ∧ (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true) ∨
       (used = bs.length ∧ (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false)) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s, 0,
      ?_, final, allocator, ?_, Nat.zero_le _, ?_, Or.inl ⟨rfl, rejected⟩⟩
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
    · exact ⟨rfl, rfl, rfl⟩
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
    have input0 : BitInv (syncAlloc h) (dispatchRegs z s) bs := by
      refine ⟨input.have_eq, ?_, input.hold_lt⟩
      rcases input.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
      · exact Or.inl empty
      · exact Or.inr ⟨ref, array, off, pointer,
          (byte_view_syncAlloc invariant.good.fresh get).1, bound, values⟩
    obtain ⟨rc, heap1, stream0, state, bytes, bodyRun, current, finalAllocator,
      localGet, localSize, localRo⟩ :=
      inflate_default_origin_local_state_return env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    obtain ⟨traceRc, traceHeap, traceStream, traceState, traceRun, traceFinal, _traceAllocator, trace⟩ :=
      inflate_body_LENLENS_header_wait_counts env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull input0 mode progress short
    have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
    cases same
    have sameState : state = traceState :=
      Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, bs.length,
      ?_, final, finalAllocator, ?_, Nat.le_refl _, ?_, Or.inr ⟨rfl, accepted⟩⟩
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
    · rw [sameState]
      exact trace
#print axioms inflate_LENLENS_header_wait_counts

/-- Original DataStep execution retains the actual TABLE counts. -/
theorem inflate_dataStep_LENLENS_header_wait_counts
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {received : List Bool}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (mode : s.mode = LENLENS) (progress : LenlensProgress s s.hold s.bits received)
    (short : (s.bits.toNat + 8 * z.avail_in.toNat) / 3 <
      s.ncode.toNat - s.«have».toNat) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist := by
  obtain ⟨z0, stream0, get0, get1, buffers, _header, inputBytes, _usedEq, _outputBytes, actual⟩ := observed
  have eq0 : z0 = z := Option.some.inj (get0.symm.trans invariant.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := s) inputBytes invariant.held
  have short0 : (Zlib.Inflate.Proofs.stream (dispatchRegs z s) input).length / 3 <
      s.ncode.toNat - s.«have».toNat := by
    rw [tcStream_length view]
    have length : z.avail_in.toNat = input.length := view.have_eq
    change (s.bits.toNat + 8 * input.length) / 3 < _
    rw [← length]
    exact short
  obtain ⟨rc1, heap1, stream1, state, used1, run, final, finalAllocator,
    _freed, _bound, trace, _kind⟩ :=
    inflate_LENLENS_header_wait_counts invariant allocator buffers view mode progress short0 flush
  have same : (rc1, heap1) = (rc, after) := Except.ok.inj (run.symm.trans actual)
  cases same
  have streamEq : stream1 = stream0 :=
    Option.some.inj (final.good.live.hz.symm.trans get1)
  subst stream0
  exact ⟨stream1, state, final, finalAllocator, trace⟩

#print axioms inflate_dataStep_LENLENS_header_wait_counts

end Zlib.Inflate.Proofs
