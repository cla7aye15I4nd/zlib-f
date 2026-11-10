import ZlibF.Proof.«inflate.c.direct-result-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflate(z_streamp strm, int flush)`.
Actual public entry, body and local cleanup retain full default J and
allocation. The return code is one of the seven public codes, derived
from the actual source and bounded loop. For OK, STREAM_END, DATA_ERROR
and BUF_ERROR, both lifetime
totals charge exactly the consumed/produced bytes and all public cursors
and remaining counts agree. Every signed flush and malformed input are
included. The explicit internal domain is default J with distinct raw
buffers. OK additionally implies original-call input/output progress and
a non-FINISH flush. END implies DONE, DATA_ERROR implies BAD, NEED_DICT implies DICT, and
MEM_ERROR implies MEM. Memory-error counter timing, all-return accounting,
caller frame and ownership remain open. This is not the all-history, frame/ownership or full Goal.inflate
result. -/
theorem inflate_default_raw_mode_result {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) (flush : Int32) :
    ∃ rc after stream state, ∃ used made : Nat,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none ∧ InflateResultCode rc ∧
      (rc = Z_OK → (used ≠ 0 ∨ made ≠ 0) ∧ flush ≠ Z_FINISH) ∧
      (rc = Z_STREAM_END → state.mode = DONE) ∧ (rc = Z_DATA_ERROR → state.mode = BAD) ∧
      (rc = Z_NEED_DICT → state.mode = DICT) ∧ (rc = Z_MEM_ERROR → state.mode = MEM) ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        StreamAccounting z stream used made ∧ stream.total_in = z.total_in + UInt64.ofNat used ∧
          stream.total_out = z.total_out + UInt64.ofNat made) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨rc, heap1, stream, state, bytes, used, made, bodyRun, current, finalAllocator,
    localGet, localSize, localRo, post⟩ :=
    inflate_default_local_counter_return env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) raw
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have code := inflate_body_default_return_code env allocated allocator
    (streamBuffers_syncAlloc invariant.good.fresh buffers) raw bodyRun
  have progress : rc = Z_OK → (used ≠ 0 ∨ made ≠ 0) ∧ flush ≠ Z_FINISH := by
    intro ok
    have runOK := bodyRun
    rw [ok] at runOK
    exact inflate_body_default_ok_progress env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) raw runOK current.good.live.hz
      (post (Or.inl ok)).1
  obtain ⟨ended, bad⟩ := inflate_body_default_terminal_modes env allocated allocator
    (streamBuffers_syncAlloc invariant.good.fresh buffers) raw bodyRun current.good.live.hs
  obtain ⟨needed, memory⟩ := inflate_body_default_direct_modes env allocated allocator
    (streamBuffers_syncAlloc invariant.good.fresh buffers) raw bodyRun current.good.live.hs
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, used, made, ?_, final, finalAllocator, ?_, code, progress, ended, bad, needed, memory, post⟩
  · obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw
    have outBool : (z.next_out == .null) = false := by
      change z.next_out = .ref (.blk ob) oo at output
      rw [output]
      rfl
    have inBool : (z.next_in == .null) = false := by
      change z.next_in = .ref (.blk ib) io at input
      rw [input]
      rfl
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h invariant.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live, bne_self_eq_false,
      Bool.false_eq_true, ite_false, ldZStream_ok allocated.good.live.hz, outBool,
      inBool, Bool.false_and, Bool.false_or, allocated.good.live.zst, castI]
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




/-- The two-counter public result has an actually initialized
concrete caller with readable/writable distinct raw buffers. -/
theorem inflate_default_raw_mode_witness :
    ∃ initialized z s incoming stream rc after finalStream finalState, ∃ used made : Nat,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, initialized) ∧
      DefaultStateJ initialized (.tab 0) witnessHeap.nextBlk z s ∧
      stream = { z with next_in := .ref (.blk 1) 0, avail_in := 2, next_out := .ref (.blk 2) 0, avail_out := 1 } ∧
      incoming = (ZStreamRef.tab 0).put initialized stream ∧
      DefaultStateJ incoming (.tab 0) witnessHeap.nextBlk stream s ∧ DefAlloc stream ∧
      StreamBuffers incoming (.tab 0) ∧ RawFastIO (dispatchRegs stream s) ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      DefaultStateJ after (.tab 0) witnessHeap.nextBlk finalStream finalState ∧ DefAlloc finalStream ∧
      after.bytes incoming.nextBlk = none ∧ InflateResultCode rc ∧ rc ≠ Z_OK ∧
      (rc = Z_STREAM_END → finalState.mode = DONE) ∧ (rc = Z_DATA_ERROR → finalState.mode = BAD) ∧
      (rc = Z_NEED_DICT → finalState.mode = DICT) ∧ (rc = Z_MEM_ERROR → finalState.mode = MEM) ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        StreamAccounting stream finalStream used made ∧
        finalStream.total_in = stream.total_in + UInt64.ofNat used ∧
        finalStream.total_out = stream.total_out + UInt64.ofNat made) := by
  obtain ⟨initialized, z, s, incoming, stream, _, _, _, _, initRun, initial,
    streamEq, heapEq, current, allocator, buffers, raw, _, _, _⟩ := inflate_default_raw_safe_witness
  obtain ⟨rc, after, finalStream, finalState, used, made, run, final, finalAllocator, freed, code, progress, ended, bad, needed, memory, post⟩ :=
    inflate_default_raw_mode_result current allocator buffers raw Z_FINISH
  have notOK : rc ≠ Z_OK := by intro ok; exact (progress ok).2 rfl
  exact ⟨initialized, z, s, incoming, stream, rc, after, finalStream, finalState, used, made,
    initRun, initial, streamEq, heapEq, current, allocator, buffers, raw, run, final, finalAllocator, freed, code, notOK, ended, bad, needed, memory, post⟩

end Zlib.Inflate.Proofs
