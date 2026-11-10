import ZlibF.Proof.«inflate.c.memory-accounting»
import ZlibF.Proof.«inflate.c.output-storage»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflate(z_streamp strm, int flush)`.
Every actual MEM_ERROR return retains both original lifetime counters,
including late window allocation failure and final local cleanup. The
explicit domain is default J with distinct raw input/output buffers. -/
theorem inflate_default_raw_memory_accounting
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s : InflateState}
    {flush : Int32} (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (executed : C.run (inflate (some r) flush) h = .ok (Z_MEM_ERROR, after))
    (getAfter : r.get after = some stream) :
    stream.total_in = z.total_in ∧ stream.total_out = z.total_out := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨value, heap1, stream1, state, scratch, bodyRun, current, finalAllocator,
    localGet, localSize, localRo⟩ :=
    inflate_default_local_state_return env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) raw
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have publicRun : C.run (inflate (some r) flush) h =
      .ok (value, freeWin heap1 (syncBuf h)) := by
    obtain ⟨ib, io, ob, oo, input, output, separate⟩ := raw
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
    have body := bodyRun
    rw [bind_app] at body
    unfold runX at body
    dsimp only [c] at body
    erw [body]
    simp only []
    change (do freeB (syncBuf h); pure value) heap1 = .ok (value, freeWin heap1 (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  have same := Except.ok.inj (publicRun.symm.trans executed)
  have codeEq : value = Z_MEM_ERROR := congrArg Prod.fst same
  have heapEq : freeWin heap1 (syncBuf h) = after := congrArg Prod.snd same
  have final := current.free_local localGet localSize
  have streamGet : r.get after = some stream1 := by rw [← heapEq]; exact final.good.live.hz
  have streamEq : stream1 = stream := Option.some.inj (streamGet.symm.trans getAfter)
  rw [codeEq] at bodyRun
  have accounting := inflate_body_default_memory_accounting env allocated allocator
    (streamBuffers_syncAlloc invariant.good.fresh buffers) raw bodyRun current.good.live.hz
  rwa [streamEq] at accounting

/-- `int inflate(z_streamp strm, int flush)`.
The actual public default/raw call combines fault freedom, full J,
progress, the four return-mode links, ordinary cursor/counter accounting,
readable produced bytes, and MEM_ERROR counter timing on one execution.
The explicit initialized/default and distinct-raw-buffer scope remains.
All-return cursor accounting, caller frame/ownership, general byte views
and the full reachable-history contract remain open. -/
theorem inflate_default_raw_memory_result {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) (flush : Int32) :
    ∃ rc after stream state, ∃ used made : Nat,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none ∧
      InflateResultCode rc ∧
      (rc = Z_OK → (used ≠ 0 ∨ made ≠ 0) ∧ flush ≠ Z_FINISH) ∧
      (rc = Z_STREAM_END → state.mode = DONE) ∧ (rc = Z_DATA_ERROR → state.mode = BAD) ∧
      (rc = Z_NEED_DICT → state.mode = DICT) ∧
      (rc = Z_MEM_ERROR → state.mode = MEM ∧ stream.total_in = z.total_in ∧ stream.total_out = z.total_out) ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        StreamAccounting z stream used made ∧ stream.total_in = z.total_in + UInt64.ofNat used ∧
        stream.total_out = z.total_out + UInt64.ofNat made ∧
        ∃ out, out.length = made ∧ Bytes after z.next_out made out) := by
  obtain ⟨rc, after, stream, state, used, made, run, current, finalAllocator, freed,
    code, progress, ended, bad, needed, memory, post⟩ :=
    inflate_default_raw_mode_result invariant allocator buffers raw flush
  refine ⟨rc, after, stream, state, used, made, run, current, finalAllocator, freed,
    code, progress, ended, bad, needed, ?_, ?_⟩
  · intro mem
    have executed := run
    rw [mem] at executed
    exact ⟨memory mem, inflate_default_raw_memory_accounting invariant allocator buffers raw
      executed current.good.live.hz⟩
  · intro normal
    obtain ⟨accounting, inputTotal, outputTotal⟩ := post normal
    exact ⟨accounting, inputTotal, outputTotal,
      inflate_default_raw_output_bytes invariant allocator buffers raw run accounting.2.1⟩

/-- An actual successful default initializer witnesses the combined
scope, including the complete FINISH call and its memory timing clause. -/
theorem inflate_default_raw_memory_witness :
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
      (rc = Z_NEED_DICT → finalState.mode = DICT) ∧
      (rc = Z_MEM_ERROR → finalState.mode = MEM ∧ finalStream.total_in = stream.total_in ∧
        finalStream.total_out = stream.total_out) ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        StreamAccounting stream finalStream used made ∧
        finalStream.total_in = stream.total_in + UInt64.ofNat used ∧
        finalStream.total_out = stream.total_out + UInt64.ofNat made ∧
        ∃ out, out.length = made ∧ Bytes after stream.next_out made out) := by
  obtain ⟨initialized, z, s, incoming, stream, _, _, _, _, initRun, initial,
    streamEq, heapEq, current, allocator, buffers, raw, _, _, _⟩ := inflate_default_raw_safe_witness
  obtain ⟨rc, after, finalStream, finalState, used, made, run, final, finalAllocator, freed,
    code, progress, ended, bad, needed, memory, post⟩ :=
    inflate_default_raw_memory_result current allocator buffers raw Z_FINISH
  have notOK : rc ≠ Z_OK := by intro ok; exact (progress ok).2 rfl
  exact ⟨initialized, z, s, incoming, stream, rc, after, finalStream, finalState, used, made,
    initRun, initial, streamEq, heapEq, current, allocator, buffers, raw, run, final,
    finalAllocator, freed, code, notOK, ended, bad, needed, memory, post⟩

end Zlib.Inflate.Proofs
