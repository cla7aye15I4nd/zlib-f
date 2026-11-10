import ZlibF.Proof.«inflate.c.all-return-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual remaining counts determine unique original-call byte counts. -/
theorem streamAccounting_counts_unique {before stream : ZStream} {used made otherUsed otherMade : Nat}
    (first : StreamAccounting before stream used made)
    (second : StreamAccounting before stream otherUsed otherMade) : used = otherUsed ∧ made = otherMade := by
  have input := first.2.2.1
  have otherInput := second.2.2.1
  have output := first.2.2.2.1
  have otherOutput := second.2.2.2.1
  omega

/-- `int inflate(z_streamp strm, int flush)`.
All public result clauses except caller frame/ownership hold on the same
actual returning call in the explicit initialized/default and distinct-raw
buffer scope. Every return has cursor/count accounting and readable
produced bytes. Progress, the four mode links, normal lifetime charging
and MEM_ERROR timing are derived from source. The full reachable-history
domain and general byte views remain open. This is not Goal.inflate. -/
theorem inflate_default_raw_accounted_result {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) (flush : Int32) :
    ∃ rc after stream state used out,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none ∧
      StreamAccounting z stream used out.length ∧ Bytes after z.next_out out.length out ∧
      InflateResultCode rc ∧
      (rc = Z_OK → (used ≠ 0 ∨ out ≠ []) ∧ flush ≠ Z_FINISH) ∧
      (rc = Z_STREAM_END → state.mode = DONE) ∧ (rc = Z_DATA_ERROR → state.mode = BAD) ∧
      (rc = Z_NEED_DICT → state.mode = DICT) ∧
      (rc = Z_MEM_ERROR → state.mode = MEM ∧ stream.total_in = z.total_in ∧ stream.total_out = z.total_out) ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        stream.total_in = z.total_in + UInt64.ofNat used ∧
        stream.total_out = z.total_out + UInt64.ofNat out.length) := by
  obtain ⟨rc, after, stream, state, used, made, run, current, finalAllocator, freed, accounting⟩ :=
    inflate_default_raw_all_return_accounting invariant allocator buffers raw flush
  obtain ⟨rc2, heap2, stream2, state2, used2, made2, run2, final2, allocator2, freed2,
    code, progress, ended, bad, needed, memory, post⟩ :=
    inflate_default_raw_memory_result invariant allocator buffers raw flush
  have codes : rc = rc2 := congrArg Prod.fst (Except.ok.inj (run.symm.trans run2))
  have heaps : after = heap2 := congrArg Prod.snd (Except.ok.inj (run.symm.trans run2))
  subst rc2
  subst heap2
  have streams : stream = stream2 := Option.some.inj (current.good.live.hz.symm.trans final2.good.live.hz)
  have states : state = state2 := Option.some.inj (current.good.live.hs.symm.trans final2.good.live.hs)
  subst stream2
  subst state2
  have counts : (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
      used2 = used ∧ made2 = made := by
    intro normal
    exact streamAccounting_counts_unique (post normal).1 accounting
  obtain ⟨out, length, bytes⟩ := inflate_default_raw_output_bytes invariant allocator buffers raw run accounting.2.1
  refine ⟨rc, after, stream, state, used, out, run, current, finalAllocator, freed, ?_, ?_,
    code, ?_, ended, bad, needed, memory, ?_⟩
  · rwa [length]
  · rwa [length]
  · intro ok
    obtain ⟨usedEq, madeEq⟩ := counts (Or.inl ok)
    have moved := progress ok
    rw [usedEq, madeEq] at moved
    refine ⟨?_, moved.2⟩
    rcases moved.1 with input | output
    · exact Or.inl input
    · refine Or.inr ?_
      intro empty
      have zero : out.length = 0 := by rw [empty]; rfl
      exact output (length.symm.trans zero)
  · intro normal
    obtain ⟨usedEq, madeEq⟩ := counts normal
    obtain ⟨_, inputTotal, outputTotal, _⟩ := post normal
    rw [usedEq] at inputTotal
    rw [madeEq] at outputTotal
    rw [length]
    exact ⟨inputTotal, outputTotal⟩

/-- The combined all-return result has a concrete caller established by
the actual default initializer, followed by the actual complete FINISH call. -/
theorem inflate_default_raw_accounted_witness :
    ∃ initialized z s incoming stream rc after finalStream finalState used out,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, initialized) ∧
      DefaultStateJ initialized (.tab 0) witnessHeap.nextBlk z s ∧
      stream = { z with next_in := .ref (.blk 1) 0, avail_in := 2, next_out := .ref (.blk 2) 0, avail_out := 1 } ∧
      incoming = (ZStreamRef.tab 0).put initialized stream ∧
      DefaultStateJ incoming (.tab 0) witnessHeap.nextBlk stream s ∧ DefAlloc stream ∧
      StreamBuffers incoming (.tab 0) ∧ RawFastIO (dispatchRegs stream s) ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      DefaultStateJ after (.tab 0) witnessHeap.nextBlk finalStream finalState ∧ DefAlloc finalStream ∧
      after.bytes incoming.nextBlk = none ∧
      StreamAccounting stream finalStream used out.length ∧ Bytes after stream.next_out out.length out ∧
      InflateResultCode rc ∧ rc ≠ Z_OK ∧
      (rc = Z_STREAM_END → finalState.mode = DONE) ∧ (rc = Z_DATA_ERROR → finalState.mode = BAD) ∧
      (rc = Z_NEED_DICT → finalState.mode = DICT) ∧
      (rc = Z_MEM_ERROR → finalState.mode = MEM ∧ finalStream.total_in = stream.total_in ∧
        finalStream.total_out = stream.total_out) ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        finalStream.total_in = stream.total_in + UInt64.ofNat used ∧
        finalStream.total_out = stream.total_out + UInt64.ofNat out.length) := by
  obtain ⟨initialized, z, s, incoming, stream, _, _, _, _, initRun, initial,
    streamEq, heapEq, current, allocator, buffers, raw, _, _, _⟩ := inflate_default_raw_safe_witness
  obtain ⟨rc, after, finalStream, finalState, used, out, run, final, finalAllocator, freed,
    accounting, bytes, code, progress, ended, bad, needed, memory, post⟩ :=
    inflate_default_raw_accounted_result current allocator buffers raw Z_FINISH
  have notOK : rc ≠ Z_OK := by intro ok; exact (progress ok).2 rfl
  exact ⟨initialized, z, s, incoming, stream, rc, after, finalStream, finalState, used, out,
    initRun, initial, streamEq, heapEq, current, allocator, buffers, raw, run, final,
    finalAllocator, freed, accounting, bytes, code, notOK, ended, bad, needed, memory, post⟩

end Zlib.Inflate.Proofs
