import ZlibF.Proof.«inflate.c.input-accounting»
import ZlibF.Proof.«inflate.c.output-ledger-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual body establishes both lifetime totals and public
cursor/count accounting for all ordinary return classes. The input base,
unchanged input total, and conserved output ledger are derived from the
actual entry and complete loop. Error/direct-code accounting and full
caller frame/ownership remain separate obligations. -/
theorem inflate_body_default_counter_accounting {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s)) :
    ∃ rc after stream state, ∃ used made : Nat,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        StreamAccounting z stream used made ∧ stream.total_in = z.total_in + UInt64.ofNat used ∧
          stream.total_out = z.total_out + UInt64.ofNat made) := by
  obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw
  have nonnull : z.next_out ≠ .null := by
    change z.next_out = .ref (.blk ob) oo at output
    rw [output]
    simp
  have inputValid : z.next_in = .null → z.avail_in = 0 := by
    change z.next_in = .ref (.blk ib) io at input
    rw [input]
    intro impossible
    cases impossible
  have raw : RawFastIO (dispatchRegs z s) := ⟨ib, io, ob, oo, input, output, different⟩
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used, made, bound, run, current,
    packet, currentRaw, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_raw_framed E invariant allocator buffers nonnull inputValid raw
  cases exit with
  | ret value =>
    refine ⟨value, heap0, stream0, state0, 0, 0, ?_, current, currentAllocator, ?_⟩
    · rw [bind_app, run]
      rfl
    · intro normal
      obtain ⟨notNeed, notMem, notStream⟩ := normalInflateCode_not_direct normal
      rcases inflate_run_direct_codes run with needed | memory | streamError
      · exact False.elim (notNeed needed)
      · exact False.elim (notMem memory)
      · exact False.elim (notStream streamError)
  | leave =>
    have unchanged := inflate_run_input_total E.strm invariant.good.live.hz current.good.live.hz run
      (by intro impossible; cases impossible)
    have base := inflate_run_default_input_base E invariant buffers nonnull inputValid run
    have outputLedger := inflate_run_default_output_ledger E invariant buffers nonnull inputValid raw run
      current.good.live.hz
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨rc, after, stream, state, leaveRun, final, finalAllocator, accounting, counters⟩ :=
      inflate_leave_accounting currentEnv current currentAllocator packet bits fixed invariant.good.live.hz
        next count put left
    refine ⟨rc, after, stream, state, used, made, ?_, final, finalAllocator, ?_⟩
    · rw [bind_app, run]
      exact leaveRun
    · intro normal
      obtain ⟨notNeed, notMem, notStream⟩ := normalInflateCode_not_direct normal
      rcases counters with ⟨inputTotal, outputTotal, mode, selected⟩ | ⟨memory, rest⟩
      · refine ⟨accounting, inputTotal.trans ?_, outputTotal.trans ?_⟩
        · have remaining : regs.have_.toNat ≤ regs.in_.toNat := by rw [base]; omega
          have ledger : stream0.total_in + regs.in_.toUInt64 = z.total_in + z.avail_in.toUInt64 := by
            rw [unchanged, base]
          exact ZlibF.Math.CounterAccounting.charge_from_ledger z.total_in stream0.total_in
            regs.in_ regs.have_ z.avail_in used remaining count ledger
        · exact ZlibF.Math.CounterAccounting.charge_from_ledger z.total_out stream0.total_out
            regs.out_ regs.left z.avail_out made packet.output.count left outputLedger
      · exact False.elim (notMem memory)

/-- Local cleanup facts and both counter results hold on the same
actual body execution, as identified by determinism. -/
theorem inflate_default_local_counter_return {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes, ∃ used made : Nat,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        StreamAccounting z stream used made ∧ stream.total_in = z.total_in + UInt64.ofNat used ∧
          stream.total_out = z.total_out + UInt64.ofNat made) := by
  obtain ⟨rc, after, stream, state, bytes, run, current, finalAllocator,
    localFinal, size, ro⟩ :=
    inflate_default_local_state_return E invariant allocator buffers raw localGet localSize localRo
  obtain ⟨rc2, heap2, stream2, state2, used, made, run2, final, alloc2, post⟩ :=
    inflate_body_default_counter_accounting E invariant allocator buffers raw
  have codes : rc = rc2 := congrArg Prod.fst (Except.ok.inj (run.symm.trans run2))
  have heaps : after = heap2 := congrArg Prod.snd (Except.ok.inj (run.symm.trans run2))
  subst rc2
  subst heap2
  have streams : stream = stream2 := Option.some.inj (current.good.live.hz.symm.trans final.good.live.hz)
  have states : state = state2 := Option.some.inj (current.good.live.hs.symm.trans final.good.live.hs)
  subst stream2
  subst state2
  exact ⟨rc, after, stream, state, bytes, used, made, run, current, finalAllocator, localFinal, size, ro, post⟩

/-- `int inflate(z_streamp strm, int flush)`.
Actual public entry, body and local cleanup retain full default J and
allocation. For OK, STREAM_END, DATA_ERROR and BUF_ERROR, both lifetime
totals charge exactly the consumed/produced bytes and all public cursors
and remaining counts agree. Every signed flush and malformed input are
included. The explicit internal domain is default J with distinct raw
buffers. This is not the all-history, frame/ownership or full Goal.inflate
result. -/
theorem inflate_default_raw_counter_accounting {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) (flush : Int32) :
    ∃ rc after stream state, ∃ used made : Nat,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none ∧
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
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, used, made, ?_, final, finalAllocator, ?_, post⟩
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
theorem inflate_default_raw_counter_witness :
    ∃ initialized z s incoming stream rc after finalStream finalState, ∃ used made : Nat,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, initialized) ∧
      DefaultStateJ initialized (.tab 0) witnessHeap.nextBlk z s ∧
      stream = { z with next_in := .ref (.blk 1) 0, avail_in := 2, next_out := .ref (.blk 2) 0, avail_out := 1 } ∧
      incoming = (ZStreamRef.tab 0).put initialized stream ∧
      DefaultStateJ incoming (.tab 0) witnessHeap.nextBlk stream s ∧ DefAlloc stream ∧
      StreamBuffers incoming (.tab 0) ∧ RawFastIO (dispatchRegs stream s) ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      DefaultStateJ after (.tab 0) witnessHeap.nextBlk finalStream finalState ∧ DefAlloc finalStream ∧
      after.bytes incoming.nextBlk = none ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        StreamAccounting stream finalStream used made ∧
        finalStream.total_in = stream.total_in + UInt64.ofNat used ∧
        finalStream.total_out = stream.total_out + UInt64.ofNat made) := by
  obtain ⟨initialized, z, s, incoming, stream, _, _, _, _, initRun, initial,
    streamEq, heapEq, current, allocator, buffers, raw, _, _, _⟩ := inflate_default_raw_safe_witness
  obtain ⟨rc, after, finalStream, finalState, used, made, run, final, finalAllocator, freed, post⟩ :=
    inflate_default_raw_counter_accounting current allocator buffers raw Z_FINISH
  exact ⟨initialized, z, s, incoming, stream, rc, after, finalStream, finalState, used, made,
    initRun, initial, streamEq, heapEq, current, allocator, buffers, raw, run, final, finalAllocator, freed, post⟩

end Zlib.Inflate.Proofs
