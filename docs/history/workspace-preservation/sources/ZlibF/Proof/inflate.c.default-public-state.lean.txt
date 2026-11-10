import ZlibF.Proof.«inflate.c.leave-default-boundary»
import ZlibF.Proof.«inflate.c.default-public-witness»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual default body, including every direct return and
the full inf_leave continuation, retains the initialized relation and
allocator. The internal fast bridge still requires distinct raw buffers. -/
theorem inflate_body_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s)) :
    ∃ rc after stream state,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream := by
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
    refine ⟨value, heap0, stream0, state0, ?_, current, currentAllocator⟩
    rw [bind_app, run]
    rfl
  | leave =>
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨rc, after, stream, state, leaveRun, final, finalAllocator⟩ :=
      inflate_leave_default_state currentEnv current currentAllocator packet bits
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator⟩
    rw [bind_app, run]
    exact leaveRun

/-- The complete state relation and local-object facts hold on the same
actual returning execution. Determinism identifies the two checked source
results; no outgoing invariant or allocator contract is assumed. -/
theorem inflate_default_local_state_return {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (raw : RawFastIO (dispatchRegs z s))
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false := by
  obtain ⟨rc, after, stream, state, bytes, run, good, tables, pending, held,
    localFinal, size, ro, window⟩ :=
    inflate_default_local_return E invariant allocator buffers raw localGet localSize localRo
  obtain ⟨rc2, heap2, stream2, state2, run2, final, finalAllocator⟩ :=
    inflate_body_default_state E invariant allocator buffers raw
  have heaps : after = heap2 := congrArg Prod.snd (Except.ok.inj (run.symm.trans run2))
  subst heap2
  have streams : stream = stream2 := Option.some.inj (good.live.hz.symm.trans final.good.live.hz)
  have states : state = state2 := Option.some.inj (good.live.hs.symm.trans final.good.live.hs)
  subst stream2
  subst state2
  exact ⟨rc, after, stream, state, bytes, run, final, finalAllocator, localFinal, size, ro⟩

/-- `int inflate(z_streamp strm, int flush)`.
Actual public entry and cleanup preserve the full default relation and the
default allocator on every returning outcome. Every signed flush, malformed
input and genuine window allocation failure are covered. The explicit internal
scope still requires distinct raw input/output blocks. This is not the full
public result/frame/ownership or all-history theorem. -/
theorem inflate_default_raw_state_safe {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) (flush : Int32) :
    ∃ rc after stream state, C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨rc, heap1, stream, state, bytes, bodyRun, current, finalAllocator,
    localGet, localSize, localRo⟩ :=
    inflate_default_local_state_return env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) raw
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, ?_, final, finalAllocator, ?_⟩
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


/-- The stronger state-preserving public result has an actually initialized
concrete caller with readable/writable distinct raw buffers. -/
theorem inflate_default_raw_state_witness :
    ∃ initialized z s incoming stream rc after finalStream finalState,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, initialized) ∧
      DefaultStateJ initialized (.tab 0) witnessHeap.nextBlk z s ∧
      stream = { z with next_in := .ref (.blk 1) 0, avail_in := 2, next_out := .ref (.blk 2) 0, avail_out := 1 } ∧
      incoming = (ZStreamRef.tab 0).put initialized stream ∧
      DefaultStateJ incoming (.tab 0) witnessHeap.nextBlk stream s ∧ DefAlloc stream ∧
      StreamBuffers incoming (.tab 0) ∧ RawFastIO (dispatchRegs stream s) ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      DefaultStateJ after (.tab 0) witnessHeap.nextBlk finalStream finalState ∧ DefAlloc finalStream ∧
      after.bytes incoming.nextBlk = none := by
  obtain ⟨initialized, z, s, incoming, stream, _, _, _, _, initRun, initial,
    streamEq, heapEq, current, allocator, buffers, raw, _, _, _⟩ := inflate_default_raw_safe_witness
  obtain ⟨rc, after, finalStream, finalState, run, final, finalAllocator, freed⟩ :=
    inflate_default_raw_state_safe current allocator buffers raw Z_FINISH
  exact ⟨initialized, z, s, incoming, stream, rc, after, finalStream, finalState,
    initRun, initial, streamEq, heapEq, current, allocator, buffers, raw, run, final, finalAllocator, freed⟩

end Zlib.Inflate.Proofs
