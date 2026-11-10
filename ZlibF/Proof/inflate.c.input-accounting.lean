import ZlibF.Proof.«inflate.c.default-public-state»
import ZlibF.Proof.«inflate.c.exit-code-run»
import ZlibF.Proof.«inflate.c.input-total-run»
import ZlibF.Proof.«inflate.c.input-base-entry»
import ZlibF.Proof.«inflate.c.leave-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The ordinary public code classes are disjoint from all direct exits. -/
theorem normalInflateCode_not_direct {rc : Int32}
    (normal : rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) :
    rc ≠ Z_NEED_DICT ∧ rc ≠ Z_MEM_ERROR ∧ rc ≠ Z_STREAM_ERROR := by
  rcases normal with equal | equal | equal | equal
  all_goals subst rc; decide

/-- The complete actual body establishes public input accounting for every
ordinary return class. The local base and lifetime-total premises are derived
from the actual entry and loop frames. DICT, MEM and STREAM_ERROR direct
returns remain distinct; full output totals and caller ownership are open. -/
theorem inflate_body_default_input_accounting {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
        StreamAccounting z stream used made ∧ stream.total_in = z.total_in + UInt64.ofNat used) := by
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
      · refine ⟨accounting, inputTotal.trans ?_⟩
        have remaining : regs.have_.toNat ≤ regs.in_.toNat := by rw [base]; omega
        have ledger : stream0.total_in + regs.in_.toUInt64 = z.total_in + z.avail_in.toUInt64 := by
          rw [unchanged, base]
        exact ZlibF.Math.CounterAccounting.charge_from_ledger z.total_in stream0.total_in
          regs.in_ regs.have_ z.avail_in used remaining count ledger
      · exact False.elim (notMem memory)

/-- The local object's exact extent and the input-accounting result belong
to the same actual returning execution. Determinism joins the closed source
results; no local-object or callee contract is assumed. -/
theorem inflate_default_local_input_return {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
        StreamAccounting z stream used made ∧ stream.total_in = z.total_in + UInt64.ofNat used) := by
  obtain ⟨rc, after, stream, state, bytes, run, current, finalAllocator,
    localFinal, size, ro⟩ :=
    inflate_default_local_state_return E invariant allocator buffers raw localGet localSize localRo
  obtain ⟨rc2, heap2, stream2, state2, used, made, run2, final, alloc2, post⟩ :=
    inflate_body_default_input_accounting E invariant allocator buffers raw
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
Actual public entry, the complete body and local cleanup retain full J and
default allocation. Every ordinary return class has exact public cursor/count
accounting and total_in charges the original consumed input exactly once.
Every signed flush and malformed input are included. The explicit internal
domain still requires initialized/default J and distinct raw buffers. Full
output totals, other return-class accounting, frame/ownership and history
closure remain open; this is not the complete public inflate theorem. -/
theorem inflate_default_raw_input_accounting {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) (flush : Int32) :
    ∃ rc after stream state, ∃ used made : Nat,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none ∧
      ((rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
        StreamAccounting z stream used made ∧ stream.total_in = z.total_in + UInt64.ofNat used) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨rc, heap1, stream, state, bytes, used, made, bodyRun, current, finalAllocator,
    localGet, localSize, localRo, post⟩ :=
    inflate_default_local_input_return env allocated allocator
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



end Zlib.Inflate.Proofs
