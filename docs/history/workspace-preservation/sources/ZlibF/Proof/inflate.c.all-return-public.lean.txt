import ZlibF.Proof.«inflate.c.all-return-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Local cleanup facts and unconditional public cursor accounting hold
on the same actual body execution, as identified by determinism. -/
theorem inflate_default_local_all_return_accounting {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
      StreamAccounting z stream used made := by
  obtain ⟨rc, after, stream, state, bytes, run, current, finalAllocator,
    localFinal, size, ro⟩ :=
    inflate_default_local_state_return E invariant allocator buffers raw localGet localSize localRo
  obtain ⟨rc2, heap2, stream2, state2, used, made, run2, final, alloc2, post⟩ :=
    inflate_body_default_all_return_accounting E invariant allocator buffers raw
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
The actual public default/raw call has exact cursor/count accounting on
every return, including dictionary requests, direct terminal entries and
late window allocation failure. Full J, allocator and local cleanup hold
on that same run. Broader byte views, caller frame and ownership remain
open. This is not the complete reachable-history contract. -/
theorem inflate_default_raw_all_return_accounting {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) (flush : Int32) :
    ∃ rc after stream state, ∃ used made : Nat,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none ∧
      StreamAccounting z stream used made := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨rc, heap1, stream, state, bytes, used, made, bodyRun, current, finalAllocator,
    localGet, localSize, localRo, post⟩ :=
    inflate_default_local_all_return_accounting env allocated allocator
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
