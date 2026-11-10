import ZlibF.Proof.«inflate.c.leave-local»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The four-byte local object cannot be the default decoder's window. -/
theorem default_local_not_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {block : Nat} {array : Array UInt8} (good : Good h r zs z s)
    (get : h.bytes block = some array) (size : array.size = 4) (bits : s.wbits = 15) :
    s.window ≠ .ref (.blk block) 0 := by
  intro window
  rcases good.inv.win.block with null | ⟨w, bytes, win, bytesGet, ro, bytesSize⟩
  · rw [window] at null
    cases null
  · rw [window] at win
    cases win
    have same : bytes = array := Option.some.inj (bytesGet.symm.trans get)
    subst bytes
    rw [size, bits] at bytesSize
    change 4 = 32768 at bytesSize
    omega

/-- A live byte object is distinct from the stream root and private state.
Its concrete size also excludes the default window. -/
theorem default_local_outside {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {block : Nat} {array : Array UInt8} (good : Good h r zs z s)
    (get : h.bytes block = some array) (size : array.size = 4) (bits : s.wbits = 15) :
    ¬ (StreamRoot r block ∨ InflateOwned zs s block) := by
  have notState : block ≠ zs := by
    intro same
    subst block
    have unique := good.uniq zs
    simp only [get, good.live.hs, cnt_some] at unique
    omega
  have notRoot : ¬ StreamRoot r block := by
    cases r with
    | tab index =>
      intro same
      change block = index at same
      subst block
      have unique := good.uniq index
      have hz : h.streams index = some z := good.live.hz
      simp only [get, hz, cnt_some] at unique
      omega
    | in_gzstate_strm index =>
      intro same
      change block = index at same
      subst block
      obtain ⟨g, gzGet, eq⟩ := Option.map_eq_some_iff.mp good.live.hz
      have unique := good.uniq index
      simp only [get, gzGet, cnt_some] at unique
      omega
  rintro (root | (state | window))
  · exact notRoot root
  · exact notState state
  · exact default_local_not_window good get size bits window

/-- The actual main body and return boundary retain the live writable local
object. All facts needed by its final free follow from source frames and
existing-object separation, rather than from a cleanup contract assumption. -/
theorem inflate_default_local_return {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
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
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧ after.bytes block = some bytes ∧
      bytes.size = 4 ∧ after.ro block = false ∧ state.wbits = 15 := by
  have pointers := raw
  obtain ⟨ib, io, ob, oo, input, output, different⟩ := pointers
  have nonnull : z.next_out ≠ .null := by change z.next_out = .ref (.blk ob) oo at output; rw [output]; simp
  have inputValid : z.next_in = .null → z.avail_in = 0 := by
    change z.next_in = .ref (.blk ib) io at input
    rw [input]
    intro impossible
    cases impossible
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used, made, bound, run, current,
    packet, currentRaw, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_raw_framed E invariant allocator buffers nonnull inputValid raw
  obtain ⟨bytes, byteGet, byteSize⟩ := sizes.view (ref := .blk block) localGet
  have byteSize4 : bytes.size = 4 := byteSize.trans localSize
  have metadata := memoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs heap0 run
  have roEq : heap0.ro = h.ro := congrArg Prod.fst metadata
  have ro0 : heap0.ro block = false := by rw [roEq]; exact localRo
  cases exit with
  | ret value =>
    refine ⟨value, heap0, stream0, state0, bytes, ?_, current.good, current.tables,
      current.pending, current.held, byteGet, byteSize4, ro0, current.window⟩
    rw [bind_app, run]
    rfl
  | leave =>
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have statics : Zlib.Crc32.Proofs.StaticsOK heap0 := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [current.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rc, after, stream, state, leaveRun, finalGood, finalTables,
      finalPending, held, localFinal, finalRo, windowBits⟩ :=
      inflate_leave_local_boundary currentEnv current.good currentAllocator.1 statics
        packet current.tables current.pending bits byteGet
        (default_local_outside current.good byteGet byteSize4 current.window)
    refine ⟨rc, after, stream, state, bytes, ?_, finalGood, finalTables, finalPending,
      held, localFinal, byteSize4, finalRo.trans ro0, windowBits.trans current.window⟩
    rw [bind_app, run]
    exact leaveRun

/-- `int inflate(z_streamp strm, int flush)`.
The actual public entry returns without a runtime fault under the initialized
default relation and the explicit distinct-raw-buffer domain. It executes the
local allocation, source entry checks, complete decode loop, all return paths
and local free. Malformed input, every signed flush and window allocation
failure are included. The local object is absent on return. This is an internal
safety milestone: the full public frame/ownership, history and functional result
contract are not asserted here. Broader caller byte views remain separate. -/
theorem inflate_default_raw_safe {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) (flush : Int32) :
    ∃ rc after stream state, C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧ state.wbits = 15 ∧ after.bytes h.nextBlk = none := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨rc, heap1, stream, state, bytes, bodyRun, finalGood, finalTables,
    finalPending, held, localGet, localSize, localRo, windowBits⟩ :=
    inflate_default_local_return env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) raw
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have final : Good (freeWin heap1 (syncBuf h)) r zs stream state :=
    good_freeBuf finalGood (by
      intro block window same
      subst block
      exact default_local_not_window finalGood localGet localSize windowBits window)
  have tables : DataTableInvariant (freeWin heap1 (syncBuf h)) state := by
    intro active
    have old := finalTables active
    constructor
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.lengthTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.distanceTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
  refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, ?_, final, tables,
    finalPending, held, windowBits, ?_⟩
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
