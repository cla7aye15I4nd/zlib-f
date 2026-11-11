import ZlibF.Proof.«inflate.c.low-output»
import ZlibF.Proof.«inflate.c.default-view-run»
import ZlibF.Proof.«inflate.c.stream-frame-run»
import ZlibF.Proof.«inflate.c.leave-default-boundary»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual main body retains allocator identity. The stream
frame is proved independently about the translated source, then attached
to this actual returning run. -/
theorem inflate_run_default_view_framed
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat ∧
      StreamRootFrame r h after ∧ DefAlloc stream := by
  obtain ⟨bs, exit, regs, after, stream, state, used, made, bound, run, final,
    packet, bits, sizes, next, count, put, left⟩ :=
    inflate_run_default_view E invariant buffers nonnull inputValid
  have frame := streamFrameX_inflate_run r c E.strm IL.init h (.error exit) regs after run
  exact ⟨bs, exit, regs, after, stream, state, used, made, bound, run, final,
    packet, bits, sizes, next, count, put, left, frame,
    frame.allocator invariant.good.live.hz final.good.live.hz allocator⟩

/-- The actual main body and every return/leave path preserve the full
default state and the live local object needed by public cleanup. General
byte views are admitted; null-pointer entry refusals are handled outside. -/
theorem inflate_default_view_local_state_return
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false := by
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used, made, bound, run, current,
    packet, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  obtain ⟨bytes, byteGet, byteSize⟩ := sizes.view (ref := .blk block) localGet
  have byteSize4 : bytes.size = 4 := byteSize.trans localSize
  have metadata := memoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs heap0 run
  have roEq : heap0.ro = h.ro := congrArg Prod.fst metadata
  have ro0 : heap0.ro block = false := by rw [roEq]; exact localRo
  cases exit with
  | ret value =>
    refine ⟨value, heap0, stream0, state0, bytes, ?_, current,
      currentAllocator, byteGet, byteSize4, ro0⟩
    rw [bind_app, run]
    rfl
  | leave =>
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have statics : Zlib.Crc32.Proofs.StaticsOK heap0 := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [current.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rc, after, stream, state, leaveRun, final, finalAllocator⟩ :=
      inflate_leave_default_state currentEnv current currentAllocator packet bits
        (inflate_run_default_low_out E invariant buffers nonnull inputValid run current.good.live.hs)
    obtain ⟨localRc, localHeap, localZ, localS, localRun, localGood, localTables,
      localPending, held, localFinal, finalRo, windowBits⟩ :=
      inflate_leave_local_boundary currentEnv current.good currentAllocator.1 statics
        packet current.tables current.pending bits byteGet
        (default_local_outside current.good byteGet byteSize4 current.local_width)
    have same : (rc, after) = (localRc, localHeap) :=
      Except.ok.inj (leaveRun.symm.trans localRun)
    cases same
    refine ⟨rc, after, stream, state, bytes, ?_, final,
      finalAllocator, localFinal, byteSize4, finalRo.trans ro0⟩
    rw [bind_app, run]
    exact leaveRun

#print axioms inflate_run_default_view_framed
#print axioms inflate_default_view_local_state_return
end Zlib.Inflate.Proofs
