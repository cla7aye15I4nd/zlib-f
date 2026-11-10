import ZlibF.Proof.«inflate.c.header-phase-transport»

namespace Zlib.Inflate.Proofs.HeaderPublicObserver
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderSourceTrace
set_option autoImplicit false

/-- Interpret an actual exhausted main-body source observation inside its
original from-init public DataStep. The initialized and intermediate J,
allocator and packet are derived from real source theorems. Neither J nor
any desired parser postcondition is a caller hypothesis. -/
theorem actual_wait_from_init
    {h after readHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s readState : InflateState}
    {log : DataLog} {flush rc : Int32} {input output : List UInt8} {used : Nat} {regs : IL}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (getZ : r.get h = some z) (pointer : z.state = some (.inflate zs)) (getS : h.istates zs = some s)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (mainRun : runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init (syncAlloc h) = .ok ((.error Ex.leave, regs), readHeap))
    (readGet : readHeap.istates zs = some readState) (window : readState.wsize = 0) (noOutput : regs.out_ = regs.left) :
    ∃ stream0 state, DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      LeaveMetadataFrame (leaveState readState regs) state ∧
      stream0.next_in = regs.next ∧ stream0.avail_in = regs.have_ ∧
      stream0.next_out = regs.put ∧ stream0.avail_out = regs.left := by
  have observed0 := observed
  obtain ⟨initial, allocator⟩ := HeaderDataTrace.origin_of_records history scope getZ pointer getS
  obtain ⟨_z0, _z1, _get0, _get1, buffers, _header, _input, _used, _output, _actual⟩ := observed
  have source := accepted_for_records history scope observed0 getZ pointer getS nonnull inputValid
  cases source with
  | observed entryHeap entryState exit actualRegs bodyHeap localHeap localBytes initialStream initialPointer initialState entryStream entryRecord actualMain switches finish localGet localSize localRo freed =>
    rw [mainRun] at actualMain
    cases actualMain
    have allocated := default_origin_syncAlloc initial
    let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
    have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
    obtain ⟨_bs, exit0, regs0, heap0, stream0, state0, _used0, _made0, _bound0, run0, current, packet,
      bits, _sizes, _next, _count, _put, _left, _fixed, currentAllocator⟩ :=
      inflate_run_default_origin_framed env allocated allocator (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
    rw [mainRun] at run0
    cases run0
    have sameState : state0 = readState := Option.some.inj (current.good.live.hs.symm.trans readGet)
    subst state0
    have readEnv : Env c readHeap r zs stream0 readState := ⟨rfl, rfl, current.good.live.hz, readGet⟩
    obtain ⟨rc0, leaveHeap, returned, state, leave, final, finalAllocator, frame, nextIn, availIn, nextOut, availOut⟩ :=
      EntryPath.HeadHistory.leave_wait_no_window readEnv current currentAllocator packet bits window noOutput
    cases finish with
    | leave actualLeave =>
      have same := Except.ok.inj (actualLeave.symm.trans leave)
      cases same
      rw [freed]
      exact ⟨returned, state, final.free_local localGet localSize, finalAllocator, frame, nextIn, availIn, nextOut, availOut⟩

#print axioms actual_wait_from_init
end Zlib.Inflate.Proofs.HeaderPublicObserver
