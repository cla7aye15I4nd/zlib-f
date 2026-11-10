import ZlibF.Proof.«inflate.c.header-phase-transport»
import ZlibF.Proof.«inflate.c.cumulative-parser-boundary»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser Zlib.Inflate.Proofs.CumulativeBoundary
set_option autoImplicit false

theorem Meaning.table_wait {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {stream0 : ZStream} {observedState : InflateState}
    (before : Meaning .table h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (short : observedState.bits.toNat + 8 * stream0.avail_in.toNat < 14)
    (actual : DataStep .inflate h after r flush rc input output used) :
    Meaning .table after r zs (credit log input output used rc) := by
  obtain ⟨z, state, current, allocator, window, empty, mode, record, lastBound, last, view⟩ := before
  have sameZ : stream0 = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : observedState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst stream0 observedState
  obtain ⟨nextZ, nextS, next, nextAllocator, _usedBound, nextMode, nextLast, _wrap, nextWindow, _below, _count, word, noOutput⟩ :=
    table_wait_observed current allocator actual mode window short
  refine ⟨nextZ, nextS, next, nextAllocator, nextWindow, ?_, nextMode, record, lastBound, ?_, ?_⟩
  · simp only [credit, empty, noOutput, List.nil_append]
  · rw [nextLast]; exact last
  · have advanced := view.advance (bytesBits (input.take used))
    simpa only [credit, bytesBits_append, word] using advanced

theorem codelens_wait_last {h after readHeap : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s readState returned : InflateState} {flush rc : Int32}
    {input output : List UInt8} {used : Nat} {regs : IL}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (actual : DataStep .inflate h after r flush rc input output used)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (mode : s.mode = CODELENS) (window : s.wsize = 0)
    (readRun : runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      .ok ((.error Ex.leave, regs), readHeap)) (readGet : readHeap.istates zs = some readState)
    (returnedGet : after.istates zs = some returned) : returned.last = s.last := by
  obtain ⟨z0, _returnedZ, get0, _get1, buffers, _header, bytes, _usedEq, _outputBytes, run⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := s) bytes initial.held
  have allocated := default_origin_syncAlloc initial
  have view0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨view.have_eq, ?_, view.hold_lt⟩
    rcases view.next with null | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨outcome, regs0, heap0, readActual, full, _cursor⟩ :=
    clRead_run_full_cursor (c := ⟨some r, some (.tab zs), syncBuf h, flush⟩) rfl rfl
      allocated.good.live.hz allocated.good.live.hs initial.good.inv.wf.1 mode initial.lengths view0
  rw [readRun] at readActual
  cases readActual
  obtain ⟨state0, _used0, stateGet, _bound, _inv, _shape, _bits, frame, _rest⟩ := full.1
  have sameState : state0 = readState := Option.some.inj (stateGet.symm.trans readGet)
  subst state0
  obtain ⟨rc0, heap0, stream1, state1, publicRun, final, _allocator, _freed, leaveFrame, _nextIn, _availIn, _nextOut, _availOut⟩ :=
    codelens_wait_public initial allocator buffers nonnull inputValid view mode window readRun readGet
  have same := Except.ok.inj (publicRun.symm.trans run)
  cases same
  have sameReturned : state1 = returned := Option.some.inj (final.good.live.hs.symm.trans returnedGet)
  subst state1
  rw [leaveFrame, frame]
  rfl

theorem Meaning.code_wait {h after readHeap : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {regs : IL}
    {stream0 : ZStream} {observedState readState : InflateState}
    (before : Meaning .code h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (nonnull : stream0.next_out ≠ .null) (inputValid : stream0.next_in = .null → stream0.avail_in = 0)
    (actual : DataStep .inflate h after r flush rc input output used)
    (readRun : runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs stream0 observedState) (syncAlloc h) =
      .ok ((.error Ex.leave, regs), readHeap)) (readGet : readHeap.istates zs = some readState)
    (readMode : readState.mode = CODELENS) : Meaning .code after r zs (credit log input output used rc) := by
  obtain ⟨z, state, current, allocator, window, empty, mode, record, received, lastBound, last, view,
    litCount, distCount, codeCount, contents, ordinary, consumed, source, trace⟩ := before
  have sameZ : stream0 = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : observedState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst stream0 observedState
  obtain ⟨nextZ, nextS, consumed2, next, nextAllocator, noOutput, _bound, nextMode, nextWindow,
    nextCode, nextLit, nextDist, nextCodes, nextRoot, source2, trace2⟩ :=
    codelens_wait_observed current allocator actual nonnull inputValid mode window contents ordinary readRun readGet readMode
  have nextLast := codelens_wait_last current allocator actual nonnull inputValid mode window readRun readGet next.good.live.hs
  refine ⟨nextZ, nextS, next, nextAllocator, nextWindow, ?_, nextMode, record,
    received ++ bytesBits (input.take used), lastBound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, consumed ++ consumed2, ?_, ?_⟩
  · simp only [credit, empty, noOutput, List.nil_append]
  · rw [nextLast]; exact last
  · simpa only [credit, bytesBits_append] using view.advance (bytesBits (input.take used))
  · rw [nextLit]; exact litCount
  · rw [nextDist]; exact distCount
  · rw [nextCode]; exact codeCount
  · rw [nextCodes, nextRoot]; exact contents
  · rw [nextCodes, nextRoot]; exact ordinary
  · rw [source, List.append_assoc, source2, ← List.append_assoc]
  · have combined := trace.trans trace2
    simpa only [nextLit, nextDist] using combined

#print axioms Meaning.table_wait
#print axioms codelens_wait_last
#print axioms Meaning.code_wait
end Zlib.Inflate.Proofs.HeaderPhaseView
