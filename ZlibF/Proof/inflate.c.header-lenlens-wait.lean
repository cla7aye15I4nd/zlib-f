import ZlibF.Proof.«inflate.c.header-lenlens-consumer»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser Zlib.Inflate.Proofs.CumulativeBoundary
set_option autoImplicit false

theorem Meaning.lens_wait {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {stream0 : ZStream} {observedState : InflateState}
    (before : Meaning .lens h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (nonnull : stream0.next_out ≠ .null) (inputValid : stream0.next_in = .null → stream0.avail_in = 0)
    (short : (stream (dispatchRegs stream0 observedState) input).length <
      3 * (observedState.ncode.toNat - observedState.«have».toNat))
    (actual : DataStep .inflate h after r flush rc input output used) :
    Meaning .lens after r zs (credit log input output used rc) := by
  obtain ⟨z, state, current, allocator, window, empty, mode, record, received, lastBound, last, countsView,
    litCount, distCount, codeCount, progress⟩ := before
  have sameZ : stream0 = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : observedState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst stream0 observedState
  obtain ⟨z0, returned, get0, get1, buffers, _header, bytes, usedEq, outputBytes, actualRun⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := state) bytes current.held
  have allocated := default_origin_syncAlloc current
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z state := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have view0 : BitInv (syncAlloc h) (dispatchRegs z state) input := by
    refine ⟨view.have_eq, ?_, view.hold_lt⟩
    rcases view.next with null | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc current.good.fresh get).1, bound, values⟩
  obtain ⟨ncode, haveBound, _nlen, _ndist, _good⟩ := current.headerLengths mode
  obtain ⟨outcome, regs, readUsed, count, countEq, readRun, readBound, _readB, nextProgress⟩ :=
    ll1_header_progress env.st env.hs current.good.inv.wf.1 ncode haveBound view0 progress
  obtain ⟨outcome0, regs0, used0, readRun0, _bound0, inv0, _remaining, regShape, wait, _complete⟩ :=
    ll1_run env.st env.hs current.good.inv.wf.1 ncode haveBound view0
  rw [← countEq, readRun] at readRun0
  cases readRun0
  have shortCount : count < state.ncode.toNat - state.«have».toNat := by rw [countEq]; omega
  obtain ⟨leave, _haveZero, _allUsed, _below⟩ := wait (by rw [← countEq]; exact shortCount)
  subst outcome
  have dispatch : runX (inflate_dispatch c) (dispatchRegs z state) (syncAlloc h) =
      .ok ((.error Ex.leave, regs), setI (syncAlloc h) zs (llSt state (stream (dispatchRegs z state) input) count)) := by
    rw [inflate_dispatch_LENLENS env _ mode, inflate_LENLENS_eq, runX_bind, readRun]
  obtain ⟨rc0, heap0, nextZ, nextS, publicRun, nextJ, nextAllocator, _freed, frame, _nextIn, availIn, _nextOut, availOut⟩ :=
    header_dispatch_wait_public (readState := llSt state (stream (dispatchRegs z state) input) count) current allocator buffers nonnull inputValid (by rw [mode]; decide) dispatch
      (by rw [setI_istates_same]) window (by rw [regShape]; rfl)
      (by rw [regShape]; rfl) (by rw [regShape]; rfl)
  have same := Except.ok.inj (publicRun.symm.trans actualRun)
  cases same
  have sameReturned : returned = nextZ := Option.some.inj (get1.symm.trans nextJ.good.live.hz)
  subst returned
  have sameUsed : readUsed = used := by
    have initialHave := view.have_eq
    have finalHave := inv0.have_eq
    have sourceHave := _readB.have_eq
    rw [usedEq, availIn]
    change z.avail_in.toNat = input.length at initialHave
    simp only [List.length_drop] at finalHave sourceHave
    omega
  subst readUsed
  have noOutput : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [availOut, Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  refine ⟨nextZ, nextS, nextJ, nextAllocator, ?_, ?_, ?_, record,
    received ++ bytesBits (input.take used), lastBound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame]; exact window
  · simp only [credit, empty, noOutput, List.nil_append]
  · rw [frame]; exact mode
  · rw [frame]; exact last
  · simpa only [credit, bytesBits_append] using countsView.advance (bytesBits (input.take used))
  · rw [frame]; exact litCount
  · rw [frame]; exact distCount
  · rw [frame]; exact codeCount
  · rw [frame]
    exact nextProgress

#print axioms Meaning.lens_wait
end Zlib.Inflate.Proofs.HeaderPhaseView
