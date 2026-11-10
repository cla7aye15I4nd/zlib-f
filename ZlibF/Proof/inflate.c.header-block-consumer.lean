import ZlibF.Proof.«inflate.c.header-head-consumer»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem block_entry_source {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      DefaultStateJ after r zs z state ∧ Env c after r zs z state ∧
      DispatchBuffers after r (dispatchRegs z state) bs ∧
      (dispatchRegs z state).bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      after = setI h zs state ∧
      state = (if s.mode = TYPE then { s with mode := TYPEDO } else s) := by
  let good := invariant.good
  let tables := invariant.tables
  let pending := invariant.pending
  let hold := invariant.held
  obtain ⟨after, state, run, finalGood, env, output, sizes, frame, heapEq, stateEq⟩ :=
    inflate_run_output_entry_frame_state E good buffers nonnull
  have currentBuffers : StreamBuffers after r := by
    obtain ⟨stream, streamGet, input, out, separate⟩ := buffers
    have eq : stream = z := Option.some.inj (streamGet.symm.trans good.live.hz)
    subst stream
    refine ⟨z, finalGood.live.hz, ?_, ?_, separate⟩
    · apply callerRange_transport good finalGood (by rw [frame]) _ _ input
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    · apply callerRange_transport good finalGood (by rw [frame]) _ _ out
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
  obtain ⟨bs, inv, separate⟩ := dispatchRegs_input (s := state) finalGood.live.hz currentBuffers inputValid
    (by rw [frame]; exact hold)
  have input : CallerRange after r z.next_in z.avail_in.toNat false := by
    obtain ⟨stream, get, input, _⟩ := currentBuffers
    have eq : stream = z := Option.some.inj (get.symm.trans finalGood.live.hz)
    subst stream
    exact input
  have finalTables : DataTableInvariant after state := by
    by_cases type : s.mode = TYPE
    · intro active
      rw [stateEq, if_pos type] at active
      change DataTableMode TYPEDO at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;> contradiction
    · have sameState : state = s := by rw [stateEq, if_neg type]
      have sameHeap : after = h := by rw [heapEq, sameState]; simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  have finalPending : DataPendingInvariant state := by
    by_cases type : s.mode = TYPE
    · apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
      rw [stateEq, if_pos type]
      change TYPEDO ≠ LENEXT ∧ TYPEDO ≠ DIST ∧ TYPEDO ≠ DISTEXT ∧ TYPEDO ≠ MATCH
      decide
    · rw [stateEq, if_neg type]
      exact pending
  have finalJ : DefaultStateJ after r zs z state := by
    by_cases type : s.mode = TYPE
    · have blockFrame : BlockHeaderFrame s state := by rw [stateEq, if_pos type]; rfl
      have modes : BlockControlMode state.mode := by
        rw [stateEq, if_pos type]
        exact Or.inr (Or.inl rfl)
      have format := invariant.block_format (Or.inl type)
      have base := invariant.toDefaultDecodeJ.block_update finalGood finalTables finalPending blockFrame modes format sizes
        (by rw [heapEq]; rfl)
      exact invariant.config_update base frame.default_config format
    · have sameState : state = s := by rw [stateEq, if_neg type]
      have sameHeap : after = h := by rw [heapEq, sameState]; simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  exact ⟨after, state, bs, run, finalJ, env, ⟨input, output, separate, inv⟩,
    finalGood.inv.bits, sizes, frame, heapEq, stateEq⟩

/-- With no new block bits, the real entry normalizes TYPE to TYPEDO,
then returns through the original public cleanup. The cumulative wrapper
source remains available for a later dynamic header call. -/
theorem Meaning.block_wait {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {stream0 : ZStream}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (before : Meaning .block h r zs log) (get : r.get h = some stream0)
    (emptyInput : stream0.avail_in = 0)
    (nonnull : stream0.next_out ≠ .null)
    (actual : DataStep .inflate h after r flush rc input output used) :
    Meaning .block after r zs (credit log input output used rc) := by
  obtain ⟨z, s, initial, allocator, window, empty, modes, last, bits0, hold0, header, view⟩ := before
  have same : stream0 = z := Option.some.inj (get.symm.trans initial.good.live.hz)
  subst stream0
  obtain ⟨z0, returned, get0, get1, buffers, active, inputBytes, usedEq, outputBytes, run⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have inputValid : z.next_in = .null → z.avail_in = 0 := by intro _; exact emptyInput
  have allocated := default_origin_syncAlloc initial
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨entryHeap, entryS, bs, entryRun, entryJ, entryEnv, packet, entryBits, _sizes, frame, heapEq, stateEq⟩ :=
    block_entry_source env allocated.toDefaultStateJ (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
  have entryLast : entryS.last = 0 := by rw [frame]; exact last
  have entryZero : entryS.bits = 0 := by rw [frame]; exact bits0
  have entryHold : entryS.hold = 0 := by rw [frame]; exact hold0
  have entryMode : entryS.mode = TYPEDO := by
    rw [stateEq]
    rcases modes with mode | mode
    · simp only [mode, ↓reduceIte]
    · have noType : s.mode ≠ TYPE := by rw [mode]; decide
      rw [if_neg noType]; exact mode
  have noBytes : bs = [] := by
    have length := packet.bits.have_eq
    change z.avail_in.toNat = bs.length at length
    rw [emptyInput, UInt32.toNat_zero] at length
    exact List.length_eq_zero_iff.mp length.symm
  subst bs
  obtain ⟨outcome, regs, count, pull, bound, inv, _source, bitCount, shape,
    _max, _same, full, wait, kinds, cursor⟩ := NEEDBITS_run_cursor packet.bits 3 (by decide)
  have zeroCount : count = 0 := by simpa only [List.length_nil, Nat.le_zero] using bound
  have regBits : regs.bits = 0 := UInt32.toNat_inj.mp (by
    simpa only [dispatchRegs, entryZero, UInt32.toNat_zero, zeroCount, Nat.mul_zero, Nat.zero_add] using bitCount)
  have regHold : regs.hold = 0 := UInt64.toNat_inj.mp (by
    have below := inv.hold_lt
    rw [regBits] at below
    change regs.hold.toNat < 1 at below
    have : regs.hold.toNat = 0 := by omega
    exact this)
  have regHave : regs.have_ = 0 := UInt32.toNat_inj.mp (by simpa using inv.have_eq)
  have sourceError : outcome = .error Ex.leave := by
    rcases kinds with normal | leave
    · have enough := full normal
      rw [regBits] at enough
      contradiction
    · exact leave
  have regSame : regs = dispatchRegs z entryS := by
    rw [shape, cursor, zeroCount, inputAdvance_zero, regBits, regHold, regHave]
    change { dispatchRegs z entryS with next := z.next_in, have_ := 0, hold := 0, bits := 0 } = dispatchRegs z entryS
    simp only [dispatchRegs, emptyInput, entryZero, entryHold]
  rw [regSame] at pull
  have typeRun := inflate_TYPEDO_wait entryEnv (dispatchRegs z entryS) (dispatchRegs z entryS) entryLast Ex.leave (by rwa [sourceError] at pull)
  have dispatch : runX (inflate_dispatch c) (dispatchRegs z entryS) entryHeap =
      .ok ((.error Ex.leave, dispatchRegs z entryS), entryHeap) := by
    rw [inflate_dispatch_block_type entryEnv (dispatchRegs z entryS) (Or.inr entryMode)]
    rw [if_neg (by rw [entryMode]; decide : entryS.mode ≠ TYPE)]
    exact typeRun
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z entryS) (fun _ => entryHeap) 0
    (by unfold fuel; decide) Ex.leave (dispatchRegs z entryS) entryHeap (by intro j impossible; omega) dispatch
  have mainRun := entryRun.trans loop
  have entryWindow : entryS.wsize = 0 := by rw [frame]; exact window
  obtain ⟨nextZ, nextS, next, nextAllocator, metadata, _nextIn, nextAvail, _nextOut, nextLeft⟩ :=
    HeaderPublicObserver.actual_wait_from_init history scope
      ⟨z, returned, initial.good.live.hz, get1, buffers, active, inputBytes, usedEq, outputBytes, run⟩
      initial.good.live.hz initial.good.live.zst initial.good.live.hs nonnull inputValid mainRun entryEnv.hs entryWindow rfl
  have sameReturned : returned = nextZ := Option.some.inj (get1.symm.trans next.good.live.hz)
  subst returned
  have zeroUsed : used = 0 := by rw [usedEq, nextAvail]; exact Nat.sub_self _
  have noOutput : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [nextLeft] at length
    change output.length = z.avail_out.toNat - z.avail_out.toNat at length
    rw [Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  refine ⟨nextZ, nextS, next, nextAllocator, ?_, ?_, Or.inr ?_, ?_, ?_, ?_, header, ?_⟩
  · rw [metadata]; exact entryWindow
  · simp only [credit, empty, noOutput, List.nil_append]
  · rw [metadata]; exact entryMode
  · rw [metadata]; exact entryLast
  · rw [metadata]; exact entryZero
  · rw [metadata]; exact entryHold
  · simpa only [credit, zeroUsed, List.take_zero, List.append_nil] using view

theorem block_last_bit (l : IL) :
    (u2i (l.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1))).toInt = (l.hold.toNat % 2 : Nat) := by
  have word : (l.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)).toNat = l.hold.toNat % 2 := by
    rw [land_mask32 _ 1 _ (by decide), UInt64.toNat_toUInt32]
    change l.hold.toNat % 4294967296 % 2 = l.hold.toNat % 2
    exact Nat.mod_mod_of_dvd _ (by decide)
  unfold u2i
  rw [Int32.toInt_ofInt_of_le (by omega) (by omega), word]

#print axioms block_entry_source
#print axioms Meaning.block_wait
#print axioms block_last_bit
end Zlib.Inflate.Proofs.HeaderPhaseView
