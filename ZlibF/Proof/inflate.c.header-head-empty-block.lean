import ZlibF.Proof.«inflate.c.header-cumulative-entry»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem Meaning.head_complete_empty_block
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (history : InflateDataTrace 15 r h log) (scope : HeaderDataTrace.PlatformScope history)
    (before : Meaning .head h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (exactHeader : log.input.length + input.length = 2)
    (enough : 2 ≤ log.input.length + input.length)
    (accepted : ∀ stream0, r.get h = some stream0 → stream0.next_out ≠ .null ∧
      (stream0.next_in = .null → stream0.avail_in = 0)) :
    ∃ (stream0 : ZStream) (state : InflateState) (pulled : IL) (headerUsed : Nat),
      r.get h = some stream0 ∧ h.istates zs = some state ∧
      runX (NEEDBITS 16) (dispatchRegs stream0 state) (syncAlloc h) = .ok ((.ok (), pulled), syncAlloc h) ∧
      headerUsed ≤ input.length ∧ log.input.length + headerUsed = 2 ∧
      (headHeaderRejected state pulled = false → headMethodRejected pulled = false →
        (headWindowRegs pulled).len.toNat ≤ 15 → headDefaultMode pulled = TYPE →
        used = headerUsed ∧ Meaning .block after r zs (credit log input output used rc)) := by
  obtain ⟨z, s, initial, allocator, window, empty, mode, last, wrap, below, count, word, prefixBound⟩ := before
  have getZ := initial.good.live.hz
  have getS := initial.good.live.hs
  obtain ⟨nonnull, inputValid⟩ := accepted z getZ
  obtain ⟨z0, returned, get0, get1, buffers, activeHeader, inputBytes, usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans getZ)
  subst z0
  have source := header_input_view_of_bytes (s := s) inputBytes initial.held
  have allocated := default_origin_syncAlloc initial
  have input0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨source.have_eq, ?_, source.hold_lt⟩
    rcases source.next with none | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl none
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have output0 := dispatchRegs_output env.hz (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull s
  obtain ⟨z1, gz1, rangeIn, _rangeOut, separate⟩ := streamBuffers_syncAlloc initial.good.fresh buffers
  have sameZ1 : z1 = z := Option.some.inj (gz1.symm.trans env.hz)
  subst z1
  have packet : DispatchBuffers (syncAlloc h) r (dispatchRegs z s) input := ⟨rangeIn, output0, separate, input0⟩
  obtain ⟨pulled, headerUsed, pull, bound, inv, usedCount, read, finish⟩ :=
    EntryPath.HeadHistory.complete_head_type_origin_entry env allocated packet mode (Or.inr wrap) count word prefixBound enough
  refine ⟨z, s, pulled, headerUsed, getZ, getS, pull, bound, usedCount, ?_⟩
  intro header method windowSize noDict
  obtain ⟨headRun, headCurrent, headPacket, headMode, headLast, _headBits⟩ := finish header method windowSize noDict
  let headRegs : IL := { headWindowRegs pulled with hold := 0, bits := 0 }
  let headState := headDefaultState s pulled
  let headHeap := setI (r.put (syncAlloc h) { z with adler := 1 }) zs headState
  have headEnv : Env c headHeap r zs { z with adler := 1 } headState := ⟨rfl, rfl, headCurrent.good.live.hz, headCurrent.good.live.hs⟩
  have remainingNil : input.drop headerUsed = [] := by
    apply List.length_eq_zero_iff.mp
    rw [List.length_drop]
    omega
  have emptyPacket : BitInv headHeap headRegs [] := by simpa only [remainingNil] using headPacket.bits
  have typeWait : runX (inflate_TYPEDO c) headRegs headHeap = .ok ((.error Ex.leave, headRegs), headHeap) := by
    obtain ⟨outcome, regs, used0, pull0, bound0, inv0, _word0, count0, shape0, _max0, _same0, full0, wait0, kinds0, cursor0⟩ :=
      NEEDBITS_run_cursor emptyPacket 3 (by decide)
    have zero : used0 = 0 := by simpa using bound0
    have bitsZero : regs.bits = 0 := UInt32.toNat_inj.mp (by simpa only [headRegs, UInt32.toNat_zero, zero, Nat.mul_zero, Nat.zero_add] using count0)
    have holdZero : regs.hold = 0 := UInt64.toNat_inj.mp (by
      have bound := inv0.hold_lt
      rw [bitsZero] at bound
      change regs.hold.toNat < 1 at bound
      change regs.hold.toNat = 0
      omega)
    have haveZero : regs.have_ = 0 := UInt32.toNat_inj.mp (by simpa using inv0.have_eq)
    have originalHave : headRegs.have_ = 0 := UInt32.toNat_inj.mp (by simpa using emptyPacket.have_eq)
    have sameRegs : regs = headRegs := by
      rw [shape0, cursor0, zero, inputAdvance_zero, bitsZero, holdZero, haveZero]
      change { headRegs with next := headRegs.next, have_ := 0, hold := 0, bits := 0 } = headRegs
      change (headWindowRegs pulled).have_ = 0 at originalHave
      simp only [headRegs, originalHave]
    have error : outcome = .error Ex.leave := by
      rcases kinds0 with normal | error
      · have enough := full0 normal
        rw [bitsZero] at enough
        contradiction
      · exact error
    exact inflate_TYPEDO_wait headEnv headRegs headRegs (headLast.trans last) Ex.leave (by simpa only [error, sameRegs] using pull0)
  have pauseRun : runX (inflate_dispatch c) headRegs headHeap = .ok ((.error Ex.leave, headRegs), headHeap) := by
    rw [inflate_dispatch_block_type headEnv headRegs (Or.inl headMode), if_pos headMode]
    by_cases pause : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
    · exact inflate_TYPE_leave c headRegs headHeap pause
    · rw [inflate_TYPE_go c headRegs headHeap ⟨fun equal => pause (Or.inl equal), fun equal => pause (Or.inr equal)⟩]
      exact typeWait
  have mainRun := head_pause_main_run env mode headRun pauseRun
  obtain ⟨_put, left, out⟩ := CumulativeTableBoundary.needbits_output_fields input0 (by decide : (16 : UInt32).toNat ≤ 49) pull
  have noOutput : headRegs.out_ = headRegs.left := by
    change pulled.out_ = pulled.left
    rw [left, out]
    rfl
  have headWindow : headState.wsize = 0 := window
  obtain ⟨nextZ, nextS, next, nextAllocator, frame, nextIn, nextAvail, nextOut, nextLeft⟩ :=
    HeaderPublicObserver.actual_wait_from_init history scope
      ⟨z, returned, getZ, get1, buffers, activeHeader, inputBytes, usedEq, outputBytes, actual⟩
      getZ initial.good.live.zst getS nonnull inputValid mainRun headCurrent.good.live.hs headWindow noOutput
  have sameReturned : returned = nextZ := Option.some.inj (get1.symm.trans next.good.live.hz)
  subst returned
  have avail : pulled.have_.toNat = (input.drop headerUsed).length := inv.have_eq
  have originalAvail : z.avail_in.toNat = input.length := source.have_eq
  have usedSame : used = headerUsed := by
    rw [usedEq, nextAvail]
    change z.avail_in.toNat - pulled.have_.toNat = headerUsed
    rw [originalAvail, avail, List.length_drop]
    omega
  have noBytes : output = [] := by
    have outputLength := header_observed_bytes_length outputBytes
    rw [nextLeft] at outputLength
    change output.length = z.avail_out.toNat - pulled.left.toNat at outputLength
    rw [left] at outputLength
    change output.length = z.avail_out.toNat - z.avail_out.toNat at outputLength
    rw [Nat.sub_self] at outputLength
    exact List.length_eq_zero_iff.mp outputLength
  have wrapper : View (readBits 16) (pulled.hold.toNat % 2 ^ 16)
      (bytesBits (log.input ++ input.take headerUsed)) [] := by
    apply View.readBits_prefix (remaining := bytesBits (input.drop headerUsed))
    have split : bytesBits (log.input ++ input) =
        bytesBits (log.input ++ input.take headerUsed) ++ bytesBits (input.drop headerUsed) := by
      rw [← bytesBits_append, List.append_assoc, List.take_append_drop]
    rw [← split]
    exact read
  refine ⟨usedSame, nextZ, nextS, next, nextAllocator, ?_, ?_, ?_⟩
  · rw [frame]; exact headWindow
  · simp only [credit, empty, noBytes, List.nil_append]
  · refine ⟨Or.inl ?_, ?_, ?_, ?_, pulled.hold.toNat % 2 ^ 16, ?_⟩
    · rw [frame]; exact headMode
    · rw [frame]; exact headLast.trans last
    · rw [frame]; rfl
    · rw [frame]; rfl
    · simpa only [credit, usedSame] using wrapper


#print axioms Meaning.head_complete_empty_block
end Zlib.Inflate.Proofs.HeaderPhaseView

namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Completing exactly the wrapper bytes, with no block byte yet present,
returns the real public TYPE state for any flush; no forced pause is used. -/
theorem Epoch.head_empty_block {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {history : InflateDataTrace 15 r h log} {flush rc : Int32} {input output : List UInt8} {used : Nat}
    {cmf flg : UInt8} (selected : Epoch r zs .head history)
    (actual : DataStep .inflate h after r flush rc input output used)
    (prefixBytes : log.input ++ input = [cmf, flg]) (valid : Zlib.HeaderOK cmf flg)
    (plain : flg.toNat / 32 % 2 = 0)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    Meaning .block after r zs (credit log input output used rc) := by
  have exactHeader : log.input.length + input.length = 2 := by
    have length := congrArg List.length prefixBytes
    simpa using length
  obtain ⟨z, s, pulled, headUsed, getZ, getS, pull, _bound, _count, complete⟩ :=
    selected.checked.2.head_complete_empty_block history selected.checked.1 actual exactHeader (by omega) accepted
  have source := selected.checked.2.plain_header_source actual (by simpa using prefixBytes) valid plain
  cases source with
  | observed sourceZ sourceS sourceRegs observedZ observedS actualPull header method window noDict =>
    have sameZ : sourceZ = z := Option.some.inj (observedZ.symm.trans getZ)
    have sameS : sourceS = s := Option.some.inj (observedS.symm.trans getS)
    subst sourceZ sourceS
    rw [pull] at actualPull
    cases actualPull
    exact (complete header method window noDict).2

#print axioms Epoch.head_empty_block
end Zlib.Inflate.Proofs.HeaderPhaseView
