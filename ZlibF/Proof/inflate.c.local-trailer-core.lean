import ZlibF.Proof.«inflate.c.local-dictionary-state»
import ZlibF.Proof.«inflate.c.check-dispatch»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem leaveOutputView_of_cursor {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {l : IL} (good : LocalGood h cutoff r zs z s) (output : OutputCursorInvariant h r l) :
    LeaveOutputView h l := by
  obtain ⟨ref, array, off, ptr, get, _, room, count, made, _⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  refine ⟨ref, off, array, ptr, get, ?_, by omega⟩
  rw [UInt32.toNat_sub_of_le _ _ count]
  exact made


theorem check_account_packet {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (out : UInt32) (v : UInt64) :
    LocalGood (chkH h r zs z s out v) cutoff r zs (chkZ z s out v) (chkS s out v) ∧
      DataPendingInvariant (chkS s out v) ∧ DispatchBuffers (chkH h r zs z s out v) r l bs ∧
      ByteViewSizes h (chkH h r zs z s out v) ∧ (chkH h r zs z s out v).static = h.static := by
  have nextGood : LocalGood (chkH h r zs z s out v) cutoff r zs (chkZ z s out v) (chkS s out v) :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl good.live.mode
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have views : ∀ ref : BRef, Space.get (chkH h r zs z s out v) ref = Space.get h ref := by
    intro ref
    rw [chkH, byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro (chkH h r zs z s out v) ref = Space.ro h ref := by
    intro ref
    rw [chkH, byte_view_ro_setI, byte_view_ro_stream_put]
  refine ⟨nextGood, ?_, ?_, ?_, ?_⟩
  · apply dataPendingInvariant_idle (s := chkS s out v) pending.sane
    change s.mode ≠ LENEXT ∧ s.mode ≠ DIST ∧ s.mode ≠ DISTEXT ∧ s.mode ≠ MATCH
    rw [mode]
    decide
  · simpa only [List.drop_zero] using dispatch_consume_local buffers good nextGood rfl views readonly
      (regs := l) (used := 0) (by rfl) (inputAdvance_zero l.next).symm (by omega)
      (by simpa only [List.drop_zero] using buffers.bits.byte_views views)
  · intro ref
    rw [views]
  · simp only [chkH, setI, ZStreamRef.put_static]

theorem inflate_LENGTH_default_boundary {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (wrapper : s.wrap = 0 ∨ s.flags = 0) :
    runX (inflate_LENGTH c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }),
      setI h zs { s with mode := DONE }) ∧
      LocalGood (setI h zs { s with mode := DONE }) cutoff r zs z { s with mode := DONE } ∧
      DataTableInvariant (setI h zs { s with mode := DONE }) { s with mode := DONE } ∧
      DataPendingInvariant { s with mode := DONE } ∧
      DispatchBuffers (setI h zs { s with mode := DONE }) r { l with ret := Z_STREAM_END } bs ∧
      ByteViewSizes h (setI h zs { s with mode := DONE }) := by
  have nextGood : LocalGood (setI h zs { s with mode := DONE }) cutoff r zs z { s with mode := DONE } :=
    good.decode_after (by rfl) (by change HEAD ≤ DONE ∧ DONE ≤ SYNC; decide)
  have views : ∀ ref : BRef, Space.get (setI h zs { s with mode := DONE }) ref = Space.get h ref :=
    fun ref => byte_view_get_setI h zs _ ref
  have bits : BitInv (setI h zs { s with mode := DONE }) { l with ret := Z_STREAM_END } bs :=
    ⟨buffers.bits.have_eq, (buffers.bits.byte_views views).next, buffers.bits.hold_lt⟩
  refine ⟨inflate_LENGTH_skip E.st E.hs wrapper, nextGood, ?_, ?_, ?_, ?_⟩
  · exact dataTableInvariant_inactive (by change ¬ DataTableMode DONE; unfold DataTableMode; decide)
  · apply dataPendingInvariant_idle (s := { s with mode := DONE }) pending.sane
    change DONE ≠ LENEXT ∧ DONE ≠ DIST ∧ DONE ≠ DISTEXT ∧ DONE ≠ MATCH
    decide
  · simpa only [List.drop_zero] using dispatch_advance_both_local buffers good nextGood rfl
      (byte_view_sizes_setI h zs _) (fun ref => byte_view_ro_setI h zs _ ref) (regs := { l with ret := Z_STREAM_END }) (used := 0) (made := 0)
      (by simp only [inputAdvance_zero]) (by rfl) (by simp only [inputAdvance_zero]) (by rfl) rfl
      (by simpa only [List.drop_zero] using bits)
  · exact byte_view_sizes_setI h zs _

theorem inflate_CHECK_default_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (mode : s.mode = CHECK) (wrapper : s.wrap = 0 ∨ s.flags = 0) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_CHECK c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  by_cases raw : s.wrap = 0
  · let state0 := { s with mode := LENGTH }
    let heap0 := setI h zs state0
    have good0 : LocalGood heap0 cutoff r zs z state0 :=
      good.decode_after (by rfl) (by change HEAD ≤ LENGTH ∧ LENGTH ≤ SYNC; decide)
    have E0 : Env c heap0 r zs z state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant state0 := by
      apply dataPendingInvariant_idle (s := state0) pending.sane
      change LENGTH ≠ LENEXT ∧ LENGTH ≠ DIST ∧ LENGTH ≠ DISTEXT ∧ LENGTH ≠ MATCH
      decide
    have packet0 : DispatchBuffers heap0 r l bs := by
      simpa only [List.drop_zero] using dispatch_consume_local buffers good good0 rfl
        (fun ref => byte_view_get_setI h zs state0 ref) (fun ref => byte_view_ro_setI h zs state0 ref)
        (regs := l) (used := 0) (by rfl) (inputAdvance_zero l.next).symm (by omega)
        (by simpa only [List.drop_zero] using buffers.bits.decode_update zs state0)
    obtain ⟨run, current, tables, nextPending, packet, sizes⟩ :=
      inflate_LENGTH_default_boundary E0 good0 pending0 packet0 (Or.inl raw)
    refine ⟨.error Ex.leave, { l with ret := Z_STREAM_END }, _, z, { state0 with mode := DONE }, 0,
      by omega, (inflate_CHECK_nowrap E.st E.hs raw).trans run, current, tables, nextPending,
      by simpa only [List.drop_zero] using packet, (byte_view_sizes_setI h zs state0).trans sizes,
      (inputAdvance_zero l.next).symm, by rfl, rfl, rfl, incoming, by rfl, Or.inl rfl⟩
  · have flags : s.flags = 0 := wrapper.resolve_left raw
    obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, bitCount, shape,
      bitBound, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
    change current.bits.toNat ≤ max l.bits.toNat 39 at bitBound
    have count : current.have_.toNat + used = l.have_.toNat := by
      rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
      omega
    have put : current.put = l.put := by rw [shape]
    have left : current.left = l.left := by rw [shape]
    have packet : DispatchBuffers h r current (bs.drop used) :=
      dispatch_consume_local buffers good good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl)
        cursor usedBound bitInv
    obtain ⟨rr, regs, j, read, jBound, inv, _, waitRun, fullRun⟩ :=
      inflate_CHECK_views_run (l.out_ - l.left) rfl E.strm E.st E.hz E.hs raw buffers.bits statics
        (fun _ => leaveOutputView_of_cursor good buffers.output)
    rw [pull] at read
    cases read
    have jEq : j = used := by
      have one := inv.have_eq
      have two := bitInv.have_eq
      rw [List.length_drop] at one two
      omega
    subst j
    rcases kinds with normal | wait
    · obtain ⟨_, v, badRun, acceptedRun⟩ := fullRun normal
      let out := l.out_ - l.left
      let stream0 := chkZ z s out v
      let state0 := chkS s out v
      let heap0 := chkH h r zs z s out v
      obtain ⟨good0, pending0, packet0, sizes0, static0⟩ := check_account_packet good pending packet mode out v
      have E0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧ (if s.flags ≠ 0 then current.hold else ZSWAP32 current.hold) ≠ state0.check
      · obtain ⟨i, _, run⟩ := badRun invalid.1 invalid.2
        obtain ⟨currentGood, tables, nextPending, nextPacket, sizes, static⟩ :=
          head_bad_packet good0 pending0 packet0 packet0.bits (by rfl) i
        have rebased : DispatchBuffers (badHeap heap0 r zs stream0 state0 i) r
            { current with out_ := l.left } (bs.drop used) := by
          simpa only [left] using nextPacket.rebase_output
        refine ⟨.ok (), { current with out_ := l.left }, _, _, { state0 with mode := BAD }, used,
          usedBound, run, currentGood, tables, nextPending, rebased, sizes0.trans sizes, cursor, count,
          put, left, by change current.bits.toNat ≤ 39; omega, static.trans static0, Or.inr ⟨rfl, ?_⟩⟩
        apply dispatchRank_advance (l := l) (used := used) (made := 0) count
        · change current.left.toNat + 0 = l.left.toNat
          rw [left]
          rfl
        · change current.bits.toNat ≤ l.bits.toNat + 8 * used
          omega
        · right
          change dispatchCredit BAD < dispatchCredit s.mode
          rw [mode]
          decide
      · let state1 := { state0 with mode := LENGTH }
        let heap1 := setI heap0 zs state1
        let first := { current with out_ := l.left, hold := 0, bits := 0 }
        have good1 : LocalGood heap1 cutoff r zs stream0 state1 :=
          good0.decode_after (by rfl) (by change HEAD ≤ LENGTH ∧ LENGTH ≤ SYNC; decide)
        have E1 : Env c heap1 r zs stream0 state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
        have pending1 : DataPendingInvariant state1 := by
          apply dataPendingInvariant_idle (s := state1) pending0.sane
          change LENGTH ≠ LENEXT ∧ LENGTH ≠ DIST ∧ LENGTH ≠ DISTEXT ∧ LENGTH ≠ MATCH
          decide
        have basePacket : DispatchBuffers heap0 r first (bs.drop used) := by
          simpa only [first, left] using packet0.rebase_output.clear_bits
        have packet1 : DispatchBuffers heap1 r first (bs.drop used) := by
          simpa only [List.drop_zero] using dispatch_consume_local basePacket good0 good1 rfl
            (fun ref => byte_view_get_setI heap0 zs state1 ref) (fun ref => byte_view_ro_setI heap0 zs state1 ref)
            (regs := first) (used := 0) (by rfl) (inputAdvance_zero first.next).symm (by omega)
            (by simpa only [List.drop_zero] using basePacket.bits.decode_update zs state1)
        obtain ⟨run, currentGood, tables, nextPending, nextPacket, sizes⟩ :=
          inflate_LENGTH_default_boundary E1 good1 pending1 packet1 (Or.inr flags)
        have result := (acceptedRun invalid).trans run
        refine ⟨.error Ex.leave, { first with ret := Z_STREAM_END }, _, stream0,
          { state1 with mode := DONE }, used, usedBound, result, currentGood, tables, nextPending,
          nextPacket, (sizes0.trans (byte_view_sizes_setI heap0 zs state1)).trans sizes, cursor, count,
          put, left, by change 0 ≤ 39; decide, ?_, Or.inl rfl⟩
        change heap0.static = h.static
        exact static0
    · obtain ⟨_, _, _, run⟩ := waitRun wait
      exact ⟨.error Ex.leave, current, h, z, s, used, usedBound, run, good,
        dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending,
        packet, ByteViewSizes.refl h, cursor, count, put, left, by omega, rfl, Or.inl rfl⟩

#print axioms check_account_packet
#print axioms inflate_LENGTH_default_boundary
#print axioms inflate_CHECK_default_rank
end Zlib.Inflate.Local
