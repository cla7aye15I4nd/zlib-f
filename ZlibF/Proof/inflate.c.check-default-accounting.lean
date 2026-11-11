import ZlibF.Math.«counter-accounting»
import ZlibF.Proof.«inflate.c.trailer-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Crediting the old output segment and rebasing preserves one modular
64-bit output account. No total-stream-length bound is needed. -/
theorem check_output_credit (total : UInt64) (l : IL) (count : l.left.toNat ≤ l.out_.toNat) :
    (total + (l.out_ - l.left).toUInt64) + l.left.toUInt64 = total + l.out_.toUInt64 := by
  exact ZlibF.Math.CounterAccounting.charge_rebase total l.out_ l.left count

/-- Actual CHECK executes its real checksum callee and LENGTH continuation
while retaining the full default state, exact public buffers and strict
rank. Output accounting is performed once before checksum acceptance. -/
theorem inflate_CHECK_default_state_accounting_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_CHECK c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) ∧
      stream.total_in = z.total_in ∧ regs.in_ = l.in_ ∧ regs.out_.toNat ≤ l.out_.toNat ∧
      (regs.out_ = l.out_ ∨ (outcome = .error Ex.leave ∧ (regs.ret = Z_STREAM_END ∨ state.mode = LENGTH)) ∨
        (outcome = .ok () ∧ state.mode = BAD)) ∧
      stream.total_out + regs.out_.toUInt64 = z.total_out + l.out_.toUInt64 := by
  let good := invariant.good
  let pending := invariant.pending
  have wrapper := invariant.trailer (Or.inl mode)
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  by_cases raw : s.wrap = 0
  · let state0 := { s with mode := LENGTH }
    let heap0 := setI h zs state0
    have good0 : Good heap0 r zs z state0 :=
      good.decode_update (by rfl) (by change HEAD ≤ LENGTH ∧ LENGTH ≤ SYNC; decide)
    have E0 : Env c heap0 r zs z state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant state0 := by
      apply dataPendingInvariant_idle (s := state0) pending.sane
      change LENGTH ≠ LENEXT ∧ LENGTH ≠ DIST ∧ LENGTH ≠ DISTEXT ∧ LENGTH ≠ MATCH
      decide
    have packet0 : DispatchBuffers heap0 r l bs := by
      simpa only [List.drop_zero] using buffers.consume good good0 rfl
        (fun ref => byte_view_get_setI h zs state0 ref) (fun ref => byte_view_ro_setI h zs state0 ref)
        (regs := l) (used := 0) (by rfl) (inputAdvance_zero l.next).symm (by omega)
        (by simpa only [List.drop_zero] using buffers.bits.decode_update zs state0)
    obtain ⟨run, current, tables, nextPending, packet, sizes⟩ :=
      inflate_LENGTH_default_boundary E0 good0 pending0 packet0 (Or.inl raw)
    have final := invariant.trailer_update (Or.inl mode) current tables nextPending (by rfl)
      (Or.inr (Or.inr (Or.inl rfl))) ((byte_view_sizes_setI h zs state0).trans sizes) rfl
    refine ⟨.error Ex.leave, { l with ret := Z_STREAM_END }, _, z, { state0 with mode := DONE }, 0,
      by omega, (inflate_CHECK_nowrap E.st E.hs raw).trans run, final,
      by simpa only [List.drop_zero] using packet, (byte_view_sizes_setI h zs state0).trans sizes,
      (inputAdvance_zero l.next).symm, by rfl, rfl, rfl, incoming, by rfl, Or.inl rfl, rfl, rfl, Nat.le_refl _, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩), rfl⟩
  · obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, bitCount, shape,
      bitBound, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
    change current.bits.toNat ≤ max l.bits.toNat 39 at bitBound
    have count : current.have_.toNat + used = l.have_.toNat := by
      rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
      omega
    have put : current.put = l.put := by rw [shape]
    have left : current.left = l.left := by rw [shape]
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl)
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
        have final := invariant.trailer_update (Or.inl mode) currentGood tables nextPending (by rfl)
          (Or.inr (Or.inr (Or.inr rfl))) (sizes0.trans sizes) (static.trans static0)
        refine ⟨.ok (), { current with out_ := l.left }, _, _, { state0 with mode := BAD }, used,
          usedBound, run, final, rebased, sizes0.trans sizes, cursor, count,
          put, left, by change current.bits.toNat ≤ 39; omega, static.trans static0, Or.inr ⟨rfl, ?_⟩, rfl,
          (by change current.in_ = l.in_; rw [shape]), buffers.output.count, Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
        · apply dispatchRank_advance (l := l) (used := used) (made := 0) count
          · change current.left.toNat + 0 = l.left.toNat
            rw [left]
            rfl
          · change current.bits.toNat ≤ l.bits.toNat + 8 * used
            omega
          · right
            change dispatchCredit BAD < dispatchCredit s.mode
            rw [mode]
            decide
        · exact check_output_credit z.total_out l buffers.output.count
      · let state1 := { state0 with mode := LENGTH }
        let heap1 := setI heap0 zs state1
        let first := { current with out_ := l.left, hold := 0, bits := 0 }
        have good1 : Good heap1 r zs stream0 state1 :=
          good0.decode_update (by rfl) (by change HEAD ≤ LENGTH ∧ LENGTH ≤ SYNC; decide)
        have E1 : Env c heap1 r zs stream0 state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
        have pending1 : DataPendingInvariant state1 := by
          apply dataPendingInvariant_idle (s := state1) pending0.sane
          change LENGTH ≠ LENEXT ∧ LENGTH ≠ DIST ∧ LENGTH ≠ DISTEXT ∧ LENGTH ≠ MATCH
          decide
        have basePacket : DispatchBuffers heap0 r first (bs.drop used) := by
          simpa only [first, left] using packet0.rebase_output.clear_bits
        have packet1 : DispatchBuffers heap1 r first (bs.drop used) := by
          simpa only [List.drop_zero] using basePacket.consume good0 good1 rfl
            (fun ref => byte_view_get_setI heap0 zs state1 ref) (fun ref => byte_view_ro_setI heap0 zs state1 ref)
            (regs := first) (used := 0) (by rfl) (inputAdvance_zero first.next).symm (by omega)
            (by simpa only [List.drop_zero] using basePacket.bits.decode_update zs state1)
        have tables1 : DataTableInvariant heap1 state1 :=
          dataTableInvariant_inactive (by change ¬ DataTableMode LENGTH; unfold DataTableMode; decide)
        have sizes1 : ByteViewSizes h heap1 := sizes0.trans (byte_view_sizes_setI heap0 zs state1)
        have J1 : DefaultStateJ heap1 r zs stream0 state1 :=
          invariant.trailer_update (Or.inl mode) good1 tables1 pending1 (by rfl)
            (Or.inr (Or.inl rfl)) sizes1 (by change heap0.static = h.static; exact static0)
        obtain ⟨outcome2, regs2, after2, stream2, state2, used2, bound2, run2, final2, packet2, sizes2,
          next2, count2, put2, left2, bits2, static2, progress2, in2, out2, streamFrame, okBad, leaveEnd⟩ :=
          inflate_LENGTH_state_rank E1 J1 packet1 rfl (by change 0 ≤ 39; decide)
        have result := (acceptedRun invalid).trans run2
        have total : used + used2 ≤ bs.length := by
          simp only [List.length_drop] at bound2
          omega
        have firstRank : dispatchRank first LENGTH < dispatchRank l s.mode := by
          apply dispatchRank_advance (l := l) (regs := first) (used := used) (made := 0)
            (by change current.have_.toNat + used = _; exact count)
          · change current.left.toNat + 0 = l.left.toNat
            rw [left]
            rfl
          · change 0 ≤ l.bits.toNat + 8 * used
            omega
          · right
            rw [mode]
            decide
        have streamTotals : stream2.total_in = stream0.total_in ∧ stream2.total_out = stream0.total_out := by
          rw [streamFrame]
          exact ⟨rfl, rfl⟩
        have outFirst : regs2.out_ = l.left := out2
        refine ⟨outcome2, regs2, after2, stream2, state2, used + used2, total, result, final2,
          by simpa only [List.drop_drop, Nat.add_comm] using packet2, sizes1.trans sizes2,
          by rw [next2]; show inputAdvance current.next used2 = _; rw [cursor, inputAdvance_add],
          by change regs2.have_.toNat + used2 = current.have_.toNat at count2; omega,
          put2.trans put, left2.trans left, bits2,
          static2.trans (by change heap0.static = h.static; exact static0), ?_,
          streamTotals.1, in2.trans (by change current.in_ = l.in_; rw [shape]),
          by rw [outFirst]; exact buffers.output.count, ?_, ?_⟩
        · rcases progress2 with leave | ⟨normal, smaller⟩
          · exact Or.inl leave
          · exact Or.inr ⟨normal, Nat.lt_trans smaller firstRank⟩
        · cases outcome2 with
          | error exit =>
            rcases progress2 with leave | ⟨normal, _⟩
            · exact Or.inr (Or.inl ⟨leave, leaveEnd leave⟩)
            · cases normal
          | ok unit =>
            cases unit
            exact Or.inr (Or.inr ⟨rfl, okBad rfl⟩)
        · rw [streamTotals.2, outFirst]
          exact check_output_credit z.total_out l buffers.output.count
    · obtain ⟨_, _, _, run⟩ := waitRun wait
      exact ⟨.error Ex.leave, current, h, z, s, used, usedBound, run, invariant,
        packet, ByteViewSizes.refl h, cursor, count, put, left, by omega, rfl, Or.inl rfl, rfl,
        (by rw [shape]), (by rw [shape]; exact Nat.le_refl _), Or.inl (by rw [shape]), (by rw [shape])⟩


#print axioms inflate_CHECK_default_state_accounting_rank
end Zlib.Inflate.Proofs
