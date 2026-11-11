import ZlibF.Proof.«inflate.c.dictionary-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- CHECK changes its checksum/output total and the selected trailer mode. -/
def TrailerFieldsFrame (before after : InflateState) : Prop :=
  after = { before with check := after.check, total := after.total, mode := after.mode }

/-- The actual trailer writes retain reset/header configuration and the
complete default relation on wait, failure and successful completion. -/
theorem DefaultStateJ.trailer_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultStateJ h r zs z s)
    (beforeMode : s.mode = CHECK ∨ s.mode = LENGTH)
    (current : Good after r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (frame : TrailerFieldsFrame s state)
    (modes : state.mode = CHECK ∨ state.mode = LENGTH ∨ state.mode = DONE ∨ state.mode = BAD)
    (sizes : ByteViewSizes h after) (static : after.static = h.static) :
    DefaultStateJ after r zs stream state := by
  have format := invariant.trailer beforeMode
  have guards : state.mode ≠ CODELENS ∧ state.mode ≠ LENLENS ∧ DICTID ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected | selected | selected <;> rw [selected] <;> decide
  have base : DefaultDecodeJ after r zs stream state := by
    refine ⟨current, tables, pending, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr (Or.inl guards.2.2), ?_, ?_, sizes.platform invariant.platform⟩
    · intro active
      exact False.elim (guards.1 active)
    · intro active
      exact False.elim (guards.2.1 active)
    · rw [frame]
      exact invariant.held
    · rw [frame]
      exact invariant.window
    · rw [frame]
      exact invariant.wrapper
    · rw [frame]
      exact invariant.header
    · intro _
      rw [frame]
      exact format
    · change after.static = _
      rw [static]
      exact invariant.globals
  have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact invariant.config_update base config format

/-- Actual default LENGTH has no gzip length word and reaches DONE with
the full default state relation and the original caller byte views. -/
theorem inflate_LENGTH_default_state_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENGTH) (skip : s.wrap = 0 ∨ s.flags = 0) :
    runX (inflate_LENGTH c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }),
      setI h zs { s with mode := DONE }) ∧
      DefaultStateJ (setI h zs { s with mode := DONE }) r zs z { s with mode := DONE } ∧
      DispatchBuffers (setI h zs { s with mode := DONE }) r { l with ret := Z_STREAM_END } bs ∧
      ByteViewSizes h (setI h zs { s with mode := DONE }) := by
  obtain ⟨run, current, tables, pending, packet, sizes⟩ :=
    inflate_LENGTH_default_boundary E invariant.good invariant.pending buffers skip
  have final := invariant.trailer_update (Or.inr mode) current tables pending (by rfl)
    (Or.inr (Or.inr (Or.inl rfl))) sizes rfl
  exact ⟨run, final, packet, sizes⟩

/-- Actual LENGTH for every completed header: with no length word (raw, or
zlib flags 0) it reaches DONE at once; with a gzip header it reads the 32-bit
length, leaves for more input, rejects a wrong length (BAD) or reaches DONE. -/
theorem inflate_LENGTH_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENGTH) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_LENGTH c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) ∧
      (regs.in_ = l.in_ ∧ regs.out_ = l.out_ ∧ HeaderStreamFrame z stream ∧
        (outcome = .ok () → state.mode = BAD) ∧
        (outcome = .error Ex.leave → regs.ret = Z_STREAM_END ∨ state.mode = LENGTH) ∧
        (state.mode = LENGTH ∨ state.mode = BAD ∨ state.mode = DONE) ∧
        (outcome = .error Ex.leave → regs.ret = Z_STREAM_END → l.ret ≠ Z_STREAM_END → state.mode = DONE)) := by
  by_cases skip : s.wrap = 0 ∨ s.flags = 0
  · obtain ⟨run, current, tables, pending, packet, sizes⟩ :=
      inflate_LENGTH_default_boundary E invariant.good invariant.pending buffers skip
    have final := invariant.trailer_update (Or.inr mode) current tables pending (by rfl)
      (Or.inr (Or.inr (Or.inl rfl))) sizes rfl
    exact ⟨.error Ex.leave, { l with ret := Z_STREAM_END }, _, z, _, 0, by omega, run, final,
      by simpa only [List.drop_zero] using packet, sizes, (inputAdvance_zero l.next).symm, by rfl,
      rfl, rfl, incoming, rfl, Or.inl rfl, ⟨rfl, rfl, rfl, (fun e => nomatch e), fun _ => Or.inl rfl,
      Or.inr (Or.inr rfl), fun _ _ _ => rfl⟩⟩
  have hw : s.wrap ≠ 0 := fun zero => skip (Or.inl zero)
  have hf : s.flags ≠ 0 := fun zero => skip (Or.inr zero)
  let good := invariant.good
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, bitCount, shape,
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
    inflate_LENGTH_run E.strm E.st E.hz E.hs hw hf buffers.bits
  rw [pull] at read
  cases read
  have jEq : j = used := by
    have one := inv.have_eq
    have two := bitInv.have_eq
    rw [List.length_drop] at one two
    omega
  subst j
  rcases kinds with normal | wait
  · obtain ⟨_, badRun, acceptedRun⟩ := fullRun normal
    by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧ current.hold ≠ (s.total &&& 0xffffffff)
    · obtain ⟨i, _, run⟩ := badRun invalid.1 invalid.2
      obtain ⟨currentGood, tables, nextPending, nextPacket, sizes, static⟩ :=
        head_bad_packet good invariant.pending packet packet.bits (by rfl) i
      have final := invariant.trailer_update (Or.inr mode) currentGood tables nextPending (by rfl)
        (Or.inr (Or.inr (Or.inr rfl))) sizes static
      refine ⟨.ok (), current, _, _, { s with mode := BAD }, used, usedBound, run, final,
        nextPacket, sizes, cursor, count, put, left, by omega, static, Or.inr ⟨rfl, ?_⟩,
        ⟨by rw [shape], by rw [shape], rfl, fun _ => rfl, (fun e => nomatch e), Or.inr (Or.inl rfl),
          fun e => nomatch e⟩⟩
      apply dispatchRank_advance (l := l) (used := used) (made := 0) count
      · change current.left.toNat + 0 = l.left.toNat
        rw [left]
        rfl
      · omega
      · right
        change dispatchCredit BAD < dispatchCredit s.mode
        rw [mode]
        decide
    · have run := acceptedRun invalid
      let state1 := { s with mode := DONE }
      let heap1 := setI h zs state1
      let first := { current with hold := 0, bits := 0, ret := Z_STREAM_END }
      have good1 : Good heap1 r zs z state1 :=
        good.decode_update (by rfl) (by change HEAD ≤ DONE ∧ DONE ≤ SYNC; decide)
      have tables : DataTableInvariant heap1 state1 :=
        dataTableInvariant_inactive (by change ¬ DataTableMode DONE; unfold DataTableMode; decide)
      have pending1 : DataPendingInvariant state1 := by
        apply dataPendingInvariant_idle (s := state1) invariant.pending.sane
        change DONE ≠ LENEXT ∧ DONE ≠ DIST ∧ DONE ≠ DISTEXT ∧ DONE ≠ MATCH
        decide
      have cleared : DispatchBuffers h r { current with hold := 0, bits := 0 } (bs.drop used) :=
        packet.clear_bits
      have views : ∀ ref : BRef, Space.get heap1 ref = Space.get h ref :=
        fun ref => byte_view_get_setI h zs state1 ref
      have bits1 : BitInv heap1 first (bs.drop used) :=
        ⟨cleared.bits.have_eq, (cleared.bits.byte_views views).next, cleared.bits.hold_lt⟩
      have packet1 : DispatchBuffers heap1 r first (bs.drop used) := by
        simpa only [List.drop_zero] using cleared.advance_both good good1 rfl
          (byte_view_sizes_setI h zs state1) (fun ref => byte_view_ro_setI h zs state1 ref)
          (regs := first) (used := 0) (made := 0)
          (by simp only [inputAdvance_zero]; rfl) (by rfl) (by simp only [inputAdvance_zero]; rfl) (by rfl) rfl
          (by simpa only [List.drop_zero] using bits1)
      have final := invariant.trailer_update (Or.inr mode) good1 tables pending1 (by rfl)
        (Or.inr (Or.inr (Or.inl rfl))) (byte_view_sizes_setI h zs state1) rfl
      exact ⟨.error Ex.leave, first, heap1, z, state1, used, usedBound, run, final, packet1,
        byte_view_sizes_setI h zs state1, cursor, count, put, left, by change 0 ≤ 39; decide, rfl, Or.inl rfl,
        ⟨by change current.in_ = _; rw [shape], by change current.out_ = _; rw [shape], rfl,
        (fun e => nomatch e), fun _ => Or.inl rfl, Or.inr (Or.inr rfl), fun _ _ _ => rfl⟩⟩
  · obtain ⟨_, _, _, run⟩ := waitRun wait
    exact ⟨.error Ex.leave, current, h, z, s, used, usedBound, run, invariant,
      packet, ByteViewSizes.refl h, cursor, count, put, left, by omega, rfl, Or.inl rfl,
      ⟨by rw [shape], by rw [shape], rfl, (fun e => nomatch e), fun _ => Or.inr mode, Or.inl mode,
        fun _ ended initial => absurd (by rw [shape] at ended; exact ended) initial⟩⟩

#print axioms inflate_LENGTH_state_rank

/-- `case LENGTH`: a result outside `BAD` holds at most `max bits 31`. -/
theorem inflate_LENGTH_held {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {state : InflateState}
    (run : runX (inflate_LENGTH c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    state.mode ≠ BAD → regs.bits.toNat ≤ max l.bits.toNat 31 := by
  intro notBad
  have same {o2 : Except Ex Unit} {r2 : IL} {a2 : Heap}
      (two : runX (inflate_LENGTH c) l h = .ok ((o2, r2), a2)) : regs = r2 ∧ after = a2 := by
    have e := Except.ok.inj (run.symm.trans two)
    simp only [Prod.mk.injEq] at e
    exact ⟨e.1.2, e.2⟩
  by_cases skip : s.wrap = 0 ∨ s.flags = 0
  · obtain ⟨run2, _⟩ := inflate_LENGTH_default_boundary E invariant.good invariant.pending buffers skip
    rw [(same run2).1]
    change l.bits.toNat ≤ _
    omega
  have hw : s.wrap ≠ 0 := fun zero => skip (Or.inl zero)
  have hf : s.flags ≠ 0 := fun zero => skip (Or.inr zero)
  obtain ⟨_, current, used, pull, usedBound, bitInv, _, _, shape, _, _, _, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 32 (by decide)
  have packet : DispatchBuffers h r current (bs.drop used) :=
    buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl)
      cursor usedBound bitInv
  obtain ⟨rr, regs1, j, read, _, _, _, waitRun, fullRun⟩ :=
    inflate_LENGTH_run E.strm E.st E.hz E.hs hw hf buffers.bits
  rw [pull] at read
  cases read
  rcases kinds with normal | wait
  · obtain ⟨_, badRun, acceptedRun⟩ := fullRun normal
    by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧ current.hold ≠ (s.total &&& 0xffffffff)
    · obtain ⟨i, _, run2⟩ := badRun invalid.1 invalid.2
      obtain ⟨currentGood, _⟩ := head_bad_packet invariant.good invariant.pending packet packet.bits (by rfl) i
      have heapEq := (same run2).2
      subst heapEq
      have stateEq := Option.some.inj (get.symm.trans currentGood.live.hs)
      rw [stateEq] at notBad
      exact absurd rfl notBad
    · rw [(same (acceptedRun invalid)).1]
      change (0 : UInt32).toNat ≤ _
      simp
  · obtain ⟨_, _, small, run2⟩ := waitRun wait
    rw [(same run2).1]
    omega

#print axioms inflate_LENGTH_held

/-- Actual CHECK executes its real checksum callee and LENGTH continuation
while retaining the full default state, exact public buffers and strict
rank. Output accounting is performed once before checksum acceptance. -/
theorem inflate_CHECK_default_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_CHECK c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
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
      (inputAdvance_zero l.next).symm, by rfl, rfl, rfl, incoming, by rfl, Or.inl rfl⟩
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
          next2, count2, put2, left2, bits2, static2, progress2, _⟩ :=
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
        refine ⟨outcome2, regs2, after2, stream2, state2, used + used2, total, result, final2,
          by simpa only [List.drop_drop, Nat.add_comm] using packet2, sizes1.trans sizes2,
          by rw [next2]; show inputAdvance current.next used2 = _; rw [cursor, inputAdvance_add], by change regs2.have_.toNat + used2 = current.have_.toNat at count2; omega,
          put2.trans put, left2.trans left, bits2,
          static2.trans (by change heap0.static = h.static; exact static0), ?_⟩
        rcases progress2 with leave | ⟨normal, smaller⟩
        · exact Or.inl leave
        · exact Or.inr ⟨normal, Nat.lt_trans smaller firstRank⟩
    · obtain ⟨_, _, _, run⟩ := waitRun wait
      exact ⟨.error Ex.leave, current, h, z, s, used, usedBound, run, invariant,
        packet, ByteViewSizes.refl h, cursor, count, put, left, by omega, rfl, Or.inl rfl⟩


end Zlib.Inflate.Proofs
