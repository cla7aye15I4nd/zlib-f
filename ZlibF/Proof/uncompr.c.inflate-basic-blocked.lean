import ZlibF.Proof.«uncompr.c.inflate-pause-basic»

namespace Zlib.Uncompr.Proof.InflateBasicBlocked
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Uncompr.Proof.InflatePause
set_option autoImplicit false

/-- Actual header/dictionary/checksum waits exhaust the offered input. The
same actual executions also supply the independent pause-mode observers. -/
theorem head_prefix_exhausted {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (B : BitInv h l bs) (wrap : s.wrap = 1 ∨ s.wrap = 5) (header : s.head = none) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (used : Nat), used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      regs.next = inputAdvance l.next used ∧
      regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits } ∧
      regs.bits.toNat ≤ max l.bits.toNat 23 ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (outcome = .ok () → 16 ≤ regs.bits.toNat) ∧
      runX (inflate_HEAD c) l h =
        (match outcome with
        | .ok () => runX (headDefaultCheck c s regs) regs h
        | .error e => .ok ((.error e, regs), h)) ∧ (outcome = .error Ex.leave → regs.have_ = 0) := by
  obtain ⟨outcome, regs, used, pull, bound, bits, _, bitCount, shape, bitBound, _, full, waiting, kinds, cursor⟩ :=
    NEEDBITS_run_cursor B 16 (by decide)
  refine ⟨outcome, regs, used, bound, bits, cursor, shape, bitBound, kinds, full, ?_, fun leave => (waiting leave).2.1⟩
  have nowrap : (s.wrap == 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  have nogzip : ((s.wrap &&& 2) != 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [nowrap, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, pull]
  rcases kinds with rfl | rfl
  · simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_ldS E]
    simp only [nogzip, bne_self_eq_false, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, header, beq_self_eq_true, Bool.not_true]
    unfold headDefaultCheck
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rfl

theorem head_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (run : runX (inflate_HEAD c) l h = .ok ((.error Ex.leave, regs), after)) : regs.have_ = 0 := by
  rcases invariant.wrapper with raw | wrapped
  · have source := inflate_HEAD_raw_run E l raw
    have impossible := xrun_outcome_eq source run
    cases impossible
  · obtain ⟨outcome, current, used, usedBound, bitInv, cursor, shape, bits, kinds, full, cut, waiting⟩ :=
      head_prefix_exhausted E buffers.bits wrapped invariant.header
    rcases kinds with normal | wait
    · rw [normal] at cut
      have packet : DispatchBuffers h r current (bs.drop used) :=
        buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
          (by rw [shape]; rfl) cursor usedBound bitInv
      obtain ⟨newRegs, heap, stream, state, source, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
        headDefaultCheck_boundary_frame E invariant.good invariant.pending packet (full normal) invariant.window
      have impossible := xrun_outcome_eq (cut.trans source) run
      cases impossible
    · rw [wait] at cut
      have sameRegs : current = regs := congrArg (fun pair => pair.1.2) (Except.ok.inj (cut.symm.trans run))
      rw [←sameRegs]
      exact waiting wait

theorem typedo_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (buffers : DispatchBuffers h r l bs)
    (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_TYPEDO c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : regs.have_ = 0 := by
  by_cases last : s.last = 0
  · obtain ⟨outcome, current, used, pull, _, _, _, _, _, _, _, _, waiting, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 3 (by decide)
    rcases kinds with normal | wait
    · rw [normal] at pull
      have actual := (inflate_TYPEDO_head E l current last pull).symm.trans run
      exact False.elim (typedoTail_no_leave flush _ _ _ _ _ actual rfl)
    · have source := inflate_TYPEDO_wait E l current last Ex.leave (by rwa [wait] at pull)
      have exhausted := (waiting wait).2.1
      rw [←xrun_regs_eq source run]
      exact exhausted
  · have source := inflate_TYPEDO_last E l last
    have impossible := xrun_outcome_eq source run
    cases impossible

/-- The caller's real block dispatcher retains a resumable mode at leave. -/
theorem type_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : regs.have_ = 0 := by
  rw [inflate_dispatch_block_type E l mode] at run
  have actual : runX (inflate_TYPEDO c) l h = .ok ((.error Ex.leave, regs), after) := by
    split at run
    · have go := inflate_TYPE_go c l h (by rw [flush]; decide)
      exact go.symm.trans run
    · exact run
  exact typedo_leave_blocked E buffers flush actual get

theorem dict_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_DICT c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : regs.have_ = 0 := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have impossible := xrun_outcome_eq source run
    cases impossible
  · let ready := { s with check := 1, mode := TYPE }
    let stream := { z with adler := 1 }
    let heap := setI (r.put h stream) zs ready
    have current : DefaultStateJ heap r zs stream ready :=
      invariant.prepare_dictionary (Or.inr mode) 1 TYPE (Or.inr rfl)
    have env : Env c heap r zs stream ready :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have packet := buffers.byte_views invariant.good current.good rfl
      (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
      (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
    have selector : runX (inflate_dispatch c) l heap = runX (inflate_TYPE c) l heap := by
      rw [inflate_dispatch_block_type env l (Or.inl rfl), ite_eq_left rfl]
    have actual := selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run)
    exact type_leave_blocked env packet (Or.inl rfl) flush actual get

/-- An incomplete dictionary-id leave retains DICTID. A complete id runs
the real DICT branch, which cannot pause awaiting an uninstalled dictionary. -/
theorem dictid_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_DICTID c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : regs.have_ = 0 := by
  obtain ⟨outcome, currentRegs, used, pull, usedBound, bitInv, _, _, shape,
    _, _, _, waiting, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 currentRegs.hold
    let ready := { s with check := value, mode := DICT }
    let stream := { z with adler := value }
    let heap := setI (r.put h stream) zs ready
    let first := { currentRegs with hold := 0, bits := 0 }
    have current : DefaultStateJ heap r zs stream ready :=
      invariant.prepare_dictionary (Or.inl mode) value DICT (Or.inl rfl)
    have env : Env c heap r zs stream ready :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have packet : DispatchBuffers h r currentRegs (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor usedBound bitInv
    have packet0 : DispatchBuffers heap r first (bs.drop used) :=
      (packet.byte_views invariant.good current.good rfl
        (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
        (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])).clear_bits
    have actual := (inflate_DICTID_parsed_cut E l currentRegs pull).symm.trans run
    exact dict_leave_blocked env current packet0 rfl flush actual get
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    rw [←xrun_regs_eq source run]
    exact (waiting wait).2.1

/-- A CHECK ordinary leave with ret=OK is a real checksum-input wait.
Successful completion has ret=END, while rejection is a normal BAD step. -/
theorem check_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) (get : after.istates zs = some returned) : regs.have_ = 0 := by
  by_cases raw : s.wrap = 0
  · let state := { s with mode := LENGTH }
    let heap := setI h zs state
    have stateGet : heap.istates zs = some state := by simp only [heap, setI_istates_same]
    have source := (inflate_CHECK_nowrap E.st E.hs raw).trans
      (inflate_LENGTH_skip (l := l) E.st stateGet (Or.inl raw))
    have ended : regs.ret = Z_STREAM_END := by rw [←xrun_regs_eq source run]
    exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) (ret.symm.trans ended))
  · have flags : s.flags = 0 := (invariant.trailer (Or.inl mode)).resolve_left raw
    have statics : Zlib.Crc32.Proofs.StaticsOK h := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [invariant.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨decision, current, used, pull, _, _, _, _, shape, _, _, _, waiting, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 32 (by decide)
    obtain ⟨rr, nextRegs, j, read, _, _, _, waitRun, fullRun⟩ :=
      inflate_CHECK_views_run (l.out_ - l.left) rfl E.strm E.st E.hz E.hs raw buffers.bits statics
        (fun _ => leaveOutputView_of_cursor invariant.good buffers.output)
    rw [pull] at read
    cases read
    rcases kinds with normal | wait
    · obtain ⟨_, value, badRun, acceptedRun⟩ := fullRun normal
      let state := chkS s (l.out_ - l.left) value
      by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧
          (if s.flags ≠ 0 then current.hold else ZSWAP32 current.hold) ≠ state.check
      · obtain ⟨i, _, source⟩ := badRun invalid.1 invalid.2
        have impossible := xrun_outcome_eq source run
        cases impossible
      · let next := { state with mode := LENGTH }
        let heap := setI (chkH h r zs z s (l.out_ - l.left) value) zs next
        have stateGet : heap.istates zs = some next := by simp only [heap, setI_istates_same]
        have source := (acceptedRun invalid).trans
          (inflate_LENGTH_skip E.st stateGet (Or.inr flags))
        have ended : regs.ret = Z_STREAM_END := by rw [←xrun_regs_eq source run]
        exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) (ret.symm.trans ended))
    · obtain ⟨_, _, _, source⟩ := waitRun wait
      rw [←xrun_regs_eq source run]
      exact (waiting wait).2.1


/-- The basic real dispatch cases leave only after exhausting input.
CHECK's successful END branch is excluded by the actual ret=OK premise. -/
theorem basic_dispatch_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (flush : c.flush = Z_NO_FLUSH)
    (mode : s.mode = HEAD ∨ s.mode = DICTID ∨ s.mode = DICT ∨
      s.mode = TYPE ∨ s.mode = TYPEDO ∨ s.mode = CHECK)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) (get : after.istates zs = some returned) : regs.have_ = 0 := by
  rcases mode with mode | mode | mode | mode | mode | mode
  · exact head_leave_blocked E invariant buffers mode ((inflate_dispatch_HEAD E l mode).symm.trans run)
  · exact dictid_leave_blocked E invariant buffers mode flush ((inflate_dispatch_DICTID E l mode).symm.trans run) get
  · exact dict_leave_blocked E invariant buffers mode flush ((inflate_dispatch_DICT E l mode).symm.trans run) get
  · exact type_leave_blocked E buffers (Or.inl mode) flush run get
  · exact type_leave_blocked E buffers (Or.inr mode) flush run get
  · exact check_leave_blocked E invariant buffers mode ((inflate_dispatch_CHECK E l mode).symm.trans run) ret get

#print axioms basic_dispatch_leave_blocked
#print axioms head_leave_blocked
#print axioms type_leave_blocked
#print axioms dict_leave_blocked
#print axioms dictid_leave_blocked
#print axioms check_leave_blocked
end Zlib.Uncompr.Proof.InflateBasicBlocked
