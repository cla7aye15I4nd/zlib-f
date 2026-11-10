import ZlibF.Proof.«inflate.c.normal-mode-dispatch»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem BlockControlMode.not_length {mode : UInt32} (allowed : BlockControlMode mode) : mode ≠ LENGTH := by
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem StoredExitMode.not_length {mode : UInt32} (allowed : StoredExitMode mode) : mode ≠ LENGTH := by
  rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide

theorem DataExitMode.not_length {mode : UInt32} (allowed : DataExitMode mode) : mode ≠ LENGTH := by
  rcases allowed with data | rfl | rfl
  · rcases data with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  all_goals decide

/-- HEAD has only its actual header or block/error continuation on a
normal return. It cannot construct MEM or SYNC. -/
theorem inflate_HEAD_normal_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (run : runX (inflate_HEAD c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  rcases invariant.wrapper with raw | wrapped
  · have source := inflate_HEAD_raw_run E l raw
    have same := xrun_state_eq (firstState := { s with mode := TYPEDO })
      source run (by simp only [setI_istates_same]) get
    rw [← same]
    change TYPEDO ≠ LENGTH
    decide
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, good, _, _, _, _,
      _, _, _, _, _, _, kinds, _, _⟩ :=
      inflate_HEAD_zlib_window_boundary_frame E invariant.good invariant.pending buffers mode
        wrapped invariant.header invariant.window
    have normal := xrun_outcome_eq source run
    have same := xrun_state_eq source run good.live.hs get
    rw [← same]
    rcases kinds with ⟨wait, _⟩ | ⟨_, allowed⟩
    · cases wait.symm.trans normal
    · rcases allowed with selected | selected | selected <;> rw [selected] <;> decide




/-- A normal DICT return runs the actual prepared TYPE branch. The
missing-dictionary branch is a distinct direct return. -/
theorem inflate_DICT_normal_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_DICT c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
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
    have views : ∀ ref : BRef, (Space.get heap ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have ro : ∀ ref : BRef, Space.ro heap ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have packet := buffers.byte_views invariant.good current.good rfl views ro
    have selector : runX (inflate_dispatch c) l heap = runX (inflate_TYPE c) l heap := by
      rw [inflate_dispatch_block_type env l (Or.inl rfl), ite_eq_left rfl]
    have actual : runX (inflate_dispatch c) l heap = .ok ((.ok (), regs), after) :=
      selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run)
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, state, used, _, source, final,
      modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_type_state_rank env current packet (Or.inl rfl) incoming
    have same := xrun_state_eq source actual final.good.live.hs get
    rw [← same]
    exact modes.not_length

/-- The actual dictionary-id read enters DICT with a cleared local bit
buffer. A normal continuation is therefore still below terminal errors. -/
theorem inflate_DICTID_normal_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (run : runX (inflate_DICTID c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  obtain ⟨outcome, currentRegs, used, pull, usedBound, bitInv, _, _, shape,
    _, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
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
    have views : ∀ ref : BRef, (Space.get heap ref : Option (Array UInt8)) = Space.get h ref := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have ro : ∀ ref : BRef, Space.ro heap ref = Space.ro h ref := by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]
    have packet0 : DispatchBuffers heap r first (bs.drop used) :=
      (packet.byte_views invariant.good current.good rfl views ro).clear_bits
    have actual : runX (inflate_DICT c) first heap = .ok ((.ok (), regs), after) :=
      (inflate_DICTID_parsed_cut E l currentRegs pull).symm.trans run
    exact inflate_DICT_normal_not_length env current packet0 rfl (by change 0 ≤ 39; decide) actual get
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    have impossible := xrun_outcome_eq source run
    cases impossible




/-- In the default CHECK path, a normal return is the actual checksum
rejection. Waiting and successful completion use ordinary leave instead. -/
theorem inflate_CHECK_normal_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  by_cases raw : s.wrap = 0
  · let state := { s with mode := LENGTH }
    let heap := setI h zs state
    have stateGet : heap.istates zs = some state := by simp only [heap, setI_istates_same]
    have source := (inflate_CHECK_nowrap E.st E.hs raw).trans
      (inflate_LENGTH_skip (l := l) E.st stateGet (Or.inl raw))
    have impossible := xrun_outcome_eq source run
    cases impossible
  · have flags : s.flags = 0 := (invariant.trailer (Or.inl mode)).resolve_left raw
    have statics : Zlib.Crc32.Proofs.StaticsOK h := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [invariant.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨outcome, current, used, pull, _, _, _, _, _, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 32 (by decide)
    obtain ⟨rr, nextRegs, j, read, _, _, _, waitRun, fullRun⟩ :=
      inflate_CHECK_views_run (l.out_ - l.left) rfl E.strm E.st E.hz E.hs raw buffers.bits statics
        (fun _ => leaveOutputView_of_cursor invariant.good buffers.output)
    rw [pull] at read
    cases read
    rcases kinds with normal | wait
    · obtain ⟨_, value, badRun, acceptedRun⟩ := fullRun normal
      let out := l.out_ - l.left
      let state := chkS s out value
      by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧
          (if s.flags ≠ 0 then current.hold else ZSWAP32 current.hold) ≠ state.check
      · obtain ⟨i, _, source⟩ := badRun invalid.1 invalid.2
        have same := xrun_state_eq (firstState := { state with mode := BAD }) source run
          (by simp only [state, out, tcBadHeap, setI_istates_same]) get
        rw [← same]
        change BAD ≠ LENGTH
        decide
      · let next := { state with mode := LENGTH }
        let heap := setI (chkH h r zs z s out value) zs next
        have stateGet : heap.istates zs = some next := by simp only [heap, setI_istates_same]
        have source := (acceptedRun invalid).trans
          (inflate_LENGTH_skip E.st stateGet (Or.inr flags))
        have impossible := xrun_outcome_eq source run
        cases impossible
    · obtain ⟨_, _, _, source⟩ := waitRun wait
      have impossible := xrun_outcome_eq source run
      cases impossible




theorem inflate_dispatch_construction_normal_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  obtain ⟨prefixRegs, prefixHeap, prefixZ, prefixState, used, _, current, _, packet, _, _, _, _, _, _, _, _, parts⟩ :=
    inflate_dispatch_construction_state_boundary E invariant buffers mode
  rcases parts with stopped | continued
  · obtain ⟨outcome, source, why⟩ := stopped
    have normal := xrun_outcome_eq source run
    have same := xrun_state_eq source run current.good.live.hs get
    have bad := why.resolve_left (fun other => other normal)
    rw [← same, bad]
    decide
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [ite_eq_left trees] at source
      have impossible := xrun_outcome_eq source run
      cases impossible
    · rw [ite_eq_right trees] at source
      have env : Env c prefixHeap r zs prefixZ prefixState :=
        ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
      have data : DataTableMode prefixState.mode := by rw [nextMode]; unfold DataTableMode; decide
      obtain ⟨outcome, finalRegs, finalHeap, finalZ, state, used2, made, _, calleeRun, final,
        modes, _, _, _, _, _, _, _, _⟩ :=
        inflate_dispatch_data_view_state_rank env current packet data
      have complete := source.trans ((inflate_dispatch_LEN_start env prefixRegs nextMode).symm.trans calleeRun)
      have same := xrun_state_eq complete run final.good.live.hs get
      rw [← same]
      exact modes.not_length

/-- Every actual normal default dispatch result excludes LENGTH. This
uses the modes retained by real source branches; it is not a statement
about arbitrary exits or arbitrary saved protocol histories. -/
theorem inflate_dispatch_normal_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal
  · exact inflate_HEAD_normal_not_length E invariant buffers head
      ((inflate_dispatch_HEAD E l head).symm.trans run) get
  · rcases dictionary with id | dictionary
    · exact inflate_DICTID_normal_not_length E invariant buffers id
        ((inflate_dispatch_DICTID E l id).symm.trans run) get
    · exact inflate_DICT_normal_not_length E invariant buffers dictionary incoming
        ((inflate_dispatch_DICT E l dictionary).symm.trans run) get
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, final, modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.not_length
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, final, modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.not_length
  · exact inflate_dispatch_construction_normal_not_length E invariant buffers construction run get
  · obtain ⟨outcome, outRegs, heap, stream, state, used, made, _, source, final, modes, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    have same := xrun_state_eq source run final.good.live.hs get
    rw [← same]
    exact modes.not_length
  · rcases trailer with check | length
    · exact inflate_CHECK_normal_not_length E invariant buffers check
        ((inflate_dispatch_CHECK E l check).symm.trans run) get
    · obtain ⟨source, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
      have complete := (inflate_dispatch_LENGTH E l length).trans source
      have impossible := xrun_outcome_eq complete run
      cases impossible
  · have source := inflate_dispatch_terminal_run E l terminal
    have impossible := xrun_outcome_eq source run
    rcases terminal with selected | selected | selected | selected <;>
      rw [selected] at impossible <;> simp [terminalExit, DONE, BAD, MEM, SYNC] at impossible

#print axioms inflate_dispatch_normal_not_length

#print axioms BlockControlMode.not_length
#print axioms StoredExitMode.not_length
#print axioms DataExitMode.not_length
#print axioms inflate_HEAD_normal_not_length
#print axioms inflate_DICT_normal_not_length
#print axioms inflate_DICTID_normal_not_length
#print axioms inflate_CHECK_normal_not_length
#print axioms inflate_dispatch_construction_normal_not_length
#print axioms inflate_dispatch_normal_not_length
end Zlib.Inflate.Proofs
