import ZlibF.Proof.«inflate.c.default-dispatch-normal-not-length»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem inflate_HEAD_result_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {result : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (run : runX (inflate_HEAD c) l h = .ok ((result, regs), after))
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
    have same := xrun_state_eq source run good.live.hs get
    rw [← same]
    rcases kinds with ⟨_, sameState⟩ | ⟨_, allowed⟩
    · rw [sameState, mode]; decide
    · rcases allowed with selected | selected | selected <;> rw [selected] <;> decide




/-- A normal DICT return runs the actual prepared TYPE branch. The
missing-dictionary branch is a distinct direct return. -/
 theorem inflate_DICT_result_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {result : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_DICT c) l h = .ok ((result, regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have same := xrun_state_eq (firstState := leaveState s l) source run
      (by simp only [setI_istates_same]) get
    rw [← same]
    change s.mode ≠ LENGTH
    rw [mode]; decide
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
    have actual : runX (inflate_dispatch c) l heap = .ok ((result, regs), after) :=
      selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run)
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, state, used, _, source, final,
      modes, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      inflate_dispatch_type_state_rank env current packet (Or.inl rfl) incoming
    have same := xrun_state_eq source actual final.good.live.hs get
    rw [← same]
    exact modes.not_length

/-- The actual dictionary-id read enters DICT with a cleared local bit
buffer. A normal continuation is therefore still below terminal errors. -/
 theorem inflate_DICTID_result_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {result : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID)
    (run : runX (inflate_DICTID c) l h = .ok ((result, regs), after))
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
    have actual : runX (inflate_DICT c) first heap = .ok ((result, regs), after) :=
      (inflate_DICTID_parsed_cut E l currentRegs pull).symm.trans run
    exact inflate_DICT_result_not_length env current packet0 rfl (by change 0 ≤ 39; decide) actual get
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    have same := xrun_state_eq source run invariant.good.live.hs get
    rw [← same, mode]; decide




/-- In the default CHECK path, a normal return is the actual checksum
rejection. Waiting and successful completion use ordinary leave instead. -/
 theorem inflate_CHECK_result_not_length
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {result : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((result, regs), after))
    (get : after.istates zs = some returned) : returned.mode ≠ LENGTH := by
  by_cases raw : s.wrap = 0
  · let state := { s with mode := LENGTH }
    let heap := setI h zs state
    have stateGet : heap.istates zs = some state := by simp only [heap, setI_istates_same]
    have source := (inflate_CHECK_nowrap E.st E.hs raw).trans
      (inflate_LENGTH_skip (l := l) E.st stateGet (Or.inl raw))
    have same := xrun_state_eq (firstState := {state with mode := DONE}) source run
      (by simp only [setI_istates_same]) get
    rw [← same]
    change DONE ≠ LENGTH
    decide
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
        have same := xrun_state_eq (firstState := {next with mode := DONE}) source run
          (by simp only [setI_istates_same]) get
        rw [← same]
        change DONE ≠ LENGTH
        decide
    · obtain ⟨_, _, _, source⟩ := waitRun wait
      have same := xrun_state_eq source run invariant.good.live.hs get
      rw [← same, mode]; decide




#print axioms inflate_HEAD_result_not_length
#print axioms inflate_DICT_result_not_length
#print axioms inflate_DICTID_result_not_length
#print axioms inflate_CHECK_result_not_length
end Zlib.Inflate.Proofs
