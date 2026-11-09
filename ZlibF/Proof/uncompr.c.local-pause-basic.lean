import ZlibF.Proof.«uncompr.c.inflate-pause-basic»
import ZlibF.Proof.«inflate.c.local-normal-mode-base»
import ZlibF.Proof.«inflate.c.local-trailer-state»

namespace Zlib.Uncompr.Proof.LocalPause
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inflate.Local Zlib.Uncompr.Proof.InflatePause
set_option autoImplicit false
set_option maxRecDepth 8192

/-- A default HEAD leave is the unchanged incomplete-header state. -/
theorem head_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (run : runX (inflate_HEAD c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  rcases invariant.wrapper with raw | wrapped
  · have source := inflate_HEAD_raw_run E l raw
    have impossible := xrun_outcome_eq source run
    cases impossible
  · obtain ⟨outcome, outRegs, heap, stream, state, used, _, source, good, _, _, _,
      _, _, _, _, _, _, _, kinds, _, _, _⟩ :=
      Zlib.Inflate.Local.inflate_HEAD_zlib_window_boundary_budget E invariant.good invariant.pending buffers mode
        wrapped invariant.header invariant.window
    have selected := xrun_outcome_eq source run
    have same := xrun_state_eq source run good.live.hs get
    rcases kinds with ⟨_, eq⟩ | ⟨normal, _⟩
    · rw [←same, eq]
      simp only [PauseGood, mode]
      decide
    · cases normal.symm.trans selected

/-- A real ordinary DICT leave has passed the installed-dictionary branch
and resumed TYPE; an absent dictionary returns NEED_DICT directly. -/
theorem dict_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_DICT c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have impossible := xrun_outcome_eq source run
    cases impossible
  · let ready := { s with check := 1, mode := TYPE }
    let stream := { z with adler := 1 }
    let heap := setI (r.put h stream) zs ready
    have current : Zlib.Inflate.Local.LocalStateJ heap cutoff r zs stream ready :=
      invariant.prepare_dictionary (Or.inr mode) 1 TYPE (Or.inr rfl)
    have env : Env c heap r zs stream ready :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have packet := dispatch_byte_views_local buffers invariant.good current.good rfl
      (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
      (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
    have selector : runX (inflate_dispatch c) l heap = runX (inflate_TYPE c) l heap := by
      rw [inflate_dispatch_block_type env l (Or.inl rfl), ite_eq_left rfl]
    have actual := selector.trans ((inflate_DICT_ready_cut E l missing).symm.trans run)
    exact type_leave_pause env packet (Or.inl rfl) flush actual get

/-- An incomplete dictionary-id leave retains DICTID. A complete id runs
the real DICT branch, which cannot pause awaiting an uninstalled dictionary. -/
theorem dictid_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICTID) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_DICTID c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  obtain ⟨outcome, currentRegs, used, pull, usedBound, bitInv, _, _, shape,
    _, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 currentRegs.hold
    let ready := { s with check := value, mode := DICT }
    let stream := { z with adler := value }
    let heap := setI (r.put h stream) zs ready
    let first := { currentRegs with hold := 0, bits := 0 }
    have current : Zlib.Inflate.Local.LocalStateJ heap cutoff r zs stream ready :=
      invariant.prepare_dictionary (Or.inl mode) value DICT (Or.inl rfl)
    have env : Env c heap r zs stream ready :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have packet : DispatchBuffers h r currentRegs (bs.drop used) :=
      dispatch_consume_local buffers invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor usedBound bitInv
    have packet0 : DispatchBuffers heap r first (bs.drop used) :=
      (dispatch_byte_views_local packet invariant.good current.good rfl
        (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
        (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])).clear_bits
    have actual := (inflate_DICTID_parsed_cut E l currentRegs pull).symm.trans run
    exact dict_leave_pause env current packet0 rfl flush actual get
  · have source := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    have same := xrun_state_eq source run E.hs get
    rw [←same]
    simp only [PauseGood, mode]
    decide

/-- A CHECK ordinary leave with ret=OK is a real checksum-input wait.
Successful completion has ret=END, while rejection is a normal BAD step. -/
theorem check_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) (get : after.istates zs = some returned) : PauseGood returned := by
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
    obtain ⟨decision, current, used, pull, _, _, _, _, shape, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 32 (by decide)
    obtain ⟨rr, nextRegs, j, read, _, _, _, waitRun, fullRun⟩ :=
      inflate_CHECK_views_run (l.out_ - l.left) rfl E.strm E.st E.hz E.hs raw buffers.bits statics
        (fun _ => Zlib.Inflate.Local.leaveOutputView_of_cursor invariant.good buffers.output)
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
      have same := xrun_state_eq source run E.hs get
      rw [←same]
      simp only [PauseGood, mode]
      decide

#print axioms dict_leave_pause
#print axioms dictid_leave_pause
#print axioms check_leave_pause
#print axioms type_leave_pause
#print axioms head_leave_pause
end Zlib.Uncompr.Proof.LocalPause
