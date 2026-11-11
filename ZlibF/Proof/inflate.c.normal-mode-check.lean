import ZlibF.Proof.«inflate.c.normal-mode-base»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- In the default CHECK path, a normal return is the actual checksum
rejection. Waiting and successful completion use ordinary leave instead. -/
theorem inflate_CHECK_normal_low
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((.ok (), regs), after))
    (get : after.istates zs = some returned) : returned.mode < MEM := by
  by_cases raw : s.wrap = 0
  · let state := { s with mode := LENGTH }
    let heap := setI h zs state
    have stateGet : heap.istates zs = some state := by simp only [heap, setI_istates_same]
    have source := (inflate_CHECK_nowrap E.st E.hs raw).trans
      (inflate_LENGTH_skip (l := l) E.st stateGet (Or.inl raw))
    have impossible := xrun_outcome_eq source run
    cases impossible
  · by_cases flags : s.flags = 0
    swap
    · sorry
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
        change BAD < MEM
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

end Zlib.Inflate.Proofs
