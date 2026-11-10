import ZlibF.Proof.«inflate.c.output-ledger-check»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact source alternatives at the end of default CHECK: input wait,
checksum refusal, or completed trailer. The local output base is retained
or rebound to the actual remaining capacity. -/
def CheckReturnShape (before : InflateState) (initial : IL) (outcome : Except Ex Unit)
    (regs : IL) (state : InflateState) : Prop :=
  (outcome = .error Ex.leave ∧ regs.ret = initial.ret ∧ state = before ∧ regs.out_ = initial.out_) ∨
  (outcome = .ok () ∧ regs.ret = initial.ret ∧ state.mode = BAD ∧ regs.out_ = initial.left) ∨
  (outcome = .error Ex.leave ∧ regs.ret = Z_STREAM_END ∧ state.mode = DONE ∧
    (regs.out_ = initial.out_ ∨ regs.out_ = initial.left))

/-- Every successful execution of the real default CHECK branch retains
the exact control/output-base relation. This includes exhausted input, a rejected checksum,
raw recovery, and successful fallthrough through LENGTH and DONE. The
checksum callee and bit-reading loop are executed by their proved rules. -/
theorem inflate_CHECK_default_return_shape
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((outcome, regs), after))
    (getAfter : after.istates zs = some state) : CheckReturnShape s l outcome regs state := by
  by_cases raw : s.wrap = 0
  · have lengthRun := inflate_LENGTH_skip (l := l) E.st
      (show (setI h zs { s with mode := LENGTH }).istates zs = some { s with mode := LENGTH } by simp)
      (Or.inl raw)
    have whole := (inflate_CHECK_nowrap E.st E.hs raw).trans lengthRun
    rw [run] at whole
    cases whole
    have stateEq : { { s with mode := LENGTH } with mode := DONE } = state := by
      simpa only [setI, upd_same, Option.some.injEq] using getAfter
    exact Or.inr (Or.inr ⟨rfl, rfl, (congrArg InflateState.mode stateEq).symm, Or.inl rfl⟩)
  · have flags : s.flags = 0 := (invariant.trailer (Or.inl mode)).resolve_left raw
    have statics : Zlib.Crc32.Proofs.StaticsOK h := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [invariant.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rr, current, used, pull, bound, bits, _, _, shape, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 32 (by decide)
    have base : current.out_ = l.out_ := by rw [shape]
    have ret : current.ret = l.ret := by rw [shape]
    obtain ⟨result, regs1, count, read, _, _, _, waitRun, fullRun⟩ :=
      inflate_CHECK_views_run (l.out_ - l.left) rfl E.strm E.st E.hz E.hs raw buffers.bits statics
        (fun _ => leaveOutputView_of_cursor invariant.good buffers.output)
    rw [pull] at read
    cases read
    rcases kinds with normal | wait
    · obtain ⟨_, value, rejected, accepted⟩ := fullRun normal
      let charged := chkZ z s (l.out_ - l.left) value
      let chargedState := chkS s (l.out_ - l.left) value
      let chargedHeap := chkH h r zs z s (l.out_ - l.left) value
      have chargedGet : r.get chargedHeap = some charged := by
        simp only [chargedHeap, charged, chkH, ZStreamRef.get_setI, ZStreamRef.get_put_same E.hz]
      by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧
          (if s.flags ≠ 0 then current.hold else ZSWAP32 current.hold) ≠ chargedState.check
      · obtain ⟨index, _, badRun⟩ := rejected invalid.1 invalid.2
        rw [run] at badRun
        cases badRun
        have stateEq : { chargedState with mode := BAD } = state := by
          simpa only [tcBadHeap, setI, upd_same, Option.some.injEq] using getAfter
        exact Or.inr (Or.inl ⟨rfl, ret, (congrArg InflateState.mode stateEq).symm, rfl⟩)
      · have stateGet : (setI chargedHeap zs { chargedState with mode := LENGTH }).istates zs =
            some { chargedState with mode := LENGTH } := by simp
        have lengthRun := inflate_LENGTH_skip
          (l := { current with out_ := l.left, hold := 0, bits := 0 }) E.st stateGet
          (Or.inr (show ({ chargedState with mode := LENGTH } : InflateState).flags = 0 from flags))
        have whole := (accepted invalid).trans lengthRun
        rw [run] at whole
        cases whole
        have stateEq : { { chargedState with mode := LENGTH } with mode := DONE } = state := by
          simpa only [setI, upd_same, Option.some.injEq] using getAfter
        exact Or.inr (Or.inr ⟨rfl, rfl, (congrArg InflateState.mode stateEq).symm, Or.inr rfl⟩)
    · obtain ⟨_, _, _, stopped⟩ := waitRun wait
      rw [run] at stopped
      cases stopped
      have stateEq : s = state := Option.some.inj (E.hs.symm.trans getAfter)
      exact Or.inl ⟨rfl, ret, stateEq.symm, base⟩

end Zlib.Inflate.Proofs
