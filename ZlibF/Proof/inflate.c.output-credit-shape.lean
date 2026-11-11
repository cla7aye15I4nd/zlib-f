import ZlibF.Proof.«inflate.c.normal-mode-check»
import ZlibF.Proof.«inflate.c.ret-construction»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem xrun_stream_eq {α : Type} {program : X α} {l firstRegs secondRegs : IL}
    {h firstHeap secondHeap : Heap} {first second : Except Ex α}
    {r : ZStreamRef} {firstZ secondZ : ZStream}
    (a : runX program l h = .ok ((first, firstRegs), firstHeap))
    (b : runX program l h = .ok ((second, secondRegs), secondHeap))
    (firstGet : r.get firstHeap = some firstZ) (secondGet : r.get secondHeap = some secondZ) :
    firstZ = secondZ := by
  have heapEq : firstHeap = secondHeap := congrArg Prod.snd (Except.ok.inj (a.symm.trans b))
  rw [heapEq] at firstGet
  exact Option.some.inj (firstGet.symm.trans secondGet)

def OutputCreditShape (original : UInt64) (z : ZStream) (s : InflateState) (l : IL) : Prop :=
  z.total_out = original ∨ ((s.mode = BAD ∨ s.mode = DONE) ∧ l.out_ = l.left)

/-- Actual CHECK either keeps the public total or has credited it while
rebasing to left and entering BAD/DONE. Waiting has not performed credit. -/
theorem inflate_CHECK_output_credit_shape
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((outcome, regs), after))
    (streamGet : r.get after = some stream) (get : after.istates zs = some returned) :
    OutputCreditShape z.total_out stream returned regs := by
  by_cases raw : s.wrap = 0
  · let state := { s with mode := LENGTH }
    let heap := setI h zs state
    have stateGet : heap.istates zs = some state := by simp only [heap, setI_istates_same]
    have source := (inflate_CHECK_nowrap E.st E.hs raw).trans
      (inflate_LENGTH_skip (l := l) E.st stateGet (Or.inl raw))
    have same := xrun_stream_eq source run (by simpa only [ZStreamRef.get_setI] using E.hz) streamGet
    left
    rw [← same]
  · by_cases flags : s.flags = 0
    swap
    · sorry
    have statics : Zlib.Crc32.Proofs.StaticsOK h := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [invariant.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨decision, current, used, pull, _, _, _, _, shape, _, _, _, _, kinds, _⟩ :=
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
        have sameState := xrun_state_eq (firstState := { state with mode := BAD }) source run
          (by simp only [state, out, tcBadHeap, setI_istates_same]) get
        have sameRegs := xrun_regs_eq source run
        right
        constructor
        · left
          rw [← sameState]
        · rw [← sameRegs]
          change l.left = current.left
          rw [shape]
      · let next := { state with mode := LENGTH }
        let heap := setI (chkH h r zs z s out value) zs next
        have stateGet : heap.istates zs = some next := by simp only [heap, setI_istates_same]
        have source := (acceptedRun invalid).trans
          (inflate_LENGTH_skip E.st stateGet (Or.inr flags))
        have sameState := xrun_state_eq (firstState := { next with mode := DONE }) source run
          (by simp only [setI_istates_same]) get
        have sameRegs := xrun_regs_eq source run
        right
        constructor
        · right
          rw [← sameState]
        · rw [← sameRegs]
          change l.left = current.left
          rw [shape]
    · obtain ⟨_, _, _, source⟩ := waitRun wait
      have same := xrun_stream_eq source run E.hz streamGet
      left
      rw [← same]

#print axioms inflate_CHECK_output_credit_shape
end Zlib.Inflate.Proofs
