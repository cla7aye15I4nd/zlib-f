import ZlibF.Proof.«inflate.c.trailer-default-state»
import ZlibF.Proof.«inflate.c.stream-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The output already charged to the stream and the local segment base
form one modular lifetime ledger. CHECK changes both parts together. -/
def OutputLedger (before after : ZStream) (initial regs : IL) : Prop :=
  after.total_out + regs.out_.toUInt64 = before.total_out + initial.out_.toUInt64

theorem OutputLedger.refl (z : ZStream) (l : IL) : OutputLedger z z l l := rfl

theorem OutputLedger.trans {a b c : ZStream} {l m n : IL}
    (first : OutputLedger a b l m) (second : OutputLedger b c m n) : OutputLedger a c l n :=
  Eq.trans second first

/-- Every successful execution of the real default CHECK branch retains
the output ledger. This includes exhausted input, a rejected checksum,
raw recovery, and successful fallthrough through LENGTH and DONE. The
checksum callee and bit-reading loop are executed by their proved rules. -/
theorem inflate_CHECK_default_output_ledger
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((outcome, regs), after))
    (getAfter : r.get after = some stream) : OutputLedger z stream l regs := by
  by_cases raw : s.wrap = 0
  · have lengthRun := inflate_LENGTH_skip (l := l) E.st
      (show (setI h zs { s with mode := LENGTH }).istates zs = some { s with mode := LENGTH } by simp)
      (Or.inl raw)
    have whole := (inflate_CHECK_nowrap E.st E.hs raw).trans lengthRun
    rw [run] at whole
    cases whole
    have current : stream = z := by
      simpa only [ZStreamRef.get_setI, E.hz, Option.some.injEq] using getAfter.symm
    subst stream
    rfl
  · have flags : s.flags = 0 := (invariant.trailer (Or.inl mode)).resolve_left raw
    have statics : Zlib.Crc32.Proofs.StaticsOK h := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [invariant.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rr, current, used, pull, bound, bits, _, _, shape, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 32 (by decide)
    have base : current.out_ = l.out_ := by rw [shape]
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
      have ledger : charged.total_out + l.left.toUInt64 = z.total_out + l.out_.toUInt64 :=
        chkZ_output_ledger z s l value buffers.output.count
      by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧
          (if s.flags ≠ 0 then current.hold else ZSWAP32 current.hold) ≠ chargedState.check
      · obtain ⟨index, _, badRun⟩ := rejected invalid.1 invalid.2
        rw [run] at badRun
        cases badRun
        have currentGet : r.get (tcBadHeap chargedHeap r zs charged chargedState index) =
            some { charged with msg := .ref (.str index) 0 } := by
          simp only [tcBadHeap, ZStreamRef.get_setI, ZStreamRef.get_put_same chargedGet]
        rw [currentGet] at getAfter
        have same : { charged with msg := .ref (.str index) 0 } = stream := Option.some.inj getAfter
        change stream.total_out + l.left.toUInt64 = _
        rw [← same]
        exact ledger
      · have stateGet : (setI chargedHeap zs { chargedState with mode := LENGTH }).istates zs =
            some { chargedState with mode := LENGTH } := by simp
        have lengthRun := inflate_LENGTH_skip
          (l := { current with out_ := l.left, hold := 0, bits := 0 }) E.st stateGet
          (Or.inr (show ({ chargedState with mode := LENGTH } : InflateState).flags = 0 from flags))
        have whole := (accepted invalid).trans lengthRun
        rw [run] at whole
        cases whole
        have currentGet : r.get
            (setI (setI chargedHeap zs { chargedState with mode := LENGTH }) zs
              { { chargedState with mode := LENGTH } with mode := DONE }) = some charged := by
          simpa only [ZStreamRef.get_setI] using chargedGet
        rw [currentGet] at getAfter
        have same : charged = stream := Option.some.inj getAfter
        change stream.total_out + l.left.toUInt64 = _
        rw [← same]
        exact ledger
    · obtain ⟨_, _, _, stopped⟩ := waitRun wait
      rw [run] at stopped
      cases stopped
      have currentGet : stream = z := Option.some.inj (getAfter.symm.trans E.hz)
      subst stream
      exact congrArg (fun count => z.total_out + count.toUInt64) base

end Zlib.Inflate.Proofs
