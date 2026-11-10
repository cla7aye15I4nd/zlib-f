import ZlibF.Proof.«inflate.c.dictionary-direct-mode»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Public fields actually published by RESTORE. Fixed stream fields and
original-call counts are proved separately by their source frames. -/
def RestoredCursors (stream : ZStream) (regs : IL) : Prop :=
  stream.next_in = regs.next ∧ stream.avail_in = regs.have_ ∧
    stream.next_out = regs.put ∧ stream.avail_out = regs.left

/-- The actual DICT direct return is NEED_DICT and publishes precisely
the final local cursors, including input consumed before this dispatch. -/
theorem inflate_DICT_direct_cursors
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {l regs : IL} {rc : Int32}
    (E : Env c h r zs z s)
    (run : runX (inflate_DICT c) l h = .ok ((.error (.ret rc), regs), after))
    (observed : r.get after = some stream) : rc = Z_NEED_DICT ∧ RestoredCursors stream regs := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have same := Except.ok.inj (source.symm.trans run)
    have result : (.error (.ret Z_NEED_DICT) : Except Ex Unit) = .error (.ret rc) :=
      congrArg (fun pair => pair.1.1) same
    have regsEq : l = regs := congrArg (fun pair => pair.1.2) same
    have heapEq : setI (r.put h (dictWaitStream z l)) zs (leaveState s l) = after :=
      congrArg Prod.snd same
    have currentGet : r.get after = some (dictWaitStream z l) := by
      rw [← heapEq, ZStreamRef.get_setI, ZStreamRef.get_put_same E.hz]
    have streamEq : dictWaitStream z l = stream := Option.some.inj (currentGet.symm.trans observed)
    refine ⟨(Ex.ret.inj (Except.error.inj result)).symm, ?_⟩
    rw [← streamEq, ← regsEq]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have executed := (inflate_DICT_ready_cut E l missing).symm.trans run
    exact False.elim (noDirect_inflate_TYPE c l
      (setI (r.put h { z with adler := 1 }) zs { s with check := 1, mode := TYPE })
      (.error (.ret rc)) regs after executed rc rfl)

/-- DICTID executes the real word read and its actual dictionary direct
return. Both published cursors are the final local cursor values. -/
theorem inflate_DICTID_direct_cursors
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {l regs : IL} {rc : Int32} {bs : List UInt8}
    (E : Env c h r zs z s) (bits : BitInv h l bs)
    (run : runX (inflate_DICTID c) l h = .ok ((.error (.ret rc), regs), after))
    (observed : r.get after = some stream) : rc = Z_NEED_DICT ∧ RestoredCursors stream regs := by
  obtain ⟨outcome, current, used, pull, _, _, _, _, _, _, _, _, _, kinds, _⟩ :=
    NEEDBITS_run_cursor bits 32 (by decide)
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 current.hold
    let ready := { s with check := value, mode := DICT }
    let stream0 := { z with adler := value }
    let heap0 := setI (r.put h stream0) zs ready
    have env : Env c heap0 r zs stream0 ready :=
      ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same E.hz _, by simp [heap0]⟩
    exact inflate_DICT_direct_cursors env
      ((inflate_DICTID_parsed_cut E l current pull).symm.trans run) observed
  · rw [wait] at pull
    have source := inflate_DICTID_wait (c := c) pull
    have same := Except.ok.inj (source.symm.trans run)
    have impossible : (.error Ex.leave : Except Ex Unit) = .error (.ret rc) :=
      congrArg (fun pair => pair.1.1) same
    cases Except.error.inj impossible

end Zlib.Inflate.Proofs
