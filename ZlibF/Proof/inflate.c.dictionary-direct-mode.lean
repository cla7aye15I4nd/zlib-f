import ZlibF.Proof.«inflate.c.no-direct-modes»
import ZlibF.Proof.«inflate.c.dictid-dispatch»
import ZlibF.Proof.«inflate.c.dictionary-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual DICT direct return is NEED_DICT and retains DICT mode.
The supplied-dictionary TYPE continuation has no direct API return. -/
theorem inflate_DICT_direct_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {rc : Int32}
    (E : Env c h r zs z s) (mode : s.mode = DICT)
    (run : runX (inflate_DICT c) l h = .ok ((.error (.ret rc), regs), after))
    (getAfter : after.istates zs = some state) : rc = Z_NEED_DICT ∧ state.mode = DICT := by
  by_cases missing : s.havedict = 0
  · have source := inflate_DICT_wait_run E l missing
    have same := Except.ok.inj (source.symm.trans run)
    have outcomeEq : (.error (.ret Z_NEED_DICT) : Except Ex Unit) = .error (.ret rc) :=
      congrArg (fun pair => pair.1.1) same
    have codeEq : Z_NEED_DICT = rc := Ex.ret.inj (Except.error.inj outcomeEq)
    have heapEq : setI (r.put h (dictWaitStream z l)) zs (leaveState s l) = after :=
      congrArg Prod.snd same
    have currentGet : after.istates zs = some (leaveState s l) := by rw [← heapEq]; simp
    have stateEq : leaveState s l = state := Option.some.inj (currentGet.symm.trans getAfter)
    refine ⟨codeEq.symm, ?_⟩
    rw [← stateEq]
    exact mode
  · have executed := (inflate_DICT_ready_cut E l missing).symm.trans run
    exact False.elim (noDirect_inflate_TYPE c l
      (setI (r.put h { z with adler := 1 }) zs { s with check := 1, mode := TYPE })
      (.error (.ret rc)) regs after executed rc rfl)

/-- DICTID executes the real word read and writes DICT before entering
the actual dictionary handler. Its only direct API outcome is NEED_DICT. -/
theorem inflate_DICTID_direct_mode
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {rc : Int32} {bs : List UInt8}
    (E : Env c h r zs z s) (bits : BitInv h l bs)
    (run : runX (inflate_DICTID c) l h = .ok ((.error (.ret rc), regs), after))
    (getAfter : after.istates zs = some state) : rc = Z_NEED_DICT ∧ state.mode = DICT := by
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
    exact inflate_DICT_direct_mode env rfl
      ((inflate_DICTID_parsed_cut E l current pull).symm.trans run) getAfter
  · rw [wait] at pull
    have source := inflate_DICTID_wait (c := c) pull
    have same := Except.ok.inj (source.symm.trans run)
    have impossible : (.error Ex.leave : Except Ex Unit) = .error (.ret rc) :=
      congrArg (fun pair => pair.1.1) same
    cases Except.error.inj impossible

end Zlib.Inflate.Proofs
