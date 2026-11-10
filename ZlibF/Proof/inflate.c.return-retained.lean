import ZlibF.Proof.«inflate.c.return-codes»
import ZlibF.Proof.«inflate.c.main.common»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Regular switch branches retain ret. Constructor, trailer and
terminal writes use their separate proved source relations. -/
theorem inflate_dispatch_regular_retained
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s)
    (nonTable : s.mode ≠ TABLE) (nonLengths : s.mode ≠ LENLENS) (nonCodes : s.mode ≠ CODELENS)
    (nonCheck : s.mode ≠ CHECK) (nonLength : s.mode ≠ LENGTH)
    (nonDone : s.mode ≠ DONE) (nonBad : s.mode ≠ BAD)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) : regs.ret = l.ret := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  dsimp only at run
  simp only [beq_iff_eq, nonTable, nonLengths, nonCodes, nonCheck, nonLength, nonDone, nonBad, ite_false] at run
  by_cases selected : s.mode = HEAD
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_HEAD l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = FLAGS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_FLAGS l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TIME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_TIME l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = OS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_OS l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXLEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_EXLEN l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXTRA
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_EXTRA l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = NAME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_NAME l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COMMENT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_COMMENT l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = HCRC
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_HCRC l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICTID
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_DICTID l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_DICT l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_TYPE l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPEDO
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_TYPEDO l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = STORED
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_STORED l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_COPY_ l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_COPY l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_LEN_ l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_LEN l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_LENEXT l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DIST
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_DIST l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DISTEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_DISTEXT l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = MATCH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_MATCH l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LIT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnRegisterX_inflate_LIT l.ret c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases memory : s.mode = MEM
  all_goals simp only [beq_iff_eq, memory, ite_true, ite_false, runX_throw] at run
  all_goals cases run; rfl

end Zlib.Inflate.Proofs
