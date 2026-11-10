import ZlibF.Proof.«inflate.c.return-codes»
import ZlibF.Proof.«inflate.c.main.common»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- All actual switch branches outside dynamic-table construction retain
an admitted local return code or write END/DATA_ERROR. This is a successful-
run source fact for every wrapper configuration. Constructor error/BAD
phase closure remains separate; no callee contract or safety is assumed. -/
theorem inflate_dispatch_nonconstruction_return_allowed
    {allowed : Int32 → Prop} {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (ended : allowed Z_STREAM_END) (badCode : allowed Z_DATA_ERROR)
    (E : Env c h r zs z s)
    (nonTable : s.mode ≠ TABLE) (nonLengths : s.mode ≠ LENLENS) (nonCodes : s.mode ≠ CODELENS)
    (incoming : allowed l.ret)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) : allowed regs.ret := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  dsimp only at run
  simp only [beq_iff_eq, nonTable, nonLengths, nonCodes, ite_false] at run
  by_cases selected : s.mode = HEAD
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_HEAD base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = FLAGS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_FLAGS base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TIME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_TIME base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = OS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_OS base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXLEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_EXLEN base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXTRA
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_EXTRA base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = NAME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_NAME base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COMMENT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_COMMENT base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = HCRC
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_HCRC base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICTID
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_DICTID base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_DICT base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_TYPE base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPEDO
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_TYPEDO base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = STORED
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_STORED base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_COPY_ base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_COPY base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_LEN_ base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_LEN base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_LENEXT base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DIST
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_DIST base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DISTEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_DISTEXT base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = MATCH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_MATCH base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LIT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact (returnAllowedX_of_frame (fun base => returnRegisterX_inflate_LIT base c))
      l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = CHECK
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnAllowedX_inflate_CHECK allowed ended c l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENGTH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnAllowedX_inflate_LENGTH allowed ended c l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DONE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact returnAllowedX_inflate_DONE allowed ended c l h outcome regs after incoming run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases bad : s.mode = BAD
  · simp only [beq_iff_eq, bad, ite_true, runX_bind, runX_modify, runX_throw] at run
    cases run
    exact badCode
  simp only [beq_iff_eq, bad, ite_false] at run
  by_cases memory : s.mode = MEM
  all_goals simp only [beq_iff_eq, memory, ite_true, ite_false, runX_throw] at run
  all_goals cases run; exact incoming

end Zlib.Inflate.Proofs
