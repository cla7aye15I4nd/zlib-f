import ZlibF.Proof.«inflate.c.output-total-modes»
import ZlibF.Proof.«inflate.c.output-base-modes»
import ZlibF.Proof.«inflate.c.output-ledger-check»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Outside CHECK, the actual switch preserves the lifetime output total.
This is a successful-run frame, with no safety or callee contract assumed. -/
theorem inflate_dispatch_noncheck_output_total
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (noncheck : s.mode ≠ CHECK)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    OutputTotalFrame r h after := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  dsimp only at run
  by_cases selected : s.mode = HEAD
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_HEAD r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = FLAGS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_FLAGS r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TIME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_TIME r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = OS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_OS r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXLEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_EXLEN r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXTRA
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_EXTRA r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = NAME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_NAME r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COMMENT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_COMMENT r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = HCRC
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_HCRC r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICTID
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_DICTID r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_DICT r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_TYPE r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPEDO
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_TYPEDO r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = STORED
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_STORED r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_COPY_ r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_COPY r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TABLE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_TABLE r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENLENS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_LENLENS r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = CODELENS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_CODELENS r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_LEN_ r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_LEN r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_LENEXT r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DIST
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_DIST r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DISTEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_DISTEXT r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = MATCH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_MATCH r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LIT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_LIT r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  simp only [beq_iff_eq, noncheck, ite_false] at run
  by_cases selected : s.mode = LENGTH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_LENGTH r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DONE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputTotalFrameX_inflate_DONE r c E.strm l h outcome regs after run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases bad : s.mode = BAD
  · simp only [beq_iff_eq, bad, ite_true, runX_bind, runX_modify, runX_throw] at run
    cases run
    rfl
  simp only [beq_iff_eq, bad, ite_false] at run
  by_cases memory : s.mode = MEM
  all_goals simp only [beq_iff_eq, memory, ite_true, ite_false, runX_throw] at run
  all_goals cases run; rfl

/-- Outside CHECK, the source also retains the local output segment base.
In particular the fast path's RESTORE/call/LOAD sequence retains out_. -/
theorem inflate_dispatch_noncheck_output_base
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (noncheck : s.mode ≠ CHECK)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    regs.out_ = l.out_ := by
  unfold inflate_dispatch at run
  rw [runX_bind, runX_rdS E] at run
  dsimp only at run
  by_cases selected : s.mode = HEAD
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_HEAD l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = FLAGS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_FLAGS l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TIME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_TIME l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = OS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_OS l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXLEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_EXLEN l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = EXTRA
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_EXTRA l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = NAME
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_NAME l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COMMENT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_COMMENT l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = HCRC
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_HCRC l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICTID
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_DICTID l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DICT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_DICT l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_TYPE l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TYPEDO
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_TYPEDO l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = STORED
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_STORED l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_COPY_ l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = COPY
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_COPY l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = TABLE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_TABLE l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENLENS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_LENLENS l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = CODELENS
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_CODELENS l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN_
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_LEN_ l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LEN
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_LEN l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LENEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_LENEXT l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DIST
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_DIST l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DISTEXT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_DISTEXT l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = MATCH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_MATCH l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = LIT
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_LIT l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  simp only [beq_iff_eq, noncheck, ite_false] at run
  by_cases selected : s.mode = LENGTH
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_LENGTH l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases selected : s.mode = DONE
  · simp only [beq_iff_eq, selected, ite_true] at run
    exact outputBaseX_inflate_DONE l.out_ c l h outcome regs after rfl run
  simp only [beq_iff_eq, selected, ite_false] at run
  by_cases bad : s.mode = BAD
  · simp only [beq_iff_eq, bad, ite_true, runX_bind, runX_modify, runX_throw] at run
    cases run
    rfl
  simp only [beq_iff_eq, bad, ite_false] at run
  by_cases memory : s.mode = MEM
  all_goals simp only [beq_iff_eq, memory, ite_true, ite_false, runX_throw] at run
  all_goals cases run; rfl

/-- Every actual default dispatch, including CHECK, preserves one output
ledger. Both non-CHECK frames and the actual CHECK accounting are proved. -/
theorem inflate_dispatch_default_output_ledger
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (getAfter : r.get after = some stream) : OutputLedger z stream l regs := by
  by_cases check : s.mode = CHECK
  · exact inflate_CHECK_default_output_ledger E invariant buffers check
      ((inflate_dispatch_CHECK E l check).symm.trans run) getAfter
  · have total := (inflate_dispatch_noncheck_output_total E check run).output_total E.hz getAfter
    have base := inflate_dispatch_noncheck_output_base E check run
    change stream.total_out + regs.out_.toUInt64 = _
    rw [total, base]

end Zlib.Inflate.Proofs
