import ZlibF.Proof.«inflate.c.input-base-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual complete mode switch retains the actual input-count base, including terminal modes and all non-default wrapper modes. -/
theorem inputBaseX_inflate_dispatch (base : UInt32) (context : Ctx) : InputBaseX base (inflate_dispatch context) := by
  unfold inflate_dispatch
  have branch0 := inputBaseX_inflate_DONE base context
  have branch1 := inputBaseX_inflate_LENGTH base context
  have branch2 := inputBaseX_inflate_CHECK base context
  have branch3 := inputBaseX_inflate_LIT base context
  have branch4 := inputBaseX_inflate_MATCH base context
  have branch5 := inputBaseX_inflate_DISTEXT base context
  have branch6 := inputBaseX_inflate_DIST base context
  have branch7 := inputBaseX_inflate_LENEXT base context
  have branch8 := inputBaseX_inflate_LEN base context
  have branch9 := inputBaseX_inflate_LEN_ base context
  have branch10 := inputBaseX_inflate_CODELENS base context
  have branch11 := inputBaseX_inflate_LENLENS base context
  have branch12 := inputBaseX_inflate_TABLE base context
  have branch13 := inputBaseX_inflate_COPY base context
  have branch14 := inputBaseX_inflate_COPY_ base context
  have branch15 := inputBaseX_inflate_STORED base context
  have branch16 := inputBaseX_inflate_TYPEDO base context
  have branch17 := inputBaseX_inflate_TYPE base context
  have branch18 := inputBaseX_inflate_DICT base context
  have branch19 := inputBaseX_inflate_DICTID base context
  have branch20 := inputBaseX_inflate_HCRC base context
  have branch21 := inputBaseX_inflate_COMMENT base context
  have branch22 := inputBaseX_inflate_NAME base context
  have branch23 := inputBaseX_inflate_EXTRA base context
  have branch24 := inputBaseX_inflate_EXLEN base context
  have branch25 := inputBaseX_inflate_OS base context
  have branch26 := inputBaseX_inflate_TIME base context
  have branch27 := inputBaseX_inflate_FLAGS base context
  have branch28 := inputBaseX_inflate_HEAD base context
  input_base_source base

/-- Every actual mode-loop execution retains the original input base.
No representation, input range, termination or callee safety is assumed. -/
theorem inputBaseX_inflate_loop (base : UInt32) (context : Ctx) :
    InputBaseX base (xwhile (pure true) (inflate_dispatch context)) :=
  inputBaseX_xwhile (inputBaseX_pure base true) (inputBaseX_inflate_dispatch base context)

theorem inflate_loop_input_base {context : Ctx} {l regs : IL} {h after : Heap} {outcome : Except Ex Unit}
    (run : runX (xwhile (pure true) (inflate_dispatch context)) l h = .ok ((outcome, regs), after)) :
    regs.in_ = l.in_ := inputBaseX_inflate_loop l.in_ context l h outcome regs after rfl run

end Zlib.Inflate.Proofs
