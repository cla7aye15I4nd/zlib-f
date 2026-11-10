import ZlibF.Proof.«inflate.c.exit-code-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual complete mode switch has exactly the classified direct
return codes, including terminal modes and all non-default wrapper modes. -/
theorem exitCodesX_inflate_dispatch (context : Ctx) : ExitCodesX (inflate_dispatch context) := by
  unfold inflate_dispatch
  have branch0 := exitCodesX_inflate_DONE context
  have branch1 := exitCodesX_inflate_LENGTH context
  have branch2 := exitCodesX_inflate_CHECK context
  have branch3 := exitCodesX_inflate_LIT context
  have branch4 := exitCodesX_inflate_MATCH context
  have branch5 := exitCodesX_inflate_DISTEXT context
  have branch6 := exitCodesX_inflate_DIST context
  have branch7 := exitCodesX_inflate_LENEXT context
  have branch8 := exitCodesX_inflate_LEN context
  have branch9 := exitCodesX_inflate_LEN_ context
  have branch10 := exitCodesX_inflate_CODELENS context
  have branch11 := exitCodesX_inflate_LENLENS context
  have branch12 := exitCodesX_inflate_TABLE context
  have branch13 := exitCodesX_inflate_COPY context
  have branch14 := exitCodesX_inflate_COPY_ context
  have branch15 := exitCodesX_inflate_STORED context
  have branch16 := exitCodesX_inflate_TYPEDO context
  have branch17 := exitCodesX_inflate_TYPE context
  have branch18 := exitCodesX_inflate_DICT context
  have branch19 := exitCodesX_inflate_DICTID context
  have branch20 := exitCodesX_inflate_HCRC context
  have branch21 := exitCodesX_inflate_COMMENT context
  have branch22 := exitCodesX_inflate_NAME context
  have branch23 := exitCodesX_inflate_EXTRA context
  have branch24 := exitCodesX_inflate_EXLEN context
  have branch25 := exitCodesX_inflate_OS context
  have branch26 := exitCodesX_inflate_TIME context
  have branch27 := exitCodesX_inflate_FLAGS context
  have branch28 := exitCodesX_inflate_HEAD context
  exit_codes_source

/-- Entry normalization, LOAD and the entire actual mode loop retain the
classified direct-return set on every successfully returning execution.
No input, representation, mode or callee safety contract is assumed. -/
theorem exitCodesX_inflate_run (context : Ctx) : ExitCodesX (inflate_run context) := by
  unfold inflate_run
  have dispatch := exitCodesX_inflate_dispatch context
  exit_codes_source

/-- Every actual direct return from the complete body is a dictionary
request, memory error or stream error. Ordinary inf_leave remains distinct. -/
theorem inflate_run_direct_codes {context : Ctx} {l regs : IL} {h after : Heap} {code : Int32}
    (run : runX (inflate_run context) l h = .ok ((.error (.ret code), regs), after)) :
    code = Z_NEED_DICT ∨ code = Z_MEM_ERROR ∨ code = Z_STREAM_ERROR :=
  exitCodesX_inflate_run context l h (.error (.ret code)) regs after run (.ret code) rfl

end Zlib.Inflate.Proofs
