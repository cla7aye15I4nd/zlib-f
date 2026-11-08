import ZlibF.Proof.«inflate.c.exit-codes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- Classify exits of the literal LOAD body. -/
theorem exitCodesX_LOAD (strm : ZStreamPtr) (state : InflateStatePtr) : ExitCodesX (LOAD strm state) := by
  unfold LOAD
  exit_codes_mode

/-- Classify exits of the literal RESTORE body. -/
theorem exitCodesX_RESTORE (strm : ZStreamPtr) (state : InflateStatePtr) : ExitCodesX (RESTORE strm state) := by
  unfold RESTORE
  exit_codes_mode

/-- Classify exits of the literal INITBITS body. -/
theorem exitCodesX_INITBITS  : ExitCodesX (INITBITS) := by
  unfold INITBITS
  exit_codes_mode

/-- Classify exits of the literal PULLBYTE body. -/
theorem exitCodesX_PULLBYTE  : ExitCodesX (PULLBYTE) := by
  unfold PULLBYTE
  exit_codes_mode

/-- Classify exits of the literal NEEDBITS body. -/
theorem exitCodesX_NEEDBITS (count : UInt32) : ExitCodesX (NEEDBITS count) := by
  unfold NEEDBITS
  have helperPULLBYTE := exitCodesX_PULLBYTE
  exit_codes_mode

/-- Classify exits of the literal BITS body. -/
theorem exitCodesX_BITS (count : UInt32) : ExitCodesX (BITS count) := by
  unfold BITS
  have helperPULLBYTE := exitCodesX_PULLBYTE
  exit_codes_mode

/-- Classify exits of the literal DROPBITS body. -/
theorem exitCodesX_DROPBITS (count : UInt32) : ExitCodesX (DROPBITS count) := by
  unfold DROPBITS
  have helperPULLBYTE := exitCodesX_PULLBYTE
  exit_codes_mode

/-- Classify exits of the literal BYTEBITS body. -/
theorem exitCodesX_BYTEBITS  : ExitCodesX (BYTEBITS) := by
  unfold BYTEBITS
  have helperPULLBYTE := exitCodesX_PULLBYTE
  exit_codes_mode

/-- Classify exits of the literal CRC2 body. -/
theorem exitCodesX_CRC2 (context : Ctx) : ExitCodesX (CRC2 context) := by
  unfold CRC2
  have helperPULLBYTE := exitCodesX_PULLBYTE
  exit_codes_mode

/-- Classify exits of the literal CRC4 body. -/
theorem exitCodesX_CRC4 (context : Ctx) : ExitCodesX (CRC4 context) := by
  unfold CRC4
  have helperPULLBYTE := exitCodesX_PULLBYTE
  exit_codes_mode

/-- Classify exits of the literal lookup1 body. -/
theorem exitCodesX_lookup1 (context : Ctx) (distance : Bool) : ExitCodesX (lookup1 context distance) := by
  unfold lookup1
  have helperPULLBYTE := exitCodesX_PULLBYTE
  exit_codes_mode
  all_goals with_reducible exact exitCodesX_BITS _

/-- Classify exits of the literal lookup2 body. -/
theorem exitCodesX_lookup2 (context : Ctx) (distance : Bool) : ExitCodesX (lookup2 context distance) := by
  unfold lookup2
  have helperPULLBYTE := exitCodesX_PULLBYTE
  exit_codes_mode

  all_goals with_reducible exact exitCodesX_BITS _

macro "exit_codes_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact exitCodesX_LOAD _ _
    | with_reducible exact exitCodesX_RESTORE _ _
    | with_reducible exact exitCodesX_INITBITS
    | with_reducible exact exitCodesX_PULLBYTE
    | with_reducible exact exitCodesX_NEEDBITS _
    | with_reducible exact exitCodesX_BITS _
    | with_reducible exact exitCodesX_DROPBITS _
    | with_reducible exact exitCodesX_BYTEBITS
    | with_reducible exact exitCodesX_CRC2 _
    | with_reducible exact exitCodesX_CRC4 _
    | with_reducible exact exitCodesX_lookup1 _ _
    | with_reducible exact exitCodesX_lookup2 _ _
    | with_reducible assumption
    | with_reducible exact exitCodesX_pure _
    | with_reducible exact exitCodesX_get
    | with_reducible exact exitCodesX_set _
    | with_reducible exact exitCodesX_modify _
    | with_reducible exact exitCodesX_lift _
    | with_reducible refine exitCodesX_throw _ ?_
    | with_reducible apply exitCodesX_xdoWhile
    | with_reducible apply exitCodesX_xwhile
    | with_reducible apply exitCodesX_xwhileBrk
    | with_reducible apply exitCodesX_xloopBrk
    | with_reducible apply exitCodesX_ite
    | with_reducible refine exitCodesX_bind ?_ (fun _ => ?_)
    | trivial
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | with_reducible decide
    | split)

end Zlib.Inflate.Proofs
