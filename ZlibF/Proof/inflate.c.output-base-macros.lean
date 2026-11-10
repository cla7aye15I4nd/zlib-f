import ZlibF.Proof.«inflate.c.output-base-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- Retain the output base of the literal LOAD body. -/
theorem outputBaseX_LOAD (base : UInt32) (strm : ZStreamPtr) (state : InflateStatePtr) : OutputBaseX base (LOAD strm state) := by
  unfold LOAD
  output_base_mode base

/-- Retain the output base of the literal RESTORE body. -/
theorem outputBaseX_RESTORE (base : UInt32) (strm : ZStreamPtr) (state : InflateStatePtr) : OutputBaseX base (RESTORE strm state) := by
  unfold RESTORE
  output_base_mode base

/-- Retain the output base of the literal INITBITS body. -/
theorem outputBaseX_INITBITS (base : UInt32)  : OutputBaseX base (INITBITS) := by
  unfold INITBITS
  output_base_mode base

/-- Retain the output base of the literal PULLBYTE body. -/
theorem outputBaseX_PULLBYTE (base : UInt32)  : OutputBaseX base (PULLBYTE) := by
  unfold PULLBYTE
  output_base_mode base

/-- Retain the output base of the literal NEEDBITS body. -/
theorem outputBaseX_NEEDBITS (base : UInt32) (count : UInt32) : OutputBaseX base (NEEDBITS count) := by
  unfold NEEDBITS
  have helperPULLBYTE := outputBaseX_PULLBYTE base
  output_base_mode base

/-- Retain the output base of the literal BITS body. -/
theorem outputBaseX_BITS (base : UInt32) (count : UInt32) : OutputBaseX base (BITS count) := by
  unfold BITS
  have helperPULLBYTE := outputBaseX_PULLBYTE base
  output_base_mode base

/-- Retain the output base of the literal DROPBITS body. -/
theorem outputBaseX_DROPBITS (base : UInt32) (count : UInt32) : OutputBaseX base (DROPBITS count) := by
  unfold DROPBITS
  have helperPULLBYTE := outputBaseX_PULLBYTE base
  output_base_mode base

/-- Retain the output base of the literal BYTEBITS body. -/
theorem outputBaseX_BYTEBITS (base : UInt32)  : OutputBaseX base (BYTEBITS) := by
  unfold BYTEBITS
  have helperPULLBYTE := outputBaseX_PULLBYTE base
  output_base_mode base

/-- Retain the output base of the literal CRC2 body. -/
theorem outputBaseX_CRC2 (base : UInt32) (context : Ctx) : OutputBaseX base (CRC2 context) := by
  unfold CRC2
  have helperPULLBYTE := outputBaseX_PULLBYTE base
  output_base_mode base

/-- Retain the output base of the literal CRC4 body. -/
theorem outputBaseX_CRC4 (base : UInt32) (context : Ctx) : OutputBaseX base (CRC4 context) := by
  unfold CRC4
  have helperPULLBYTE := outputBaseX_PULLBYTE base
  output_base_mode base

/-- Retain the output base of the literal lookup1 body. -/
theorem outputBaseX_lookup1 (base : UInt32) (context : Ctx) (distance : Bool) : OutputBaseX base (lookup1 context distance) := by
  unfold lookup1
  have helperPULLBYTE := outputBaseX_PULLBYTE base
  output_base_mode base
  all_goals with_reducible exact outputBaseX_BITS base _

/-- Retain the output base of the literal lookup2 body. -/
theorem outputBaseX_lookup2 (base : UInt32) (context : Ctx) (distance : Bool) : OutputBaseX base (lookup2 context distance) := by
  unfold lookup2
  have helperPULLBYTE := outputBaseX_PULLBYTE base
  output_base_mode base

  all_goals with_reducible exact outputBaseX_BITS base _

macro "output_base_source " base:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible exact outputBaseX_LOAD $base _ _
    | with_reducible exact outputBaseX_RESTORE $base _ _
    | with_reducible exact outputBaseX_INITBITS $base
    | with_reducible exact outputBaseX_PULLBYTE $base
    | with_reducible exact outputBaseX_NEEDBITS $base _
    | with_reducible exact outputBaseX_BITS $base _
    | with_reducible exact outputBaseX_DROPBITS $base _
    | with_reducible exact outputBaseX_BYTEBITS $base
    | with_reducible exact outputBaseX_CRC2 $base _
    | with_reducible exact outputBaseX_CRC4 $base _
    | with_reducible exact outputBaseX_lookup1 $base _ _
    | with_reducible exact outputBaseX_lookup2 $base _ _
    | with_reducible assumption
    | with_reducible exact outputBaseX_pure $base _
    | with_reducible exact outputBaseX_get $base
    | with_reducible exact outputBaseX_lift $base _
    | with_reducible exact outputBaseX_throw $base _
    | with_reducible refine outputBaseX_set $base _ ?_
    | with_reducible refine outputBaseX_modify $base _ (fun _ incoming => ?_)
    | with_reducible refine outputBaseX_get_bind (fun _ incoming => ?_)
    | with_reducible apply outputBaseX_xdoWhile
    | with_reducible apply outputBaseX_xwhile
    | with_reducible apply outputBaseX_xwhileBrk
    | with_reducible apply outputBaseX_xloopBrk
    | with_reducible apply outputBaseX_ite
    | with_reducible refine outputBaseX_bind ?_ (fun _ => ?_)
    | split)

end Zlib.Inflate.Proofs
