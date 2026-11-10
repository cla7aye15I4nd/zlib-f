import ZlibF.Proof.«inflate.c.input-base-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- Retain the input base of the literal LOAD body. -/
theorem inputBaseX_LOAD (base : UInt32) (strm : ZStreamPtr) (state : InflateStatePtr) : InputBaseX base (LOAD strm state) := by
  unfold LOAD
  input_base_mode base

/-- Retain the input base of the literal RESTORE body. -/
theorem inputBaseX_RESTORE (base : UInt32) (strm : ZStreamPtr) (state : InflateStatePtr) : InputBaseX base (RESTORE strm state) := by
  unfold RESTORE
  input_base_mode base

/-- Retain the input base of the literal INITBITS body. -/
theorem inputBaseX_INITBITS (base : UInt32)  : InputBaseX base (INITBITS) := by
  unfold INITBITS
  input_base_mode base

/-- Retain the input base of the literal PULLBYTE body. -/
theorem inputBaseX_PULLBYTE (base : UInt32)  : InputBaseX base (PULLBYTE) := by
  unfold PULLBYTE
  input_base_mode base

/-- Retain the input base of the literal NEEDBITS body. -/
theorem inputBaseX_NEEDBITS (base : UInt32) (count : UInt32) : InputBaseX base (NEEDBITS count) := by
  unfold NEEDBITS
  have helperPULLBYTE := inputBaseX_PULLBYTE base
  input_base_mode base

/-- Retain the input base of the literal BITS body. -/
theorem inputBaseX_BITS (base : UInt32) (count : UInt32) : InputBaseX base (BITS count) := by
  unfold BITS
  have helperPULLBYTE := inputBaseX_PULLBYTE base
  input_base_mode base

/-- Retain the input base of the literal DROPBITS body. -/
theorem inputBaseX_DROPBITS (base : UInt32) (count : UInt32) : InputBaseX base (DROPBITS count) := by
  unfold DROPBITS
  have helperPULLBYTE := inputBaseX_PULLBYTE base
  input_base_mode base

/-- Retain the input base of the literal BYTEBITS body. -/
theorem inputBaseX_BYTEBITS (base : UInt32)  : InputBaseX base (BYTEBITS) := by
  unfold BYTEBITS
  have helperPULLBYTE := inputBaseX_PULLBYTE base
  input_base_mode base

/-- Retain the input base of the literal CRC2 body. -/
theorem inputBaseX_CRC2 (base : UInt32) (context : Ctx) : InputBaseX base (CRC2 context) := by
  unfold CRC2
  have helperPULLBYTE := inputBaseX_PULLBYTE base
  input_base_mode base

/-- Retain the input base of the literal CRC4 body. -/
theorem inputBaseX_CRC4 (base : UInt32) (context : Ctx) : InputBaseX base (CRC4 context) := by
  unfold CRC4
  have helperPULLBYTE := inputBaseX_PULLBYTE base
  input_base_mode base

/-- Retain the input base of the literal lookup1 body. -/
theorem inputBaseX_lookup1 (base : UInt32) (context : Ctx) (distance : Bool) : InputBaseX base (lookup1 context distance) := by
  unfold lookup1
  have helperPULLBYTE := inputBaseX_PULLBYTE base
  input_base_mode base
  all_goals with_reducible exact inputBaseX_BITS base _

/-- Retain the input base of the literal lookup2 body. -/
theorem inputBaseX_lookup2 (base : UInt32) (context : Ctx) (distance : Bool) : InputBaseX base (lookup2 context distance) := by
  unfold lookup2
  have helperPULLBYTE := inputBaseX_PULLBYTE base
  input_base_mode base

  all_goals with_reducible exact inputBaseX_BITS base _

macro "input_base_source " base:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible exact inputBaseX_LOAD $base _ _
    | with_reducible exact inputBaseX_RESTORE $base _ _
    | with_reducible exact inputBaseX_INITBITS $base
    | with_reducible exact inputBaseX_PULLBYTE $base
    | with_reducible exact inputBaseX_NEEDBITS $base _
    | with_reducible exact inputBaseX_BITS $base _
    | with_reducible exact inputBaseX_DROPBITS $base _
    | with_reducible exact inputBaseX_BYTEBITS $base
    | with_reducible exact inputBaseX_CRC2 $base _
    | with_reducible exact inputBaseX_CRC4 $base _
    | with_reducible exact inputBaseX_lookup1 $base _ _
    | with_reducible exact inputBaseX_lookup2 $base _ _
    | with_reducible assumption
    | with_reducible exact inputBaseX_pure $base _
    | with_reducible exact inputBaseX_get $base
    | with_reducible exact inputBaseX_lift $base _
    | with_reducible exact inputBaseX_throw $base _
    | with_reducible refine inputBaseX_set $base _ ?_
    | with_reducible refine inputBaseX_modify $base _ (fun _ incoming => ?_)
    | with_reducible refine inputBaseX_get_bind (fun _ incoming => ?_)
    | with_reducible apply inputBaseX_xdoWhile
    | with_reducible apply inputBaseX_xwhile
    | with_reducible apply inputBaseX_xwhileBrk
    | with_reducible apply inputBaseX_xloopBrk
    | with_reducible apply inputBaseX_ite
    | with_reducible refine inputBaseX_bind ?_ (fun _ => ?_)
    | split)

end Zlib.Inflate.Proofs
