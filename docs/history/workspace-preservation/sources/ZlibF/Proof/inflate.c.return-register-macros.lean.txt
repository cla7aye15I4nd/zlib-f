import ZlibF.Proof.«inflate.c.return-register-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- Retain the return register of the literal LOAD body. -/
theorem returnRegisterX_LOAD (base : Int32) (strm : ZStreamPtr) (state : InflateStatePtr) : ReturnRegisterX base (LOAD strm state) := by
  unfold LOAD
  return_register_mode base

/-- Retain the return register of the literal RESTORE body. -/
theorem returnRegisterX_RESTORE (base : Int32) (strm : ZStreamPtr) (state : InflateStatePtr) : ReturnRegisterX base (RESTORE strm state) := by
  unfold RESTORE
  return_register_mode base

/-- Retain the return register of the literal INITBITS body. -/
theorem returnRegisterX_INITBITS (base : Int32)  : ReturnRegisterX base (INITBITS) := by
  unfold INITBITS
  return_register_mode base

/-- Retain the return register of the literal PULLBYTE body. -/
theorem returnRegisterX_PULLBYTE (base : Int32)  : ReturnRegisterX base (PULLBYTE) := by
  unfold PULLBYTE
  return_register_mode base

/-- Retain the return register of the literal NEEDBITS body. -/
theorem returnRegisterX_NEEDBITS (base : Int32) (count : UInt32) : ReturnRegisterX base (NEEDBITS count) := by
  unfold NEEDBITS
  have helperPULLBYTE := returnRegisterX_PULLBYTE base
  return_register_mode base

/-- Retain the return register of the literal BITS body. -/
theorem returnRegisterX_BITS (base : Int32) (count : UInt32) : ReturnRegisterX base (BITS count) := by
  unfold BITS
  have helperPULLBYTE := returnRegisterX_PULLBYTE base
  return_register_mode base

/-- Retain the return register of the literal DROPBITS body. -/
theorem returnRegisterX_DROPBITS (base : Int32) (count : UInt32) : ReturnRegisterX base (DROPBITS count) := by
  unfold DROPBITS
  have helperPULLBYTE := returnRegisterX_PULLBYTE base
  return_register_mode base

/-- Retain the return register of the literal BYTEBITS body. -/
theorem returnRegisterX_BYTEBITS (base : Int32)  : ReturnRegisterX base (BYTEBITS) := by
  unfold BYTEBITS
  have helperPULLBYTE := returnRegisterX_PULLBYTE base
  return_register_mode base

/-- Retain the return register of the literal CRC2 body. -/
theorem returnRegisterX_CRC2 (base : Int32) (context : Ctx) : ReturnRegisterX base (CRC2 context) := by
  unfold CRC2
  have helperPULLBYTE := returnRegisterX_PULLBYTE base
  return_register_mode base

/-- Retain the return register of the literal CRC4 body. -/
theorem returnRegisterX_CRC4 (base : Int32) (context : Ctx) : ReturnRegisterX base (CRC4 context) := by
  unfold CRC4
  have helperPULLBYTE := returnRegisterX_PULLBYTE base
  return_register_mode base

/-- Retain the return register of the literal lookup1 body. -/
theorem returnRegisterX_lookup1 (base : Int32) (context : Ctx) (distance : Bool) : ReturnRegisterX base (lookup1 context distance) := by
  unfold lookup1
  have helperPULLBYTE := returnRegisterX_PULLBYTE base
  return_register_mode base
  all_goals with_reducible exact returnRegisterX_BITS base _

/-- Retain the return register of the literal lookup2 body. -/
theorem returnRegisterX_lookup2 (base : Int32) (context : Ctx) (distance : Bool) : ReturnRegisterX base (lookup2 context distance) := by
  unfold lookup2
  have helperPULLBYTE := returnRegisterX_PULLBYTE base
  return_register_mode base

  all_goals with_reducible exact returnRegisterX_BITS base _

macro "return_register_source " base:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible exact returnRegisterX_LOAD $base _ _
    | with_reducible exact returnRegisterX_RESTORE $base _ _
    | with_reducible exact returnRegisterX_INITBITS $base
    | with_reducible exact returnRegisterX_PULLBYTE $base
    | with_reducible exact returnRegisterX_NEEDBITS $base _
    | with_reducible exact returnRegisterX_BITS $base _
    | with_reducible exact returnRegisterX_DROPBITS $base _
    | with_reducible exact returnRegisterX_BYTEBITS $base
    | with_reducible exact returnRegisterX_CRC2 $base _
    | with_reducible exact returnRegisterX_CRC4 $base _
    | with_reducible exact returnRegisterX_lookup1 $base _ _
    | with_reducible exact returnRegisterX_lookup2 $base _ _
    | with_reducible assumption
    | with_reducible exact returnRegisterX_pure $base _
    | with_reducible exact returnRegisterX_get $base
    | with_reducible exact returnRegisterX_lift $base _
    | with_reducible exact returnRegisterX_throw $base _
    | with_reducible refine returnRegisterX_set $base _ ?_
    | with_reducible refine returnRegisterX_modify $base _ (fun _ incoming => ?_)
    | with_reducible refine returnRegisterX_get_bind (fun _ incoming => ?_)
    | with_reducible apply returnRegisterX_xdoWhile
    | with_reducible apply returnRegisterX_xwhile
    | with_reducible apply returnRegisterX_xwhileBrk
    | with_reducible apply returnRegisterX_xloopBrk
    | with_reducible apply returnRegisterX_ite
    | with_reducible refine returnRegisterX_bind ?_ (fun _ => ?_)
    | split)

end Zlib.Inflate.Proofs
