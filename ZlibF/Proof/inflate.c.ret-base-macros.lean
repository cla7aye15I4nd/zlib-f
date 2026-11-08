import ZlibF.Proof.«inflate.c.ret-base-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

theorem retBaseX_LOAD (base : Int32) (strm : ZStreamPtr) (st : InflateStatePtr) : RetBaseX base (LOAD strm st) := by
  unfold LOAD
  repeat' first
    | ret_base_source

theorem retBaseX_RESTORE (base : Int32) (strm : ZStreamPtr) (st : InflateStatePtr) : RetBaseX base (RESTORE strm st) := by
  unfold RESTORE
  repeat' first
    | ret_base_source

theorem retBaseX_INITBITS (base : Int32)  : RetBaseX base (INITBITS) := by
  unfold INITBITS
  repeat' first
    | ret_base_source

theorem retBaseX_PULLBYTE (base : Int32)  : RetBaseX base (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | ret_base_source

theorem retBaseX_NEEDBITS (base : Int32) (n : UInt32) : RetBaseX base (NEEDBITS n) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact retBaseX_PULLBYTE base
    | ret_base_source

theorem retBaseX_BITS (base : Int32) (n : UInt32) : RetBaseX base (BITS n) := by
  unfold BITS
  repeat' first
    | ret_base_source

theorem retBaseX_DROPBITS (base : Int32) (n : UInt32) : RetBaseX base (DROPBITS n) := by
  unfold DROPBITS
  repeat' first
    | ret_base_source

theorem retBaseX_BYTEBITS (base : Int32)  : RetBaseX base (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | ret_base_source

theorem retBaseX_CRC2 (base : Int32) (c : Ctx) : RetBaseX base (CRC2 c) := by
  unfold CRC2
  repeat' first
    | ret_base_source

theorem retBaseX_CRC4 (base : Int32) (c : Ctx) : RetBaseX base (CRC4 c) := by
  unfold CRC4
  repeat' first
    | ret_base_source

theorem retBaseX_lookup1 (base : Int32) (c : Ctx) (distance : Bool) : RetBaseX base (lookup1 c distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact retBaseX_PULLBYTE base
    | with_reducible exact retBaseX_BITS base _
    | ret_base_source

theorem retBaseX_lookup2 (base : Int32) (c : Ctx) (distance : Bool) : RetBaseX base (lookup2 c distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact retBaseX_PULLBYTE base
    | with_reducible exact retBaseX_BITS base _
    | ret_base_source


end Zlib.Inflate.Proofs
