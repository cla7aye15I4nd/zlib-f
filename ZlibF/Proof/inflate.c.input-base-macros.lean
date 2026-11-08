import ZlibF.Proof.«inflate.c.input-base-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

theorem inputBaseX_LOAD (base : UInt32) (strm : ZStreamPtr) (st : InflateStatePtr) : InputBaseX base (LOAD strm st) := by
  unfold LOAD
  repeat' first
    | input_base_source

theorem inputBaseX_RESTORE (base : UInt32) (strm : ZStreamPtr) (st : InflateStatePtr) : InputBaseX base (RESTORE strm st) := by
  unfold RESTORE
  repeat' first
    | input_base_source

theorem inputBaseX_INITBITS (base : UInt32)  : InputBaseX base (INITBITS) := by
  unfold INITBITS
  repeat' first
    | input_base_source

theorem inputBaseX_PULLBYTE (base : UInt32)  : InputBaseX base (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | input_base_source

theorem inputBaseX_NEEDBITS (base : UInt32) (n : UInt32) : InputBaseX base (NEEDBITS n) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact inputBaseX_PULLBYTE base
    | input_base_source

theorem inputBaseX_BITS (base : UInt32) (n : UInt32) : InputBaseX base (BITS n) := by
  unfold BITS
  repeat' first
    | input_base_source

theorem inputBaseX_DROPBITS (base : UInt32) (n : UInt32) : InputBaseX base (DROPBITS n) := by
  unfold DROPBITS
  repeat' first
    | input_base_source

theorem inputBaseX_BYTEBITS (base : UInt32)  : InputBaseX base (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | input_base_source

theorem inputBaseX_CRC2 (base : UInt32) (c : Ctx) : InputBaseX base (CRC2 c) := by
  unfold CRC2
  repeat' first
    | input_base_source

theorem inputBaseX_CRC4 (base : UInt32) (c : Ctx) : InputBaseX base (CRC4 c) := by
  unfold CRC4
  repeat' first
    | input_base_source

theorem inputBaseX_lookup1 (base : UInt32) (c : Ctx) (distance : Bool) : InputBaseX base (lookup1 c distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact inputBaseX_PULLBYTE base
    | with_reducible exact inputBaseX_BITS base _
    | input_base_source

theorem inputBaseX_lookup2 (base : UInt32) (c : Ctx) (distance : Bool) : InputBaseX base (lookup2 c distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact inputBaseX_PULLBYTE base
    | with_reducible exact inputBaseX_BITS base _
    | input_base_source


end Zlib.Inflate.Proofs
