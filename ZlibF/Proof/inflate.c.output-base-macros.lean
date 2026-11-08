import ZlibF.Proof.«inflate.c.output-base-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

theorem outputBaseX_LOAD (base : UInt32) (strm : ZStreamPtr) (st : InflateStatePtr) : OutputBaseX base (LOAD strm st) := by
  unfold LOAD
  repeat' first
    | output_base_source

theorem outputBaseX_RESTORE (base : UInt32) (strm : ZStreamPtr) (st : InflateStatePtr) : OutputBaseX base (RESTORE strm st) := by
  unfold RESTORE
  repeat' first
    | output_base_source

theorem outputBaseX_INITBITS (base : UInt32)  : OutputBaseX base (INITBITS) := by
  unfold INITBITS
  repeat' first
    | output_base_source

theorem outputBaseX_PULLBYTE (base : UInt32)  : OutputBaseX base (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | output_base_source

theorem outputBaseX_NEEDBITS (base : UInt32) (n : UInt32) : OutputBaseX base (NEEDBITS n) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact outputBaseX_PULLBYTE base
    | output_base_source

theorem outputBaseX_BITS (base : UInt32) (n : UInt32) : OutputBaseX base (BITS n) := by
  unfold BITS
  repeat' first
    | output_base_source

theorem outputBaseX_DROPBITS (base : UInt32) (n : UInt32) : OutputBaseX base (DROPBITS n) := by
  unfold DROPBITS
  repeat' first
    | output_base_source

theorem outputBaseX_BYTEBITS (base : UInt32)  : OutputBaseX base (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | output_base_source

theorem outputBaseX_CRC2 (base : UInt32) (c : Ctx) : OutputBaseX base (CRC2 c) := by
  unfold CRC2
  repeat' first
    | output_base_source

theorem outputBaseX_CRC4 (base : UInt32) (c : Ctx) : OutputBaseX base (CRC4 c) := by
  unfold CRC4
  repeat' first
    | output_base_source

theorem outputBaseX_lookup1 (base : UInt32) (c : Ctx) (distance : Bool) : OutputBaseX base (lookup1 c distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact outputBaseX_PULLBYTE base
    | with_reducible exact outputBaseX_BITS base _
    | output_base_source

theorem outputBaseX_lookup2 (base : UInt32) (c : Ctx) (distance : Bool) : OutputBaseX base (lookup2 c distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact outputBaseX_PULLBYTE base
    | with_reducible exact outputBaseX_BITS base _
    | output_base_source


end Zlib.Inflate.Proofs
