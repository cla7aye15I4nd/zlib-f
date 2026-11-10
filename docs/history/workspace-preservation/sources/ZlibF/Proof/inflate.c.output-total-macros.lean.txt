import ZlibF.Proof.«inflate.c.output-total-fast»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual checksum selection calls the two proved translated checksum frames. -/
theorem outputTotalFrameM_UPDATE_CHECK (r : ZStreamRef) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    OutputTotalFrameM r (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine outputTotalFrameM_bind (outputTotalFrameM_rdS r _ _) (fun flags => ?_)
  exact outputTotalFrameM_ite (outputTotalFrameM_crc32 r _ _ _) (outputTotalFrameM_adler32 r _ _ _)

/-- The actual LOAD source macro preserves the public output total. -/
theorem outputTotalFrameX_LOAD (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : OutputTotalFrameX r (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual RESTORE source macro preserves the public output total. -/
theorem outputTotalFrameX_RESTORE (r : ZStreamRef) (state : InflateStatePtr) : OutputTotalFrameX r (RESTORE (some r) state) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual INITBITS source macro preserves the public output total. -/
theorem outputTotalFrameX_INITBITS (r : ZStreamRef)  : OutputTotalFrameX r (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual PULLBYTE source macro preserves the public output total. -/
theorem outputTotalFrameX_PULLBYTE (r : ZStreamRef)  : OutputTotalFrameX r (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual NEEDBITS source macro preserves the public output total. -/
theorem outputTotalFrameX_NEEDBITS (r : ZStreamRef) (count : UInt32) : OutputTotalFrameX r (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_PULLBYTE r
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BITS source macro preserves the public output total. -/
theorem outputTotalFrameX_BITS (r : ZStreamRef) (count : UInt32) : OutputTotalFrameX r (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_PULLBYTE r
    | with_reducible exact outputTotalFrameX_NEEDBITS r _
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual DROPBITS source macro preserves the public output total. -/
theorem outputTotalFrameX_DROPBITS (r : ZStreamRef) (count : UInt32) : OutputTotalFrameX r (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_PULLBYTE r
    | with_reducible exact outputTotalFrameX_NEEDBITS r _
    | with_reducible exact outputTotalFrameX_BITS r _
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BYTEBITS source macro preserves the public output total. -/
theorem outputTotalFrameX_BYTEBITS (r : ZStreamRef)  : OutputTotalFrameX r (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_PULLBYTE r
    | with_reducible exact outputTotalFrameX_NEEDBITS r _
    | with_reducible exact outputTotalFrameX_BITS r _
    | with_reducible exact outputTotalFrameX_DROPBITS r _
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC2 source macro preserves the public output total. -/
theorem outputTotalFrameX_CRC2 (r : ZStreamRef) (context : Ctx) : OutputTotalFrameX r (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_PULLBYTE r
    | with_reducible exact outputTotalFrameX_NEEDBITS r _
    | with_reducible exact outputTotalFrameX_BITS r _
    | with_reducible exact outputTotalFrameX_DROPBITS r _
    | with_reducible exact outputTotalFrameX_BYTEBITS r
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves the public output total. -/
theorem outputTotalFrameX_CRC4 (r : ZStreamRef) (context : Ctx) : OutputTotalFrameX r (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_PULLBYTE r
    | with_reducible exact outputTotalFrameX_NEEDBITS r _
    | with_reducible exact outputTotalFrameX_BITS r _
    | with_reducible exact outputTotalFrameX_DROPBITS r _
    | with_reducible exact outputTotalFrameX_BYTEBITS r
    | with_reducible exact outputTotalFrameX_CRC2 r _
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup1 source macro preserves the public output total. -/
theorem outputTotalFrameX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : OutputTotalFrameX r (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_PULLBYTE r
    | with_reducible exact outputTotalFrameX_NEEDBITS r _
    | with_reducible exact outputTotalFrameX_BITS r _
    | with_reducible exact outputTotalFrameX_DROPBITS r _
    | with_reducible exact outputTotalFrameX_BYTEBITS r
    | with_reducible exact outputTotalFrameX_CRC2 r _
    | with_reducible exact outputTotalFrameX_CRC4 r _
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup2 source macro preserves the public output total. -/
theorem outputTotalFrameX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : OutputTotalFrameX r (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact outputTotalFrameX_LOAD r _ _
    | with_reducible exact outputTotalFrameX_RESTORE r _
    | with_reducible exact outputTotalFrameX_INITBITS r
    | with_reducible exact outputTotalFrameX_PULLBYTE r
    | with_reducible exact outputTotalFrameX_NEEDBITS r _
    | with_reducible exact outputTotalFrameX_BITS r _
    | with_reducible exact outputTotalFrameX_DROPBITS r _
    | with_reducible exact outputTotalFrameX_BYTEBITS r
    | with_reducible exact outputTotalFrameX_CRC2 r _
    | with_reducible exact outputTotalFrameX_CRC4 r _
    | with_reducible exact outputTotalFrameX_lookup1 r _ _
    | with_reducible exact outputTotalFrameX_pure r _
    | with_reducible exact outputTotalFrameX_get r
    | with_reducible exact outputTotalFrameX_set r _
    | with_reducible exact outputTotalFrameX_modify r _
    | with_reducible exact outputTotalFrameX_throw r _
    | with_reducible apply outputTotalFrameX_lift
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_rdS r _ _
    | with_reducible exact outputTotalFrameM_rdZ r _ _
    | with_reducible exact outputTotalFrameM_wrS_any r _ _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_crc32 r _ _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_shl32 r _ _
    | with_reducible exact outputTotalFrameM_shr32 r _ _
    | with_reducible exact outputTotalFrameM_shl64 r _ _
    | with_reducible exact outputTotalFrameM_shr64 r _ _
    | with_reducible (refine outputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputTotalFrameX_xwhile
    | with_reducible apply outputTotalFrameX_xloopBrk
    | with_reducible apply outputTotalFrameX_ite
    | with_reducible (refine outputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
