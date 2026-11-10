import ZlibF.Proof.«inflate.c.input-total-fast»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual checksum selection calls the two proved translated checksum frames. -/
theorem inputTotalFrameM_UPDATE_CHECK (r : ZStreamRef) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    InputTotalFrameM r (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine inputTotalFrameM_bind (inputTotalFrameM_rdS r _ _) (fun flags => ?_)
  exact inputTotalFrameM_ite (inputTotalFrameM_crc32 r _ _ _) (inputTotalFrameM_adler32 r _ _ _)

/-- The actual LOAD source macro preserves the public input total. -/
theorem inputTotalFrameX_LOAD (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : InputTotalFrameX r (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual RESTORE source macro preserves the public input total. -/
theorem inputTotalFrameX_RESTORE (r : ZStreamRef) (state : InflateStatePtr) : InputTotalFrameX r (RESTORE (some r) state) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual INITBITS source macro preserves the public input total. -/
theorem inputTotalFrameX_INITBITS (r : ZStreamRef)  : InputTotalFrameX r (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual PULLBYTE source macro preserves the public input total. -/
theorem inputTotalFrameX_PULLBYTE (r : ZStreamRef)  : InputTotalFrameX r (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual NEEDBITS source macro preserves the public input total. -/
theorem inputTotalFrameX_NEEDBITS (r : ZStreamRef) (count : UInt32) : InputTotalFrameX r (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_PULLBYTE r
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BITS source macro preserves the public input total. -/
theorem inputTotalFrameX_BITS (r : ZStreamRef) (count : UInt32) : InputTotalFrameX r (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_PULLBYTE r
    | with_reducible exact inputTotalFrameX_NEEDBITS r _
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual DROPBITS source macro preserves the public input total. -/
theorem inputTotalFrameX_DROPBITS (r : ZStreamRef) (count : UInt32) : InputTotalFrameX r (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_PULLBYTE r
    | with_reducible exact inputTotalFrameX_NEEDBITS r _
    | with_reducible exact inputTotalFrameX_BITS r _
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BYTEBITS source macro preserves the public input total. -/
theorem inputTotalFrameX_BYTEBITS (r : ZStreamRef)  : InputTotalFrameX r (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_PULLBYTE r
    | with_reducible exact inputTotalFrameX_NEEDBITS r _
    | with_reducible exact inputTotalFrameX_BITS r _
    | with_reducible exact inputTotalFrameX_DROPBITS r _
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC2 source macro preserves the public input total. -/
theorem inputTotalFrameX_CRC2 (r : ZStreamRef) (context : Ctx) : InputTotalFrameX r (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_PULLBYTE r
    | with_reducible exact inputTotalFrameX_NEEDBITS r _
    | with_reducible exact inputTotalFrameX_BITS r _
    | with_reducible exact inputTotalFrameX_DROPBITS r _
    | with_reducible exact inputTotalFrameX_BYTEBITS r
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves the public input total. -/
theorem inputTotalFrameX_CRC4 (r : ZStreamRef) (context : Ctx) : InputTotalFrameX r (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_PULLBYTE r
    | with_reducible exact inputTotalFrameX_NEEDBITS r _
    | with_reducible exact inputTotalFrameX_BITS r _
    | with_reducible exact inputTotalFrameX_DROPBITS r _
    | with_reducible exact inputTotalFrameX_BYTEBITS r
    | with_reducible exact inputTotalFrameX_CRC2 r _
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup1 source macro preserves the public input total. -/
theorem inputTotalFrameX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : InputTotalFrameX r (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_PULLBYTE r
    | with_reducible exact inputTotalFrameX_NEEDBITS r _
    | with_reducible exact inputTotalFrameX_BITS r _
    | with_reducible exact inputTotalFrameX_DROPBITS r _
    | with_reducible exact inputTotalFrameX_BYTEBITS r
    | with_reducible exact inputTotalFrameX_CRC2 r _
    | with_reducible exact inputTotalFrameX_CRC4 r _
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup2 source macro preserves the public input total. -/
theorem inputTotalFrameX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : InputTotalFrameX r (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact inputTotalFrameX_LOAD r _ _
    | with_reducible exact inputTotalFrameX_RESTORE r _
    | with_reducible exact inputTotalFrameX_INITBITS r
    | with_reducible exact inputTotalFrameX_PULLBYTE r
    | with_reducible exact inputTotalFrameX_NEEDBITS r _
    | with_reducible exact inputTotalFrameX_BITS r _
    | with_reducible exact inputTotalFrameX_DROPBITS r _
    | with_reducible exact inputTotalFrameX_BYTEBITS r
    | with_reducible exact inputTotalFrameX_CRC2 r _
    | with_reducible exact inputTotalFrameX_CRC4 r _
    | with_reducible exact inputTotalFrameX_lookup1 r _ _
    | with_reducible exact inputTotalFrameX_pure r _
    | with_reducible exact inputTotalFrameX_get r
    | with_reducible exact inputTotalFrameX_set r _
    | with_reducible exact inputTotalFrameX_modify r _
    | with_reducible exact inputTotalFrameX_throw r _
    | with_reducible apply inputTotalFrameX_lift
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_rdS r _ _
    | with_reducible exact inputTotalFrameM_rdZ r _ _
    | with_reducible exact inputTotalFrameM_wrS_any r _ _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_crc32 r _ _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_shl32 r _ _
    | with_reducible exact inputTotalFrameM_shr32 r _ _
    | with_reducible exact inputTotalFrameM_shl64 r _ _
    | with_reducible exact inputTotalFrameM_shr64 r _ _
    | with_reducible (refine inputTotalFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputTotalFrameX_xwhile
    | with_reducible apply inputTotalFrameX_xloopBrk
    | with_reducible apply inputTotalFrameX_ite
    | with_reducible (refine inputTotalFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
