import ZlibF.Proof.«inflate.c.live-frame-tables»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual checksum selection calls the two proved translated checksum frames. -/
theorem fastMemoryMetaFrameM_UPDATE_CHECK (r : ZStreamRef) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    FastMemoryMetaFrameM r (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_rdS r _ _) (fun flags => ?_)
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_crc32 r _ _ _) (fastMemoryMetaFrameM_adler32 r _ _ _)

/-- The actual LOAD source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_LOAD (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : FastMemoryMetaFrameX r (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual RESTORE source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_RESTORE (r : ZStreamRef) (state : InflateStatePtr) : FastMemoryMetaFrameX r (RESTORE (some r) state) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual INITBITS source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_INITBITS (r : ZStreamRef)  : FastMemoryMetaFrameX r (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual PULLBYTE source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_PULLBYTE (r : ZStreamRef)  : FastMemoryMetaFrameX r (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual NEEDBITS source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_NEEDBITS (r : ZStreamRef) (count : UInt32) : FastMemoryMetaFrameX r (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_PULLBYTE r
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BITS source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_BITS (r : ZStreamRef) (count : UInt32) : FastMemoryMetaFrameX r (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_PULLBYTE r
    | with_reducible exact fastMemoryMetaFrameX_NEEDBITS r _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual DROPBITS source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_DROPBITS (r : ZStreamRef) (count : UInt32) : FastMemoryMetaFrameX r (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_PULLBYTE r
    | with_reducible exact fastMemoryMetaFrameX_NEEDBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BITS r _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BYTEBITS source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_BYTEBITS (r : ZStreamRef)  : FastMemoryMetaFrameX r (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_PULLBYTE r
    | with_reducible exact fastMemoryMetaFrameX_NEEDBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BITS r _
    | with_reducible exact fastMemoryMetaFrameX_DROPBITS r _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC2 source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_CRC2 (r : ZStreamRef) (context : Ctx) : FastMemoryMetaFrameX r (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_PULLBYTE r
    | with_reducible exact fastMemoryMetaFrameX_NEEDBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BITS r _
    | with_reducible exact fastMemoryMetaFrameX_DROPBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BYTEBITS r
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_CRC4 (r : ZStreamRef) (context : Ctx) : FastMemoryMetaFrameX r (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_PULLBYTE r
    | with_reducible exact fastMemoryMetaFrameX_NEEDBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BITS r _
    | with_reducible exact fastMemoryMetaFrameX_DROPBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BYTEBITS r
    | with_reducible exact fastMemoryMetaFrameX_CRC2 r _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup1 source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : FastMemoryMetaFrameX r (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_PULLBYTE r
    | with_reducible exact fastMemoryMetaFrameX_NEEDBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BITS r _
    | with_reducible exact fastMemoryMetaFrameX_DROPBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BYTEBITS r
    | with_reducible exact fastMemoryMetaFrameX_CRC2 r _
    | with_reducible exact fastMemoryMetaFrameX_CRC4 r _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup2 source macro preserves allocation metadata. -/
theorem fastMemoryMetaFrameX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : FastMemoryMetaFrameX r (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact fastMemoryMetaFrameX_LOAD r _ _
    | with_reducible exact fastMemoryMetaFrameX_RESTORE r _
    | with_reducible exact fastMemoryMetaFrameX_INITBITS r
    | with_reducible exact fastMemoryMetaFrameX_PULLBYTE r
    | with_reducible exact fastMemoryMetaFrameX_NEEDBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BITS r _
    | with_reducible exact fastMemoryMetaFrameX_DROPBITS r _
    | with_reducible exact fastMemoryMetaFrameX_BYTEBITS r
    | with_reducible exact fastMemoryMetaFrameX_CRC2 r _
    | with_reducible exact fastMemoryMetaFrameX_CRC4 r _
    | with_reducible exact fastMemoryMetaFrameX_lookup1 r _ _
    | with_reducible exact fastMemoryMetaFrameX_pure r _
    | with_reducible exact fastMemoryMetaFrameX_get r
    | with_reducible exact fastMemoryMetaFrameX_set r _
    | with_reducible exact fastMemoryMetaFrameX_modify r _
    | with_reducible exact fastMemoryMetaFrameX_throw r _
    | with_reducible apply fastMemoryMetaFrameX_lift
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_rdS r _ _
    | with_reducible exact fastMemoryMetaFrameM_rdZ r _ _
    | with_reducible exact fastMemoryMetaFrameM_wrS_any r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_shr64 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply fastMemoryMetaFrameX_xwhile
    | with_reducible apply fastMemoryMetaFrameX_xloopBrk
    | with_reducible apply fastMemoryMetaFrameX_ite
    | with_reducible (refine fastMemoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
