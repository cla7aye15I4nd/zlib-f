import ZlibF.Proof.«inflate.c.memory-meta-frame-fast»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual checksum selection calls the two proved translated checksum frames. -/
theorem memoryMetaFrameM_UPDATE_CHECK (r : ZStreamRef) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    MemoryMetaFrameM r (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine memoryMetaFrameM_bind (memoryMetaFrameM_rdS r _ _) (fun flags => ?_)
  exact memoryMetaFrameM_ite (memoryMetaFrameM_crc32 r _ _ _) (memoryMetaFrameM_adler32 r _ _ _)

/-- The actual LOAD source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_LOAD (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : MemoryMetaFrameX r (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual RESTORE source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_RESTORE (r : ZStreamRef) (state : InflateStatePtr) : MemoryMetaFrameX r (RESTORE (some r) state) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual INITBITS source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_INITBITS (r : ZStreamRef)  : MemoryMetaFrameX r (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual PULLBYTE source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_PULLBYTE (r : ZStreamRef)  : MemoryMetaFrameX r (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual NEEDBITS source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_NEEDBITS (r : ZStreamRef) (count : UInt32) : MemoryMetaFrameX r (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_PULLBYTE r
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BITS source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_BITS (r : ZStreamRef) (count : UInt32) : MemoryMetaFrameX r (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_PULLBYTE r
    | with_reducible exact memoryMetaFrameX_NEEDBITS r _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual DROPBITS source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_DROPBITS (r : ZStreamRef) (count : UInt32) : MemoryMetaFrameX r (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_PULLBYTE r
    | with_reducible exact memoryMetaFrameX_NEEDBITS r _
    | with_reducible exact memoryMetaFrameX_BITS r _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BYTEBITS source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_BYTEBITS (r : ZStreamRef)  : MemoryMetaFrameX r (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_PULLBYTE r
    | with_reducible exact memoryMetaFrameX_NEEDBITS r _
    | with_reducible exact memoryMetaFrameX_BITS r _
    | with_reducible exact memoryMetaFrameX_DROPBITS r _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC2 source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_CRC2 (r : ZStreamRef) (context : Ctx) : MemoryMetaFrameX r (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_PULLBYTE r
    | with_reducible exact memoryMetaFrameX_NEEDBITS r _
    | with_reducible exact memoryMetaFrameX_BITS r _
    | with_reducible exact memoryMetaFrameX_DROPBITS r _
    | with_reducible exact memoryMetaFrameX_BYTEBITS r
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_CRC4 (r : ZStreamRef) (context : Ctx) : MemoryMetaFrameX r (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_PULLBYTE r
    | with_reducible exact memoryMetaFrameX_NEEDBITS r _
    | with_reducible exact memoryMetaFrameX_BITS r _
    | with_reducible exact memoryMetaFrameX_DROPBITS r _
    | with_reducible exact memoryMetaFrameX_BYTEBITS r
    | with_reducible exact memoryMetaFrameX_CRC2 r _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup1 source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : MemoryMetaFrameX r (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_PULLBYTE r
    | with_reducible exact memoryMetaFrameX_NEEDBITS r _
    | with_reducible exact memoryMetaFrameX_BITS r _
    | with_reducible exact memoryMetaFrameX_DROPBITS r _
    | with_reducible exact memoryMetaFrameX_BYTEBITS r
    | with_reducible exact memoryMetaFrameX_CRC2 r _
    | with_reducible exact memoryMetaFrameX_CRC4 r _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup2 source macro preserves allocation metadata. -/
theorem memoryMetaFrameX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : MemoryMetaFrameX r (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact memoryMetaFrameX_LOAD r _ _
    | with_reducible exact memoryMetaFrameX_RESTORE r _
    | with_reducible exact memoryMetaFrameX_INITBITS r
    | with_reducible exact memoryMetaFrameX_PULLBYTE r
    | with_reducible exact memoryMetaFrameX_NEEDBITS r _
    | with_reducible exact memoryMetaFrameX_BITS r _
    | with_reducible exact memoryMetaFrameX_DROPBITS r _
    | with_reducible exact memoryMetaFrameX_BYTEBITS r
    | with_reducible exact memoryMetaFrameX_CRC2 r _
    | with_reducible exact memoryMetaFrameX_CRC4 r _
    | with_reducible exact memoryMetaFrameX_lookup1 r _ _
    | with_reducible exact memoryMetaFrameX_pure r _
    | with_reducible exact memoryMetaFrameX_get r
    | with_reducible exact memoryMetaFrameX_set r _
    | with_reducible exact memoryMetaFrameX_modify r _
    | with_reducible exact memoryMetaFrameX_throw r _
    | with_reducible apply memoryMetaFrameX_lift
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_rdS r _ _
    | with_reducible exact memoryMetaFrameM_rdZ r _ _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_crc32 r _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_shr64 r _ _
    | with_reducible (refine memoryMetaFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply memoryMetaFrameX_xwhile
    | with_reducible apply memoryMetaFrameX_xloopBrk
    | with_reducible apply memoryMetaFrameX_ite
    | with_reducible (refine memoryMetaFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
