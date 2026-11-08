import ZlibF.Proof.«inflate.c.stream-frame-fast»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual checksum selection calls the two proved translated checksum frames. -/
theorem streamFrameM_UPDATE_CHECK (r : ZStreamRef) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    StreamFrameM r (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine streamFrameM_bind (streamFrameM_rdS r _ _) (fun flags => ?_)
  exact streamFrameM_ite (streamFrameM_crc32 r _ _ _) (streamFrameM_adler32 r _ _ _)

/-- The actual LOAD source macro preserves fixed stream fields. -/
theorem streamFrameX_LOAD (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : StreamFrameX r (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual RESTORE source macro preserves fixed stream fields. -/
theorem streamFrameX_RESTORE (r : ZStreamRef) (state : InflateStatePtr) : StreamFrameX r (RESTORE (some r) state) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual INITBITS source macro preserves fixed stream fields. -/
theorem streamFrameX_INITBITS (r : ZStreamRef)  : StreamFrameX r (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual PULLBYTE source macro preserves fixed stream fields. -/
theorem streamFrameX_PULLBYTE (r : ZStreamRef)  : StreamFrameX r (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual NEEDBITS source macro preserves fixed stream fields. -/
theorem streamFrameX_NEEDBITS (r : ZStreamRef) (count : UInt32) : StreamFrameX r (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_PULLBYTE r
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BITS source macro preserves fixed stream fields. -/
theorem streamFrameX_BITS (r : ZStreamRef) (count : UInt32) : StreamFrameX r (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_PULLBYTE r
    | with_reducible exact streamFrameX_NEEDBITS r _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual DROPBITS source macro preserves fixed stream fields. -/
theorem streamFrameX_DROPBITS (r : ZStreamRef) (count : UInt32) : StreamFrameX r (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_PULLBYTE r
    | with_reducible exact streamFrameX_NEEDBITS r _
    | with_reducible exact streamFrameX_BITS r _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual BYTEBITS source macro preserves fixed stream fields. -/
theorem streamFrameX_BYTEBITS (r : ZStreamRef)  : StreamFrameX r (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_PULLBYTE r
    | with_reducible exact streamFrameX_NEEDBITS r _
    | with_reducible exact streamFrameX_BITS r _
    | with_reducible exact streamFrameX_DROPBITS r _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC2 source macro preserves fixed stream fields. -/
theorem streamFrameX_CRC2 (r : ZStreamRef) (context : Ctx) : StreamFrameX r (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_PULLBYTE r
    | with_reducible exact streamFrameX_NEEDBITS r _
    | with_reducible exact streamFrameX_BITS r _
    | with_reducible exact streamFrameX_DROPBITS r _
    | with_reducible exact streamFrameX_BYTEBITS r
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves fixed stream fields. -/
theorem streamFrameX_CRC4 (r : ZStreamRef) (context : Ctx) : StreamFrameX r (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_PULLBYTE r
    | with_reducible exact streamFrameX_NEEDBITS r _
    | with_reducible exact streamFrameX_BITS r _
    | with_reducible exact streamFrameX_DROPBITS r _
    | with_reducible exact streamFrameX_BYTEBITS r
    | with_reducible exact streamFrameX_CRC2 r _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup1 source macro preserves fixed stream fields. -/
theorem streamFrameX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : StreamFrameX r (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_PULLBYTE r
    | with_reducible exact streamFrameX_NEEDBITS r _
    | with_reducible exact streamFrameX_BITS r _
    | with_reducible exact streamFrameX_DROPBITS r _
    | with_reducible exact streamFrameX_BYTEBITS r
    | with_reducible exact streamFrameX_CRC2 r _
    | with_reducible exact streamFrameX_CRC4 r _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual lookup2 source macro preserves fixed stream fields. -/
theorem streamFrameX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : StreamFrameX r (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact streamFrameX_LOAD r _ _
    | with_reducible exact streamFrameX_RESTORE r _
    | with_reducible exact streamFrameX_INITBITS r
    | with_reducible exact streamFrameX_PULLBYTE r
    | with_reducible exact streamFrameX_NEEDBITS r _
    | with_reducible exact streamFrameX_BITS r _
    | with_reducible exact streamFrameX_DROPBITS r _
    | with_reducible exact streamFrameX_BYTEBITS r
    | with_reducible exact streamFrameX_CRC2 r _
    | with_reducible exact streamFrameX_CRC4 r _
    | with_reducible exact streamFrameX_lookup1 r _ _
    | with_reducible exact streamFrameX_pure r _
    | with_reducible exact streamFrameX_get r
    | with_reducible exact streamFrameX_set r _
    | with_reducible exact streamFrameX_modify r _
    | with_reducible exact streamFrameX_throw r _
    | with_reducible apply streamFrameX_lift
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_rdS r _ _
    | with_reducible exact streamFrameM_rdZ r _ _
    | with_reducible exact streamFrameM_wrS_any r _ _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_crc32 r _ _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_shl32 r _ _
    | with_reducible exact streamFrameM_shr32 r _ _
    | with_reducible exact streamFrameM_shl64 r _ _
    | with_reducible exact streamFrameM_shr64 r _ _
    | with_reducible (refine streamFrameM_wrZ r _ (fun _ => ?_))
    | with_reducible apply streamFrameX_xwhile
    | with_reducible apply streamFrameX_xloopBrk
    | with_reducible apply streamFrameX_ite
    | with_reducible (refine streamFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
