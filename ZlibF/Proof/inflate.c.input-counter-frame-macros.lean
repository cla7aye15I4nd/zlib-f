import ZlibF.Proof.«inflate.c.input-counter-frame-fast»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputCounterM_UPDATE_CHECK (r : ZStreamRef) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    InputCounterM r (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine inputCounterM_bind (inputCounterM_rdS r _ _) (fun flags => ?_)
  exact inputCounterM_ite (inputCounterM_crc32 r _ _ _) (inputCounterM_adler32 r _ _ _)

theorem inputCounterX_LOAD (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : InputCounterX r (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_RESTORE (r : ZStreamRef) (state : InflateStatePtr) : InputCounterX r (RESTORE (some r) state) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_INITBITS (r : ZStreamRef)  : InputCounterX r (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_PULLBYTE (r : ZStreamRef)  : InputCounterX r (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_NEEDBITS (r : ZStreamRef) (count : UInt32) : InputCounterX r (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_PULLBYTE r
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_BITS (r : ZStreamRef) (count : UInt32) : InputCounterX r (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_PULLBYTE r
    | with_reducible exact inputCounterX_NEEDBITS r _
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_DROPBITS (r : ZStreamRef) (count : UInt32) : InputCounterX r (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_PULLBYTE r
    | with_reducible exact inputCounterX_NEEDBITS r _
    | with_reducible exact inputCounterX_BITS r _
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_BYTEBITS (r : ZStreamRef)  : InputCounterX r (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_PULLBYTE r
    | with_reducible exact inputCounterX_NEEDBITS r _
    | with_reducible exact inputCounterX_BITS r _
    | with_reducible exact inputCounterX_DROPBITS r _
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_CRC2 (r : ZStreamRef) (context : Ctx) : InputCounterX r (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_PULLBYTE r
    | with_reducible exact inputCounterX_NEEDBITS r _
    | with_reducible exact inputCounterX_BITS r _
    | with_reducible exact inputCounterX_DROPBITS r _
    | with_reducible exact inputCounterX_BYTEBITS r
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_CRC4 (r : ZStreamRef) (context : Ctx) : InputCounterX r (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_PULLBYTE r
    | with_reducible exact inputCounterX_NEEDBITS r _
    | with_reducible exact inputCounterX_BITS r _
    | with_reducible exact inputCounterX_DROPBITS r _
    | with_reducible exact inputCounterX_BYTEBITS r
    | with_reducible exact inputCounterX_CRC2 r _
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : InputCounterX r (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_PULLBYTE r
    | with_reducible exact inputCounterX_NEEDBITS r _
    | with_reducible exact inputCounterX_BITS r _
    | with_reducible exact inputCounterX_DROPBITS r _
    | with_reducible exact inputCounterX_BYTEBITS r
    | with_reducible exact inputCounterX_CRC2 r _
    | with_reducible exact inputCounterX_CRC4 r _
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem inputCounterX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : InputCounterX r (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact inputCounterX_LOAD r _ _
    | with_reducible exact inputCounterX_RESTORE r _
    | with_reducible exact inputCounterX_INITBITS r
    | with_reducible exact inputCounterX_PULLBYTE r
    | with_reducible exact inputCounterX_NEEDBITS r _
    | with_reducible exact inputCounterX_BITS r _
    | with_reducible exact inputCounterX_DROPBITS r _
    | with_reducible exact inputCounterX_BYTEBITS r
    | with_reducible exact inputCounterX_CRC2 r _
    | with_reducible exact inputCounterX_CRC4 r _
    | with_reducible exact inputCounterX_lookup1 r _ _
    | with_reducible exact inputCounterX_pure r _
    | with_reducible exact inputCounterX_get r
    | with_reducible exact inputCounterX_set r _
    | with_reducible exact inputCounterX_modify r _
    | with_reducible exact inputCounterX_throw r _
    | with_reducible apply inputCounterX_lift
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_rdS r _ _
    | with_reducible exact inputCounterM_rdZ r _ _
    | with_reducible exact inputCounterM_wrS_any r _ _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_crc32 r _ _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_shl32 r _ _
    | with_reducible exact inputCounterM_shr32 r _ _
    | with_reducible exact inputCounterM_shl64 r _ _
    | with_reducible exact inputCounterM_shr64 r _ _
    | with_reducible (refine inputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply inputCounterX_xwhile
    | with_reducible apply inputCounterX_xloopBrk
    | with_reducible apply inputCounterX_ite
    | with_reducible (refine inputCounterX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs.InputCounter
