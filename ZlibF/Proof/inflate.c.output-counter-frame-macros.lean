import ZlibF.Proof.«inflate.c.output-counter-frame-fast»

namespace Zlib.Inflate.Proofs.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem outputCounterM_UPDATE_CHECK (r : ZStreamRef) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    OutputCounterM r (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine outputCounterM_bind (outputCounterM_rdS r _ _) (fun flags => ?_)
  exact outputCounterM_ite (outputCounterM_crc32 r _ _ _) (outputCounterM_adler32 r _ _ _)

theorem outputCounterX_LOAD (r : ZStreamRef) (strm : ZStreamPtr) (state : InflateStatePtr) : OutputCounterX r (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_RESTORE (r : ZStreamRef) (state : InflateStatePtr) : OutputCounterX r (RESTORE (some r) state) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_INITBITS (r : ZStreamRef)  : OutputCounterX r (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_PULLBYTE (r : ZStreamRef)  : OutputCounterX r (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_NEEDBITS (r : ZStreamRef) (count : UInt32) : OutputCounterX r (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_PULLBYTE r
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_BITS (r : ZStreamRef) (count : UInt32) : OutputCounterX r (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_PULLBYTE r
    | with_reducible exact outputCounterX_NEEDBITS r _
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_DROPBITS (r : ZStreamRef) (count : UInt32) : OutputCounterX r (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_PULLBYTE r
    | with_reducible exact outputCounterX_NEEDBITS r _
    | with_reducible exact outputCounterX_BITS r _
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_BYTEBITS (r : ZStreamRef)  : OutputCounterX r (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_PULLBYTE r
    | with_reducible exact outputCounterX_NEEDBITS r _
    | with_reducible exact outputCounterX_BITS r _
    | with_reducible exact outputCounterX_DROPBITS r _
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_CRC2 (r : ZStreamRef) (context : Ctx) : OutputCounterX r (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_PULLBYTE r
    | with_reducible exact outputCounterX_NEEDBITS r _
    | with_reducible exact outputCounterX_BITS r _
    | with_reducible exact outputCounterX_DROPBITS r _
    | with_reducible exact outputCounterX_BYTEBITS r
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_CRC4 (r : ZStreamRef) (context : Ctx) : OutputCounterX r (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_PULLBYTE r
    | with_reducible exact outputCounterX_NEEDBITS r _
    | with_reducible exact outputCounterX_BITS r _
    | with_reducible exact outputCounterX_DROPBITS r _
    | with_reducible exact outputCounterX_BYTEBITS r
    | with_reducible exact outputCounterX_CRC2 r _
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_lookup1 (r : ZStreamRef) (context : Ctx) (distance : Bool) : OutputCounterX r (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_PULLBYTE r
    | with_reducible exact outputCounterX_NEEDBITS r _
    | with_reducible exact outputCounterX_BITS r _
    | with_reducible exact outputCounterX_DROPBITS r _
    | with_reducible exact outputCounterX_BYTEBITS r
    | with_reducible exact outputCounterX_CRC2 r _
    | with_reducible exact outputCounterX_CRC4 r _
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

theorem outputCounterX_lookup2 (r : ZStreamRef) (context : Ctx) (distance : Bool) : OutputCounterX r (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact outputCounterX_LOAD r _ _
    | with_reducible exact outputCounterX_RESTORE r _
    | with_reducible exact outputCounterX_INITBITS r
    | with_reducible exact outputCounterX_PULLBYTE r
    | with_reducible exact outputCounterX_NEEDBITS r _
    | with_reducible exact outputCounterX_BITS r _
    | with_reducible exact outputCounterX_DROPBITS r _
    | with_reducible exact outputCounterX_BYTEBITS r
    | with_reducible exact outputCounterX_CRC2 r _
    | with_reducible exact outputCounterX_CRC4 r _
    | with_reducible exact outputCounterX_lookup1 r _ _
    | with_reducible exact outputCounterX_pure r _
    | with_reducible exact outputCounterX_get r
    | with_reducible exact outputCounterX_set r _
    | with_reducible exact outputCounterX_modify r _
    | with_reducible exact outputCounterX_throw r _
    | with_reducible apply outputCounterX_lift
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_rdS r _ _
    | with_reducible exact outputCounterM_rdZ r _ _
    | with_reducible exact outputCounterM_wrS_any r _ _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_crc32 r _ _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_shl32 r _ _
    | with_reducible exact outputCounterM_shr32 r _ _
    | with_reducible exact outputCounterM_shl64 r _ _
    | with_reducible exact outputCounterM_shr64 r _ _
    | with_reducible (refine outputCounterM_wrZ r _ (fun _ => ?_))
    | with_reducible apply outputCounterX_xwhile
    | with_reducible apply outputCounterX_xloopBrk
    | with_reducible apply outputCounterX_ite
    | with_reducible (refine outputCounterX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs.OutputCounter
