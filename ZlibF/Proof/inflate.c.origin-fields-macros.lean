import ZlibF.Proof.«inflate.c.origin-fields-checksums»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! The actual bit, lookup and metadata macros retain the origin-field frame.
Every called primitive and checksum has a proved translated-body frame. -/

theorem originFieldFrameM_setMode (r : ZStreamRef) (owner : InflateStatePtr) (mode : UInt32) :
    OriginFieldFrameM r owner (setMode owner mode) := originFieldFrameM_wrS r owner _ (fun _ => rfl)

theorem originFieldFrameM_setMsg (r : ZStreamRef) (owner : InflateStatePtr) (message : String) :
    OriginFieldFrameM r owner (setMsg (some r) message) := by
  unfold setMsg
  exact originFieldFrameM_bind (originFieldFrameM_strLit r owner message) (fun _ => originFieldFrameM_wrZ r owner _)

theorem originFieldFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    OriginFieldFrameM r context.st (badMode context message) := by
  unfold badMode
  rw [root]
  exact originFieldFrameM_bind (originFieldFrameM_setMsg r context.st message) (fun _ => originFieldFrameM_setMode r context.st _)

theorem originFieldFrameX_RESTORE (r : ZStreamRef) (owner : InflateStatePtr) :
    OriginFieldFrameX r owner (RESTORE (some r) owner) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameM_wrZ r owner _
    | with_reducible exact originFieldFrameM_wrS r owner _ (fun _ => rfl)
    | with_reducible apply originFieldFrameX_lift
    | with_reducible refine originFieldFrameX_bind ?_ (fun _ => ?_)

theorem originFieldFrameM_UPDATE_CHECK (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    OriginFieldFrameM r owner (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine originFieldFrameM_bind (originFieldFrameM_rdS r owner _ _) (fun flags => ?_)
  exact originFieldFrameM_ite (originFieldFrameM_crc32 r owner _ _ _) (originFieldFrameM_adler32 r owner _ _ _)

theorem originFieldFrameX_LOAD (r : ZStreamRef) (owner : InflateStatePtr) (strm : ZStreamPtr) (state : InflateStatePtr) : OriginFieldFrameX r owner (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem originFieldFrameX_INITBITS (r : ZStreamRef) (owner : InflateStatePtr)  : OriginFieldFrameX r owner (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner _
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem originFieldFrameX_PULLBYTE (r : ZStreamRef) (owner : InflateStatePtr)  : OriginFieldFrameX r owner (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner _
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem originFieldFrameX_NEEDBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : OriginFieldFrameX r owner (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner _
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_PULLBYTE r owner
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem originFieldFrameX_BITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : OriginFieldFrameX r owner (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner _
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_PULLBYTE r owner
    | with_reducible exact originFieldFrameX_NEEDBITS r owner _
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem originFieldFrameX_DROPBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : OriginFieldFrameX r owner (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner _
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_PULLBYTE r owner
    | with_reducible exact originFieldFrameX_NEEDBITS r owner _
    | with_reducible exact originFieldFrameX_BITS r owner _
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem originFieldFrameX_BYTEBITS (r : ZStreamRef) (owner : InflateStatePtr)  : OriginFieldFrameX r owner (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner _
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_PULLBYTE r owner
    | with_reducible exact originFieldFrameX_NEEDBITS r owner _
    | with_reducible exact originFieldFrameX_BITS r owner _
    | with_reducible exact originFieldFrameX_DROPBITS r owner _
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem originFieldFrameX_lookup1 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : OriginFieldFrameX r owner (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner _
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_PULLBYTE r owner
    | with_reducible exact originFieldFrameX_NEEDBITS r owner _
    | with_reducible exact originFieldFrameX_BITS r owner _
    | with_reducible exact originFieldFrameX_DROPBITS r owner _
    | with_reducible exact originFieldFrameX_BYTEBITS r owner
    | with_reducible exact originFieldFrameX_CRC2 r owner _
    | with_reducible exact originFieldFrameX_CRC4 r owner _
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem originFieldFrameX_lookup2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : OriginFieldFrameX r owner (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner _
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_PULLBYTE r owner
    | with_reducible exact originFieldFrameX_NEEDBITS r owner _
    | with_reducible exact originFieldFrameX_BITS r owner _
    | with_reducible exact originFieldFrameX_DROPBITS r owner _
    | with_reducible exact originFieldFrameX_BYTEBITS r owner
    | with_reducible exact originFieldFrameX_CRC2 r owner _
    | with_reducible exact originFieldFrameX_CRC4 r owner _
    | with_reducible exact originFieldFrameX_lookup1 r owner _ _
    | with_reducible exact originFieldFrameX_pure r owner _
    | with_reducible exact originFieldFrameX_get r owner
    | with_reducible exact originFieldFrameX_set r owner _
    | with_reducible exact originFieldFrameX_modify r owner _
    | with_reducible exact originFieldFrameX_throw r owner _
    | with_reducible apply originFieldFrameX_lift
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_rdS r owner _ _
    | with_reducible exact originFieldFrameM_rdZ r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
