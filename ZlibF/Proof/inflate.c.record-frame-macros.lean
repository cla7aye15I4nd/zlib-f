import ZlibF.Proof.«inflate.c.record-frame-checksums»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! The actual bit, lookup and metadata macros retain the record frame.
Every called primitive and checksum has a proved translated-body frame. -/

theorem recordFrameM_setMode (r : ZStreamRef) (owner : InflateStatePtr) (mode : UInt32) :
    RecordFrameM r owner (setMode owner mode) := recordFrameM_wrS r owner _

theorem recordFrameM_setMsg (r : ZStreamRef) (owner : InflateStatePtr) (message : String) :
    RecordFrameM r owner (setMsg (some r) message) := by
  unfold setMsg
  exact recordFrameM_bind (recordFrameM_strLit r owner message) (fun _ => recordFrameM_wrZ r owner _)

theorem recordFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    RecordFrameM r context.st (badMode context message) := by
  unfold badMode
  rw [root]
  exact recordFrameM_bind (recordFrameM_setMsg r context.st message) (fun _ => recordFrameM_setMode r context.st _)

theorem recordFrameM_inflate_fixed (r : ZStreamRef) (owner : InflateStatePtr) :
    RecordFrameM r owner (Zlib.Inftrees.inflate_fixed owner) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_stS r owner _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible refine recordFrameM_bind ?_ (fun _ => ?_)

theorem recordFrameX_RESTORE (r : ZStreamRef) (owner : InflateStatePtr) :
    RecordFrameX r owner (RESTORE (some r) owner) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameM_wrZ r owner _
    | with_reducible exact recordFrameM_wrS r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible refine recordFrameX_bind ?_ (fun _ => ?_)

theorem recordFrameM_UPDATE_CHECK (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    RecordFrameM r owner (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine recordFrameM_bind (recordFrameM_rdS r owner _ _) (fun flags => ?_)
  exact recordFrameM_ite (recordFrameM_crc32 r owner _ _ _) (recordFrameM_adler32 r owner _ _ _)

theorem recordFrameX_LOAD (r : ZStreamRef) (owner : InflateStatePtr) (strm : ZStreamPtr) (state : InflateStatePtr) : RecordFrameX r owner (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem recordFrameX_INITBITS (r : ZStreamRef) (owner : InflateStatePtr)  : RecordFrameX r owner (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact recordFrameX_LOAD r owner _ _
    | with_reducible exact recordFrameX_RESTORE r owner _
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem recordFrameX_PULLBYTE (r : ZStreamRef) (owner : InflateStatePtr)  : RecordFrameX r owner (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact recordFrameX_LOAD r owner _ _
    | with_reducible exact recordFrameX_RESTORE r owner _
    | with_reducible exact recordFrameX_INITBITS r owner
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem recordFrameX_NEEDBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : RecordFrameX r owner (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact recordFrameX_LOAD r owner _ _
    | with_reducible exact recordFrameX_RESTORE r owner _
    | with_reducible exact recordFrameX_INITBITS r owner
    | with_reducible exact recordFrameX_PULLBYTE r owner
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem recordFrameX_BITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : RecordFrameX r owner (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact recordFrameX_LOAD r owner _ _
    | with_reducible exact recordFrameX_RESTORE r owner _
    | with_reducible exact recordFrameX_INITBITS r owner
    | with_reducible exact recordFrameX_PULLBYTE r owner
    | with_reducible exact recordFrameX_NEEDBITS r owner _
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem recordFrameX_DROPBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : RecordFrameX r owner (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact recordFrameX_LOAD r owner _ _
    | with_reducible exact recordFrameX_RESTORE r owner _
    | with_reducible exact recordFrameX_INITBITS r owner
    | with_reducible exact recordFrameX_PULLBYTE r owner
    | with_reducible exact recordFrameX_NEEDBITS r owner _
    | with_reducible exact recordFrameX_BITS r owner _
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem recordFrameX_BYTEBITS (r : ZStreamRef) (owner : InflateStatePtr)  : RecordFrameX r owner (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact recordFrameX_LOAD r owner _ _
    | with_reducible exact recordFrameX_RESTORE r owner _
    | with_reducible exact recordFrameX_INITBITS r owner
    | with_reducible exact recordFrameX_PULLBYTE r owner
    | with_reducible exact recordFrameX_NEEDBITS r owner _
    | with_reducible exact recordFrameX_BITS r owner _
    | with_reducible exact recordFrameX_DROPBITS r owner _
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem recordFrameX_lookup1 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : RecordFrameX r owner (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact recordFrameX_LOAD r owner _ _
    | with_reducible exact recordFrameX_RESTORE r owner _
    | with_reducible exact recordFrameX_INITBITS r owner
    | with_reducible exact recordFrameX_PULLBYTE r owner
    | with_reducible exact recordFrameX_NEEDBITS r owner _
    | with_reducible exact recordFrameX_BITS r owner _
    | with_reducible exact recordFrameX_DROPBITS r owner _
    | with_reducible exact recordFrameX_BYTEBITS r owner
    | with_reducible exact recordFrameX_CRC2 r owner _
    | with_reducible exact recordFrameX_CRC4 r owner _
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem recordFrameX_lookup2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : RecordFrameX r owner (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact recordFrameX_LOAD r owner _ _
    | with_reducible exact recordFrameX_RESTORE r owner _
    | with_reducible exact recordFrameX_INITBITS r owner
    | with_reducible exact recordFrameX_PULLBYTE r owner
    | with_reducible exact recordFrameX_NEEDBITS r owner _
    | with_reducible exact recordFrameX_BITS r owner _
    | with_reducible exact recordFrameX_DROPBITS r owner _
    | with_reducible exact recordFrameX_BYTEBITS r owner
    | with_reducible exact recordFrameX_CRC2 r owner _
    | with_reducible exact recordFrameX_CRC4 r owner _
    | with_reducible exact recordFrameX_lookup1 r owner _ _
    | with_reducible exact recordFrameX_pure r owner _
    | with_reducible exact recordFrameX_get r owner
    | with_reducible exact recordFrameX_set r owner _
    | with_reducible exact recordFrameX_modify r owner _
    | with_reducible exact recordFrameX_throw r owner _
    | with_reducible apply recordFrameX_lift
    | with_reducible exact recordFrameM_ldS r owner _
    | with_reducible exact recordFrameM_ldZ r owner _
    | with_reducible exact recordFrameM_rdS r owner _ _
    | with_reducible exact recordFrameM_rdZ r owner _ _
    | with_reducible exact recordFrameM_crc32 r owner _ _ _
    | with_reducible exact recordFrameM_ptr_load r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_shl32 r owner _ _
    | with_reducible exact recordFrameM_shr32 r owner _ _
    | with_reducible exact recordFrameM_shl64 r owner _ _
    | with_reducible exact recordFrameM_shr64 r owner _ _
    | with_reducible apply recordFrameX_xwhile
    | with_reducible apply recordFrameX_xloopBrk
    | with_reducible apply recordFrameX_ite
    | with_reducible (refine recordFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
