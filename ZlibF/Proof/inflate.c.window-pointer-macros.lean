import ZlibF.Proof.«inflate.c.window-pointer-checksums»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! The actual bit, lookup and metadata macros retain the window-pointer frame.
Every called primitive and checksum has a proved translated-body frame. -/

theorem windowFrameM_setMode (r : ZStreamRef) (owner : InflateStatePtr) (mode : UInt32) :
    WindowFrameM r owner (setMode owner mode) := windowFrameM_wrS r owner _ (fun _ => rfl)

theorem windowFrameM_setMsg (r : ZStreamRef) (owner : InflateStatePtr) (message : String) :
    WindowFrameM r owner (setMsg (some r) message) := by
  unfold setMsg
  exact windowFrameM_bind (windowFrameM_strLit r owner message) (fun _ => windowFrameM_wrZ r owner _)

theorem windowFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    WindowFrameM r context.st (badMode context message) := by
  unfold badMode
  rw [root]
  exact windowFrameM_bind (windowFrameM_setMsg r context.st message) (fun _ => windowFrameM_setMode r context.st _)

theorem windowFrameM_inflate_fixed (r : ZStreamRef) (owner : InflateStatePtr) :
    WindowFrameM r owner (Zlib.Inftrees.inflate_fixed owner) := by
  intro h value after run
  cases owner with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [Zlib.Inftrees.inflate_fixed, bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [Zlib.Inftrees.inflate_fixed, bind_app, ldI_eq, stI_eq, get,
          Option.isSome_some, ↓reduceIte, setI_istates_same, setI_setI] at run
        cases run
        exact decoderWindows_setI get rfl

theorem windowFrameX_RESTORE (r : ZStreamRef) (owner : InflateStatePtr) :
    WindowFrameX r owner (RESTORE (some r) owner) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible exact windowFrameM_wrS r owner _ (fun _ => rfl)
    | with_reducible apply windowFrameX_lift
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

theorem windowFrameM_UPDATE_CHECK (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine windowFrameM_bind (windowFrameM_rdS r owner _ _) (fun flags => ?_)
  exact windowFrameM_ite (windowFrameM_crc32 r owner _ _ _) (windowFrameM_adler32 r owner _ _ _)

theorem windowFrameX_LOAD (r : ZStreamRef) (owner : InflateStatePtr) (strm : ZStreamPtr) (state : InflateStatePtr) : WindowFrameX r owner (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_INITBITS (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_PULLBYTE (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_NEEDBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_BITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_DROPBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_BYTEBITS (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_lookup1 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : WindowFrameX r owner (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
    | with_reducible exact windowFrameX_CRC4 r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_lookup2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : WindowFrameX r owner (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
    | with_reducible exact windowFrameX_CRC4 r owner _
    | with_reducible exact windowFrameX_lookup1 r owner _ _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
