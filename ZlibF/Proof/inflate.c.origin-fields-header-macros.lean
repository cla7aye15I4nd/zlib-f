import ZlibF.Proof.«inflate.c.origin-fields-fast»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A header record write cannot change an inflate state pointer. -/
theorem originFieldFrameM_stHeader (r : ZStreamRef) (owner : InflateStatePtr) (pointer : GzHeaderPtr) (header : GzHeader) :
    OriginFieldFrameM r owner (stGzHeader pointer header) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab id =>
      simp only [stGzHeader, GzHeaderRef.get, GzHeaderRef.isRo, Bool.false_eq_true, ↓reduceIte] at run
      cases get : h.gzheaders id with
      | none => rw [get] at run; cases run
      | some old =>
        rw [get] at run
        cases run
        simp only [OriginFieldFrame, GzHeaderRef.put, get]
        rfl

theorem originFieldFrameX_CRC2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) : OriginFieldFrameX r owner (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_PULLBYTE r owner
    | with_reducible exact originFieldFrameX_NEEDBITS r owner _
    | with_reducible exact originFieldFrameX_BITS r owner _
    | with_reducible exact originFieldFrameX_DROPBITS r owner _
    | with_reducible exact originFieldFrameX_BYTEBITS r owner
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
    | with_reducible exact originFieldFrameM_wrS_any r owner _ _ (fun _ => rfl)
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_wrZ r owner _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves decoder origin fields. -/
theorem originFieldFrameX_CRC4 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) : OriginFieldFrameX r owner (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact originFieldFrameX_LOAD r owner _ _
    | with_reducible exact originFieldFrameX_RESTORE r owner
    | with_reducible exact originFieldFrameX_INITBITS r owner
    | with_reducible exact originFieldFrameX_PULLBYTE r owner
    | with_reducible exact originFieldFrameX_NEEDBITS r owner _
    | with_reducible exact originFieldFrameX_BITS r owner _
    | with_reducible exact originFieldFrameX_DROPBITS r owner _
    | with_reducible exact originFieldFrameX_BYTEBITS r owner
    | with_reducible exact originFieldFrameX_CRC2 r owner _
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
    | with_reducible exact originFieldFrameM_wrS_any r owner _ _ (fun _ => rfl)
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_crc32 r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_wrZ r owner _
    | with_reducible apply originFieldFrameX_xwhile
    | with_reducible apply originFieldFrameX_xloopBrk
    | with_reducible apply originFieldFrameX_ite
    | with_reducible (refine originFieldFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
