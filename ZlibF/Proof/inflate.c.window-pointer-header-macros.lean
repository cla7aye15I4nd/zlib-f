import ZlibF.Proof.«inflate.c.window-pointer-fast»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A header record write cannot change an inflate state pointer. -/
theorem windowFrameM_stHeader (r : ZStreamRef) (owner : InflateStatePtr) (pointer : GzHeaderPtr) (header : GzHeader) :
    WindowFrameM r owner (stGzHeader pointer header) := by
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
        simp only [WindowFrame, GzHeaderRef.put, get]
        rfl

theorem windowFrameX_CRC2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) : WindowFrameX r owner (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
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
    | with_reducible exact windowFrameM_wrS_any r owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves decoder window pointers. -/
theorem windowFrameX_CRC4 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) : WindowFrameX r owner (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
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
    | with_reducible exact windowFrameM_wrS_any r owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
