import ZlibF.Proof.«inflate.c.window-pointer-tables»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem windowFrameM_fast_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_shl64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_chk64 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_subn (r : ZStreamRef) (owner : InflateStatePtr) (pointer : BPtr) (count : UInt32) : WindowFrameM r owner (Zlib.Inffast.subn pointer count) :=
  windowFrameM_ptr_add r owner _ _

theorem windowFrameM_fast_pull (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ =>
      windowFrameM_bind (windowFrameM_fast_shl64 r owner _ _) (fun _ => windowFrameM_pure r owner _)))

theorem windowFrameM_fast_copy1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ =>
      windowFrameM_bind (windowFrameM_store8 r owner _ _) (fun _ =>
        windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ => windowFrameM_pure r owner _))))

theorem windowFrameM_fast_copyOp (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.copyOp state) :=
  windowFrameM_cdoWhile (windowFrameM_fast_copy1 r owner) (fun _ => windowFrameM_pure r owner _) state

/-- Actual fast-decoder diagnostics retain the decoder window pointers. -/
theorem windowFrameM_fast_badData (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : WindowFrameM r owner (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  repeat' first
    | with_reducible exact windowFrameM_strLit r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_stZ r owner _ _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_bind ?_ (fun _ => ?_)

/-- Successful actual fast copyMatch execution preserves decoder window pointers. -/
theorem windowFrameM_fast_copyMatch (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves decoder window pointers. -/
theorem windowFrameM_fast_dodist (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves decoder window pointers. -/
theorem windowFrameM_fast_dolen (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_fast_dodist r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves decoder window pointers. -/
theorem windowFrameM_fast_body (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_fast_dodist r owner _ root _
    | with_reducible exact windowFrameM_fast_dolen r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves decoder window pointers, through its actual record writes, on every successful run. -/
theorem windowFrameM_inflate_fast (r : ZStreamRef) (owner : InflateStatePtr) (start : UInt32) :
    WindowFrameM r owner (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact windowFrameM_fast_body r owner _ rfl _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_castI r owner _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible exact windowFrameM_stZ r owner _ _
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
