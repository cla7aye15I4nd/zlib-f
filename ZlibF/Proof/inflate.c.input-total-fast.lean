import ZlibF.Proof.«inflate.c.input-total-tables»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputTotalFrameM_fast_shl32 (r : ZStreamRef) (value shift : UInt32) : InputTotalFrameM r (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_fast_shl64 (r : ZStreamRef) (value shift : UInt64) : InputTotalFrameM r (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_fast_shr64 (r : ZStreamRef) (value shift : UInt64) : InputTotalFrameM r (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_fast_chk64 (r : ZStreamRef) (value : Int) : InputTotalFrameM r (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_fast_subn (r : ZStreamRef) (pointer : BPtr) (count : UInt32) : InputTotalFrameM r (Zlib.Inffast.subn pointer count) :=
  inputTotalFrameM_ptr_add r _ _

theorem inputTotalFrameM_fast_pull (r : ZStreamRef) (state : Zlib.Inffast.L) : InputTotalFrameM r (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact inputTotalFrameM_bind (inputTotalFrameM_ptr_load r _) (fun _ =>
    inputTotalFrameM_bind (inputTotalFrameM_ptr_add r _ _) (fun _ =>
      inputTotalFrameM_bind (inputTotalFrameM_fast_shl64 r _ _) (fun _ => inputTotalFrameM_pure r _)))

theorem inputTotalFrameM_fast_copy1 (r : ZStreamRef) (state : Zlib.Inffast.L) : InputTotalFrameM r (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact inputTotalFrameM_bind (inputTotalFrameM_ptr_load r _) (fun _ =>
    inputTotalFrameM_bind (inputTotalFrameM_ptr_add r _ _) (fun _ =>
      inputTotalFrameM_bind (inputTotalFrameM_store8 r _ _) (fun _ =>
        inputTotalFrameM_bind (inputTotalFrameM_ptr_add r _ _) (fun _ => inputTotalFrameM_pure r _))))

theorem inputTotalFrameM_fast_copyOp (r : ZStreamRef) (state : Zlib.Inffast.L) : InputTotalFrameM r (Zlib.Inffast.copyOp state) :=
  inputTotalFrameM_cdoWhile (inputTotalFrameM_fast_copy1 r) (fun _ => inputTotalFrameM_pure r _) state

/-- Actual fast-decoder diagnostics retain the caller's fixed root fields. -/
theorem inputTotalFrameM_fast_badData (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : InputTotalFrameM r (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  refine inputTotalFrameM_bind (inputTotalFrameM_strLit r _) (fun pointer => ?_)
  refine inputTotalFrameM_ldZ_update r (fun z => { z with msg := pointer }) _ (fun _ => rfl) (fun _ => ?_)
  exact inputTotalFrameM_bind (inputTotalFrameM_ldS r _) (fun _ => inputTotalFrameM_stS r _ _)

/-- Successful actual fast copyMatch execution preserves the public input total. -/
theorem inputTotalFrameM_fast_copyMatch (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    InputTotalFrameM r (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact inputTotalFrameM_fast_badData r _ root _
    | with_reducible exact inputTotalFrameM_fast_copyOp r _
    | with_reducible exact inputTotalFrameM_fast_copy1 r _
    | with_reducible exact inputTotalFrameM_fast_pull r _
    | with_reducible exact inputTotalFrameM_fast_subn r _ _
    | with_reducible exact inputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact inputTotalFrameM_fast_shl64 r _ _
    | with_reducible exact inputTotalFrameM_fast_shr64 r _ _
    | with_reducible exact inputTotalFrameM_fast_chk64 r _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_stS r _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_ptr_diff r _ _
    | with_reducible exact inputTotalFrameM_ptr_lt r _ _
    | with_reducible exact inputTotalFrameM_pure r _
    | with_reducible exact inputTotalFrameM_ub r _
    | with_reducible (refine inputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputTotalFrameM_ite
    | with_reducible (refine inputTotalFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves the public input total. -/
theorem inputTotalFrameM_fast_dodist (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    InputTotalFrameM r (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact inputTotalFrameM_fast_badData r _ root _
    | with_reducible exact inputTotalFrameM_fast_copyOp r _
    | with_reducible exact inputTotalFrameM_fast_copy1 r _
    | with_reducible exact inputTotalFrameM_fast_pull r _
    | with_reducible exact inputTotalFrameM_fast_subn r _ _
    | with_reducible exact inputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact inputTotalFrameM_fast_shl64 r _ _
    | with_reducible exact inputTotalFrameM_fast_shr64 r _ _
    | with_reducible exact inputTotalFrameM_fast_chk64 r _
    | with_reducible exact inputTotalFrameM_fast_copyMatch r _ root _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_stS r _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_ptr_diff r _ _
    | with_reducible exact inputTotalFrameM_ptr_lt r _ _
    | with_reducible exact inputTotalFrameM_pure r _
    | with_reducible exact inputTotalFrameM_ub r _
    | with_reducible (refine inputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputTotalFrameM_ite
    | with_reducible (refine inputTotalFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves the public input total. -/
theorem inputTotalFrameM_fast_dolen (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    InputTotalFrameM r (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact inputTotalFrameM_fast_badData r _ root _
    | with_reducible exact inputTotalFrameM_fast_copyOp r _
    | with_reducible exact inputTotalFrameM_fast_copy1 r _
    | with_reducible exact inputTotalFrameM_fast_pull r _
    | with_reducible exact inputTotalFrameM_fast_subn r _ _
    | with_reducible exact inputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact inputTotalFrameM_fast_shl64 r _ _
    | with_reducible exact inputTotalFrameM_fast_shr64 r _ _
    | with_reducible exact inputTotalFrameM_fast_chk64 r _
    | with_reducible exact inputTotalFrameM_fast_copyMatch r _ root _
    | with_reducible exact inputTotalFrameM_fast_dodist r _ root _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_stS r _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_ptr_diff r _ _
    | with_reducible exact inputTotalFrameM_ptr_lt r _ _
    | with_reducible exact inputTotalFrameM_pure r _
    | with_reducible exact inputTotalFrameM_ub r _
    | with_reducible (refine inputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputTotalFrameM_ite
    | with_reducible (refine inputTotalFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves the public input total. -/
theorem inputTotalFrameM_fast_body (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    InputTotalFrameM r (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact inputTotalFrameM_fast_badData r _ root _
    | with_reducible exact inputTotalFrameM_fast_copyOp r _
    | with_reducible exact inputTotalFrameM_fast_copy1 r _
    | with_reducible exact inputTotalFrameM_fast_pull r _
    | with_reducible exact inputTotalFrameM_fast_subn r _ _
    | with_reducible exact inputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact inputTotalFrameM_fast_shl64 r _ _
    | with_reducible exact inputTotalFrameM_fast_shr64 r _ _
    | with_reducible exact inputTotalFrameM_fast_chk64 r _
    | with_reducible exact inputTotalFrameM_fast_copyMatch r _ root _
    | with_reducible exact inputTotalFrameM_fast_dodist r _ root _
    | with_reducible exact inputTotalFrameM_fast_dolen r _ root _
    | with_reducible exact inputTotalFrameM_store8 r _ _
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_stS r _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_ptr_diff r _ _
    | with_reducible exact inputTotalFrameM_ptr_lt r _ _
    | with_reducible exact inputTotalFrameM_pure r _
    | with_reducible exact inputTotalFrameM_ub r _
    | with_reducible (refine inputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputTotalFrameM_ite
    | with_reducible (refine inputTotalFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves the caller's public input total on every successful run. No raw-buffer or callee-safety contract is assumed by this frame. -/
theorem inputTotalFrameM_inflate_fast (r : ZStreamRef) (start : UInt32) :
    InputTotalFrameM r (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact inputTotalFrameM_fast_body r _ rfl _
    | with_reducible exact inputTotalFrameM_fast_subn r _ _
    | with_reducible exact inputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact inputTotalFrameM_fast_chk64 r _
    | with_reducible exact inputTotalFrameM_ldZ r _
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_stS r _ _
    | with_reducible exact inputTotalFrameM_castI r _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_ptr_diff r _ _
    | with_reducible exact inputTotalFrameM_ptr_lt r _ _
    | with_reducible exact inputTotalFrameM_pure r _
    | with_reducible exact inputTotalFrameM_ub r _
    | with_reducible (refine inputTotalFrameM_ldZ_update r _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine inputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputTotalFrameM_ite
    | with_reducible (refine inputTotalFrameM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
