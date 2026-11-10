import ZlibF.Proof.«inflate.c.output-total-tables»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem outputTotalFrameM_fast_shl32 (r : ZStreamRef) (value shift : UInt32) : OutputTotalFrameM r (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_fast_shl64 (r : ZStreamRef) (value shift : UInt64) : OutputTotalFrameM r (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_fast_shr64 (r : ZStreamRef) (value shift : UInt64) : OutputTotalFrameM r (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_fast_chk64 (r : ZStreamRef) (value : Int) : OutputTotalFrameM r (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_fast_subn (r : ZStreamRef) (pointer : BPtr) (count : UInt32) : OutputTotalFrameM r (Zlib.Inffast.subn pointer count) :=
  outputTotalFrameM_ptr_add r _ _

theorem outputTotalFrameM_fast_pull (r : ZStreamRef) (state : Zlib.Inffast.L) : OutputTotalFrameM r (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact outputTotalFrameM_bind (outputTotalFrameM_ptr_load r _) (fun _ =>
    outputTotalFrameM_bind (outputTotalFrameM_ptr_add r _ _) (fun _ =>
      outputTotalFrameM_bind (outputTotalFrameM_fast_shl64 r _ _) (fun _ => outputTotalFrameM_pure r _)))

theorem outputTotalFrameM_fast_copy1 (r : ZStreamRef) (state : Zlib.Inffast.L) : OutputTotalFrameM r (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact outputTotalFrameM_bind (outputTotalFrameM_ptr_load r _) (fun _ =>
    outputTotalFrameM_bind (outputTotalFrameM_ptr_add r _ _) (fun _ =>
      outputTotalFrameM_bind (outputTotalFrameM_store8 r _ _) (fun _ =>
        outputTotalFrameM_bind (outputTotalFrameM_ptr_add r _ _) (fun _ => outputTotalFrameM_pure r _))))

theorem outputTotalFrameM_fast_copyOp (r : ZStreamRef) (state : Zlib.Inffast.L) : OutputTotalFrameM r (Zlib.Inffast.copyOp state) :=
  outputTotalFrameM_cdoWhile (outputTotalFrameM_fast_copy1 r) (fun _ => outputTotalFrameM_pure r _) state

/-- Actual fast-decoder diagnostics retain the caller's output total. -/
theorem outputTotalFrameM_fast_badData (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : OutputTotalFrameM r (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  refine outputTotalFrameM_bind (outputTotalFrameM_strLit r _) (fun pointer => ?_)
  refine outputTotalFrameM_ldZ_update r (fun z => { z with msg := pointer }) _ (fun _ => rfl) (fun _ => ?_)
  exact outputTotalFrameM_bind (outputTotalFrameM_ldS r _) (fun _ => outputTotalFrameM_stS r _ _)

/-- Successful actual fast copyMatch execution preserves the public output total. -/
theorem outputTotalFrameM_fast_copyMatch (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OutputTotalFrameM r (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact outputTotalFrameM_fast_badData r _ root _
    | with_reducible exact outputTotalFrameM_fast_copyOp r _
    | with_reducible exact outputTotalFrameM_fast_copy1 r _
    | with_reducible exact outputTotalFrameM_fast_pull r _
    | with_reducible exact outputTotalFrameM_fast_subn r _ _
    | with_reducible exact outputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact outputTotalFrameM_fast_shl64 r _ _
    | with_reducible exact outputTotalFrameM_fast_shr64 r _ _
    | with_reducible exact outputTotalFrameM_fast_chk64 r _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_stS r _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_ptr_diff r _ _
    | with_reducible exact outputTotalFrameM_ptr_lt r _ _
    | with_reducible exact outputTotalFrameM_pure r _
    | with_reducible exact outputTotalFrameM_ub r _
    | with_reducible (refine outputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputTotalFrameM_ite
    | with_reducible (refine outputTotalFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves the public output total. -/
theorem outputTotalFrameM_fast_dodist (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OutputTotalFrameM r (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact outputTotalFrameM_fast_badData r _ root _
    | with_reducible exact outputTotalFrameM_fast_copyOp r _
    | with_reducible exact outputTotalFrameM_fast_copy1 r _
    | with_reducible exact outputTotalFrameM_fast_pull r _
    | with_reducible exact outputTotalFrameM_fast_subn r _ _
    | with_reducible exact outputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact outputTotalFrameM_fast_shl64 r _ _
    | with_reducible exact outputTotalFrameM_fast_shr64 r _ _
    | with_reducible exact outputTotalFrameM_fast_chk64 r _
    | with_reducible exact outputTotalFrameM_fast_copyMatch r _ root _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_stS r _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_ptr_diff r _ _
    | with_reducible exact outputTotalFrameM_ptr_lt r _ _
    | with_reducible exact outputTotalFrameM_pure r _
    | with_reducible exact outputTotalFrameM_ub r _
    | with_reducible (refine outputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputTotalFrameM_ite
    | with_reducible (refine outputTotalFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves the public output total. -/
theorem outputTotalFrameM_fast_dolen (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OutputTotalFrameM r (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact outputTotalFrameM_fast_badData r _ root _
    | with_reducible exact outputTotalFrameM_fast_copyOp r _
    | with_reducible exact outputTotalFrameM_fast_copy1 r _
    | with_reducible exact outputTotalFrameM_fast_pull r _
    | with_reducible exact outputTotalFrameM_fast_subn r _ _
    | with_reducible exact outputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact outputTotalFrameM_fast_shl64 r _ _
    | with_reducible exact outputTotalFrameM_fast_shr64 r _ _
    | with_reducible exact outputTotalFrameM_fast_chk64 r _
    | with_reducible exact outputTotalFrameM_fast_copyMatch r _ root _
    | with_reducible exact outputTotalFrameM_fast_dodist r _ root _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_stS r _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_ptr_diff r _ _
    | with_reducible exact outputTotalFrameM_ptr_lt r _ _
    | with_reducible exact outputTotalFrameM_pure r _
    | with_reducible exact outputTotalFrameM_ub r _
    | with_reducible (refine outputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputTotalFrameM_ite
    | with_reducible (refine outputTotalFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves the public output total. -/
theorem outputTotalFrameM_fast_body (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OutputTotalFrameM r (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact outputTotalFrameM_fast_badData r _ root _
    | with_reducible exact outputTotalFrameM_fast_copyOp r _
    | with_reducible exact outputTotalFrameM_fast_copy1 r _
    | with_reducible exact outputTotalFrameM_fast_pull r _
    | with_reducible exact outputTotalFrameM_fast_subn r _ _
    | with_reducible exact outputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact outputTotalFrameM_fast_shl64 r _ _
    | with_reducible exact outputTotalFrameM_fast_shr64 r _ _
    | with_reducible exact outputTotalFrameM_fast_chk64 r _
    | with_reducible exact outputTotalFrameM_fast_copyMatch r _ root _
    | with_reducible exact outputTotalFrameM_fast_dodist r _ root _
    | with_reducible exact outputTotalFrameM_fast_dolen r _ root _
    | with_reducible exact outputTotalFrameM_store8 r _ _
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_stS r _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_ptr_diff r _ _
    | with_reducible exact outputTotalFrameM_ptr_lt r _ _
    | with_reducible exact outputTotalFrameM_pure r _
    | with_reducible exact outputTotalFrameM_ub r _
    | with_reducible (refine outputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputTotalFrameM_ite
    | with_reducible (refine outputTotalFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves the caller's public output total on every successful run. No raw-buffer or callee-safety contract is assumed by this frame. -/
theorem outputTotalFrameM_inflate_fast (r : ZStreamRef) (start : UInt32) :
    OutputTotalFrameM r (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact outputTotalFrameM_fast_body r _ rfl _
    | with_reducible exact outputTotalFrameM_fast_subn r _ _
    | with_reducible exact outputTotalFrameM_fast_shl32 r _ _
    | with_reducible exact outputTotalFrameM_fast_chk64 r _
    | with_reducible exact outputTotalFrameM_ldZ r _
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_stS r _ _
    | with_reducible exact outputTotalFrameM_castI r _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_ptr_diff r _ _
    | with_reducible exact outputTotalFrameM_ptr_lt r _ _
    | with_reducible exact outputTotalFrameM_pure r _
    | with_reducible exact outputTotalFrameM_ub r _
    | with_reducible (refine outputTotalFrameM_ldZ_update r _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine outputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputTotalFrameM_ite
    | with_reducible (refine outputTotalFrameM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
