import ZlibF.Proof.«inflate.c.output-counter-frame-tables»

namespace Zlib.Inflate.Proofs.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem outputCounterM_fast_shl32 (r : ZStreamRef) (value shift : UInt32) : OutputCounterM r (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_fast_shl64 (r : ZStreamRef) (value shift : UInt64) : OutputCounterM r (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_fast_shr64 (r : ZStreamRef) (value shift : UInt64) : OutputCounterM r (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_fast_chk64 (r : ZStreamRef) (value : Int) : OutputCounterM r (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_fast_subn (r : ZStreamRef) (pointer : BPtr) (count : UInt32) : OutputCounterM r (Zlib.Inffast.subn pointer count) :=
  outputCounterM_ptr_add r _ _

theorem outputCounterM_fast_pull (r : ZStreamRef) (state : Zlib.Inffast.L) : OutputCounterM r (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact outputCounterM_bind (outputCounterM_ptr_load r _) (fun _ =>
    outputCounterM_bind (outputCounterM_ptr_add r _ _) (fun _ =>
      outputCounterM_bind (outputCounterM_fast_shl64 r _ _) (fun _ => outputCounterM_pure r _)))

theorem outputCounterM_fast_copy1 (r : ZStreamRef) (state : Zlib.Inffast.L) : OutputCounterM r (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact outputCounterM_bind (outputCounterM_ptr_load r _) (fun _ =>
    outputCounterM_bind (outputCounterM_ptr_add r _ _) (fun _ =>
      outputCounterM_bind (outputCounterM_store8 r _ _) (fun _ =>
        outputCounterM_bind (outputCounterM_ptr_add r _ _) (fun _ => outputCounterM_pure r _))))

theorem outputCounterM_fast_copyOp (r : ZStreamRef) (state : Zlib.Inffast.L) : OutputCounterM r (Zlib.Inffast.copyOp state) :=
  outputCounterM_cdoWhile (outputCounterM_fast_copy1 r) (fun _ => outputCounterM_pure r _) state

theorem outputCounterM_fast_badData (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : OutputCounterM r (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  refine outputCounterM_bind (outputCounterM_strLit r _) (fun pointer => ?_)
  refine outputCounterM_ldZ_update r (fun z => { z with msg := pointer }) _ (fun _ => rfl) (fun _ => ?_)
  exact outputCounterM_bind (outputCounterM_ldS r _) (fun _ => outputCounterM_stS r _ _)

theorem outputCounterM_fast_copyMatch (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OutputCounterM r (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact outputCounterM_fast_badData r _ root _
    | with_reducible exact outputCounterM_fast_copyOp r _
    | with_reducible exact outputCounterM_fast_copy1 r _
    | with_reducible exact outputCounterM_fast_pull r _
    | with_reducible exact outputCounterM_fast_subn r _ _
    | with_reducible exact outputCounterM_fast_shl32 r _ _
    | with_reducible exact outputCounterM_fast_shl64 r _ _
    | with_reducible exact outputCounterM_fast_shr64 r _ _
    | with_reducible exact outputCounterM_fast_chk64 r _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_stS r _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_ptr_diff r _ _
    | with_reducible exact outputCounterM_ptr_lt r _ _
    | with_reducible exact outputCounterM_pure r _
    | with_reducible exact outputCounterM_ub r _
    | with_reducible (refine outputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputCounterM_ite
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

theorem outputCounterM_fast_dodist (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OutputCounterM r (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact outputCounterM_fast_badData r _ root _
    | with_reducible exact outputCounterM_fast_copyOp r _
    | with_reducible exact outputCounterM_fast_copy1 r _
    | with_reducible exact outputCounterM_fast_pull r _
    | with_reducible exact outputCounterM_fast_subn r _ _
    | with_reducible exact outputCounterM_fast_shl32 r _ _
    | with_reducible exact outputCounterM_fast_shl64 r _ _
    | with_reducible exact outputCounterM_fast_shr64 r _ _
    | with_reducible exact outputCounterM_fast_chk64 r _
    | with_reducible exact outputCounterM_fast_copyMatch r _ root _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_stS r _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_ptr_diff r _ _
    | with_reducible exact outputCounterM_ptr_lt r _ _
    | with_reducible exact outputCounterM_pure r _
    | with_reducible exact outputCounterM_ub r _
    | with_reducible (refine outputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputCounterM_ite
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

theorem outputCounterM_fast_dolen (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OutputCounterM r (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact outputCounterM_fast_badData r _ root _
    | with_reducible exact outputCounterM_fast_copyOp r _
    | with_reducible exact outputCounterM_fast_copy1 r _
    | with_reducible exact outputCounterM_fast_pull r _
    | with_reducible exact outputCounterM_fast_subn r _ _
    | with_reducible exact outputCounterM_fast_shl32 r _ _
    | with_reducible exact outputCounterM_fast_shl64 r _ _
    | with_reducible exact outputCounterM_fast_shr64 r _ _
    | with_reducible exact outputCounterM_fast_chk64 r _
    | with_reducible exact outputCounterM_fast_copyMatch r _ root _
    | with_reducible exact outputCounterM_fast_dodist r _ root _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_stS r _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_ptr_diff r _ _
    | with_reducible exact outputCounterM_ptr_lt r _ _
    | with_reducible exact outputCounterM_pure r _
    | with_reducible exact outputCounterM_ub r _
    | with_reducible (refine outputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputCounterM_ite
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

theorem outputCounterM_fast_body (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OutputCounterM r (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact outputCounterM_fast_badData r _ root _
    | with_reducible exact outputCounterM_fast_copyOp r _
    | with_reducible exact outputCounterM_fast_copy1 r _
    | with_reducible exact outputCounterM_fast_pull r _
    | with_reducible exact outputCounterM_fast_subn r _ _
    | with_reducible exact outputCounterM_fast_shl32 r _ _
    | with_reducible exact outputCounterM_fast_shl64 r _ _
    | with_reducible exact outputCounterM_fast_shr64 r _ _
    | with_reducible exact outputCounterM_fast_chk64 r _
    | with_reducible exact outputCounterM_fast_copyMatch r _ root _
    | with_reducible exact outputCounterM_fast_dodist r _ root _
    | with_reducible exact outputCounterM_fast_dolen r _ root _
    | with_reducible exact outputCounterM_store8 r _ _
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_stS r _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_ptr_diff r _ _
    | with_reducible exact outputCounterM_ptr_lt r _ _
    | with_reducible exact outputCounterM_pure r _
    | with_reducible exact outputCounterM_ub r _
    | with_reducible (refine outputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputCounterM_ite
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

theorem outputCounterM_inflate_fast (r : ZStreamRef) (start : UInt32) :
    OutputCounterM r (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact outputCounterM_fast_body r _ rfl _
    | with_reducible exact outputCounterM_fast_subn r _ _
    | with_reducible exact outputCounterM_fast_shl32 r _ _
    | with_reducible exact outputCounterM_fast_chk64 r _
    | with_reducible exact outputCounterM_ldZ r _
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_stS r _ _
    | with_reducible exact outputCounterM_castI r _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_ptr_diff r _ _
    | with_reducible exact outputCounterM_ptr_lt r _ _
    | with_reducible exact outputCounterM_pure r _
    | with_reducible exact outputCounterM_ub r _
    | with_reducible (refine outputCounterM_ldZ_update r _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine outputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputCounterM_ite
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs.OutputCounter
