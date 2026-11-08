import ZlibF.Proof.«inflate.c.input-counter-frame-tables»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputCounterM_fast_shl32 (r : ZStreamRef) (value shift : UInt32) : InputCounterM r (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_fast_shl64 (r : ZStreamRef) (value shift : UInt64) : InputCounterM r (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_fast_shr64 (r : ZStreamRef) (value shift : UInt64) : InputCounterM r (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_fast_chk64 (r : ZStreamRef) (value : Int) : InputCounterM r (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_fast_subn (r : ZStreamRef) (pointer : BPtr) (count : UInt32) : InputCounterM r (Zlib.Inffast.subn pointer count) :=
  inputCounterM_ptr_add r _ _

theorem inputCounterM_fast_pull (r : ZStreamRef) (state : Zlib.Inffast.L) : InputCounterM r (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact inputCounterM_bind (inputCounterM_ptr_load r _) (fun _ =>
    inputCounterM_bind (inputCounterM_ptr_add r _ _) (fun _ =>
      inputCounterM_bind (inputCounterM_fast_shl64 r _ _) (fun _ => inputCounterM_pure r _)))

theorem inputCounterM_fast_copy1 (r : ZStreamRef) (state : Zlib.Inffast.L) : InputCounterM r (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact inputCounterM_bind (inputCounterM_ptr_load r _) (fun _ =>
    inputCounterM_bind (inputCounterM_ptr_add r _ _) (fun _ =>
      inputCounterM_bind (inputCounterM_store8 r _ _) (fun _ =>
        inputCounterM_bind (inputCounterM_ptr_add r _ _) (fun _ => inputCounterM_pure r _))))

theorem inputCounterM_fast_copyOp (r : ZStreamRef) (state : Zlib.Inffast.L) : InputCounterM r (Zlib.Inffast.copyOp state) :=
  inputCounterM_cdoWhile (inputCounterM_fast_copy1 r) (fun _ => inputCounterM_pure r _) state

theorem inputCounterM_fast_badData (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : InputCounterM r (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  refine inputCounterM_bind (inputCounterM_strLit r _) (fun pointer => ?_)
  refine inputCounterM_ldZ_update r (fun z => { z with msg := pointer }) _ (fun _ => rfl) (fun _ => ?_)
  exact inputCounterM_bind (inputCounterM_ldS r _) (fun _ => inputCounterM_stS r _ _)

theorem inputCounterM_fast_copyMatch (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    InputCounterM r (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact inputCounterM_fast_badData r _ root _
    | with_reducible exact inputCounterM_fast_copyOp r _
    | with_reducible exact inputCounterM_fast_copy1 r _
    | with_reducible exact inputCounterM_fast_pull r _
    | with_reducible exact inputCounterM_fast_subn r _ _
    | with_reducible exact inputCounterM_fast_shl32 r _ _
    | with_reducible exact inputCounterM_fast_shl64 r _ _
    | with_reducible exact inputCounterM_fast_shr64 r _ _
    | with_reducible exact inputCounterM_fast_chk64 r _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_stS r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_ptr_diff r _ _
    | with_reducible exact inputCounterM_ptr_lt r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible exact inputCounterM_ub r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_fast_dodist (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    InputCounterM r (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact inputCounterM_fast_badData r _ root _
    | with_reducible exact inputCounterM_fast_copyOp r _
    | with_reducible exact inputCounterM_fast_copy1 r _
    | with_reducible exact inputCounterM_fast_pull r _
    | with_reducible exact inputCounterM_fast_subn r _ _
    | with_reducible exact inputCounterM_fast_shl32 r _ _
    | with_reducible exact inputCounterM_fast_shl64 r _ _
    | with_reducible exact inputCounterM_fast_shr64 r _ _
    | with_reducible exact inputCounterM_fast_chk64 r _
    | with_reducible exact inputCounterM_fast_copyMatch r _ root _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_stS r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_ptr_diff r _ _
    | with_reducible exact inputCounterM_ptr_lt r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible exact inputCounterM_ub r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_fast_dolen (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    InputCounterM r (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact inputCounterM_fast_badData r _ root _
    | with_reducible exact inputCounterM_fast_copyOp r _
    | with_reducible exact inputCounterM_fast_copy1 r _
    | with_reducible exact inputCounterM_fast_pull r _
    | with_reducible exact inputCounterM_fast_subn r _ _
    | with_reducible exact inputCounterM_fast_shl32 r _ _
    | with_reducible exact inputCounterM_fast_shl64 r _ _
    | with_reducible exact inputCounterM_fast_shr64 r _ _
    | with_reducible exact inputCounterM_fast_chk64 r _
    | with_reducible exact inputCounterM_fast_copyMatch r _ root _
    | with_reducible exact inputCounterM_fast_dodist r _ root _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_stS r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_ptr_diff r _ _
    | with_reducible exact inputCounterM_ptr_lt r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible exact inputCounterM_ub r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_fast_body (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    InputCounterM r (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact inputCounterM_fast_badData r _ root _
    | with_reducible exact inputCounterM_fast_copyOp r _
    | with_reducible exact inputCounterM_fast_copy1 r _
    | with_reducible exact inputCounterM_fast_pull r _
    | with_reducible exact inputCounterM_fast_subn r _ _
    | with_reducible exact inputCounterM_fast_shl32 r _ _
    | with_reducible exact inputCounterM_fast_shl64 r _ _
    | with_reducible exact inputCounterM_fast_shr64 r _ _
    | with_reducible exact inputCounterM_fast_chk64 r _
    | with_reducible exact inputCounterM_fast_copyMatch r _ root _
    | with_reducible exact inputCounterM_fast_dodist r _ root _
    | with_reducible exact inputCounterM_fast_dolen r _ root _
    | with_reducible exact inputCounterM_store8 r _ _
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_stS r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_ptr_diff r _ _
    | with_reducible exact inputCounterM_ptr_lt r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible exact inputCounterM_ub r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_inflate_fast (r : ZStreamRef) (start : UInt32) :
    InputCounterM r (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact inputCounterM_fast_body r _ rfl _
    | with_reducible exact inputCounterM_fast_subn r _ _
    | with_reducible exact inputCounterM_fast_shl32 r _ _
    | with_reducible exact inputCounterM_fast_chk64 r _
    | with_reducible exact inputCounterM_ldZ r _
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_stS r _ _
    | with_reducible exact inputCounterM_castI r _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_ptr_diff r _ _
    | with_reducible exact inputCounterM_ptr_lt r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible exact inputCounterM_ub r _
    | with_reducible (refine inputCounterM_ldZ_update r _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine inputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs.InputCounter
