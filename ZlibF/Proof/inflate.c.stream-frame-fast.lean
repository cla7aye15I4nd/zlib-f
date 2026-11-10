import ZlibF.Proof.«inflate.c.stream-frame-tables»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem streamFrameM_fast_shl32 (r : ZStreamRef) (value shift : UInt32) : StreamFrameM r (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_fast_shl64 (r : ZStreamRef) (value shift : UInt64) : StreamFrameM r (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_fast_shr64 (r : ZStreamRef) (value shift : UInt64) : StreamFrameM r (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_fast_chk64 (r : ZStreamRef) (value : Int) : StreamFrameM r (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_fast_subn (r : ZStreamRef) (pointer : BPtr) (count : UInt32) : StreamFrameM r (Zlib.Inffast.subn pointer count) :=
  streamFrameM_ptr_add r _ _

theorem streamFrameM_fast_pull (r : ZStreamRef) (state : Zlib.Inffast.L) : StreamFrameM r (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact streamFrameM_bind (streamFrameM_ptr_load r _) (fun _ =>
    streamFrameM_bind (streamFrameM_ptr_add r _ _) (fun _ =>
      streamFrameM_bind (streamFrameM_fast_shl64 r _ _) (fun _ => streamFrameM_pure r _)))

theorem streamFrameM_fast_copy1 (r : ZStreamRef) (state : Zlib.Inffast.L) : StreamFrameM r (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact streamFrameM_bind (streamFrameM_ptr_load r _) (fun _ =>
    streamFrameM_bind (streamFrameM_ptr_add r _ _) (fun _ =>
      streamFrameM_bind (streamFrameM_store8 r _ _) (fun _ =>
        streamFrameM_bind (streamFrameM_ptr_add r _ _) (fun _ => streamFrameM_pure r _))))

theorem streamFrameM_fast_copyOp (r : ZStreamRef) (state : Zlib.Inffast.L) : StreamFrameM r (Zlib.Inffast.copyOp state) :=
  streamFrameM_cdoWhile (streamFrameM_fast_copy1 r) (fun _ => streamFrameM_pure r _) state

/-- Actual fast-decoder diagnostics retain the caller's fixed root fields. -/
theorem streamFrameM_fast_badData (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : StreamFrameM r (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  refine streamFrameM_bind (streamFrameM_strLit r _) (fun pointer => ?_)
  refine streamFrameM_ldZ_update r (fun z => { z with msg := pointer }) _ (fun _ => rfl) (fun _ => ?_)
  exact streamFrameM_bind (streamFrameM_ldS r _) (fun _ => streamFrameM_stS r _ _)

/-- Successful actual fast copyMatch execution preserves fixed stream fields. -/
theorem streamFrameM_fast_copyMatch (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    StreamFrameM r (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact streamFrameM_fast_badData r _ root _
    | with_reducible exact streamFrameM_fast_copyOp r _
    | with_reducible exact streamFrameM_fast_copy1 r _
    | with_reducible exact streamFrameM_fast_pull r _
    | with_reducible exact streamFrameM_fast_subn r _ _
    | with_reducible exact streamFrameM_fast_shl32 r _ _
    | with_reducible exact streamFrameM_fast_shl64 r _ _
    | with_reducible exact streamFrameM_fast_shr64 r _ _
    | with_reducible exact streamFrameM_fast_chk64 r _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_stS r _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_ptr_diff r _ _
    | with_reducible exact streamFrameM_ptr_lt r _ _
    | with_reducible exact streamFrameM_pure r _
    | with_reducible exact streamFrameM_ub r _
    | with_reducible (refine streamFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine streamFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply streamFrameM_ite
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves fixed stream fields. -/
theorem streamFrameM_fast_dodist (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    StreamFrameM r (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact streamFrameM_fast_badData r _ root _
    | with_reducible exact streamFrameM_fast_copyOp r _
    | with_reducible exact streamFrameM_fast_copy1 r _
    | with_reducible exact streamFrameM_fast_pull r _
    | with_reducible exact streamFrameM_fast_subn r _ _
    | with_reducible exact streamFrameM_fast_shl32 r _ _
    | with_reducible exact streamFrameM_fast_shl64 r _ _
    | with_reducible exact streamFrameM_fast_shr64 r _ _
    | with_reducible exact streamFrameM_fast_chk64 r _
    | with_reducible exact streamFrameM_fast_copyMatch r _ root _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_stS r _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_ptr_diff r _ _
    | with_reducible exact streamFrameM_ptr_lt r _ _
    | with_reducible exact streamFrameM_pure r _
    | with_reducible exact streamFrameM_ub r _
    | with_reducible (refine streamFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine streamFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply streamFrameM_ite
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves fixed stream fields. -/
theorem streamFrameM_fast_dolen (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    StreamFrameM r (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact streamFrameM_fast_badData r _ root _
    | with_reducible exact streamFrameM_fast_copyOp r _
    | with_reducible exact streamFrameM_fast_copy1 r _
    | with_reducible exact streamFrameM_fast_pull r _
    | with_reducible exact streamFrameM_fast_subn r _ _
    | with_reducible exact streamFrameM_fast_shl32 r _ _
    | with_reducible exact streamFrameM_fast_shl64 r _ _
    | with_reducible exact streamFrameM_fast_shr64 r _ _
    | with_reducible exact streamFrameM_fast_chk64 r _
    | with_reducible exact streamFrameM_fast_copyMatch r _ root _
    | with_reducible exact streamFrameM_fast_dodist r _ root _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_stS r _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_ptr_diff r _ _
    | with_reducible exact streamFrameM_ptr_lt r _ _
    | with_reducible exact streamFrameM_pure r _
    | with_reducible exact streamFrameM_ub r _
    | with_reducible (refine streamFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine streamFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply streamFrameM_ite
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves fixed stream fields. -/
theorem streamFrameM_fast_body (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    StreamFrameM r (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact streamFrameM_fast_badData r _ root _
    | with_reducible exact streamFrameM_fast_copyOp r _
    | with_reducible exact streamFrameM_fast_copy1 r _
    | with_reducible exact streamFrameM_fast_pull r _
    | with_reducible exact streamFrameM_fast_subn r _ _
    | with_reducible exact streamFrameM_fast_shl32 r _ _
    | with_reducible exact streamFrameM_fast_shl64 r _ _
    | with_reducible exact streamFrameM_fast_shr64 r _ _
    | with_reducible exact streamFrameM_fast_chk64 r _
    | with_reducible exact streamFrameM_fast_copyMatch r _ root _
    | with_reducible exact streamFrameM_fast_dodist r _ root _
    | with_reducible exact streamFrameM_fast_dolen r _ root _
    | with_reducible exact streamFrameM_store8 r _ _
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_stS r _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_ptr_diff r _ _
    | with_reducible exact streamFrameM_ptr_lt r _ _
    | with_reducible exact streamFrameM_pure r _
    | with_reducible exact streamFrameM_ub r _
    | with_reducible (refine streamFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine streamFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply streamFrameM_ite
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves the caller's state root,
allocator functions, opaque argument and reserved field on every successful
run. No raw-buffer or callee-safety contract is assumed by this frame. -/
theorem streamFrameM_inflate_fast (r : ZStreamRef) (start : UInt32) :
    StreamFrameM r (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact streamFrameM_fast_body r _ rfl _
    | with_reducible exact streamFrameM_fast_subn r _ _
    | with_reducible exact streamFrameM_fast_shl32 r _ _
    | with_reducible exact streamFrameM_fast_chk64 r _
    | with_reducible exact streamFrameM_ldZ r _
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_stS r _ _
    | with_reducible exact streamFrameM_castI r _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_ptr_diff r _ _
    | with_reducible exact streamFrameM_ptr_lt r _ _
    | with_reducible exact streamFrameM_pure r _
    | with_reducible exact streamFrameM_ub r _
    | with_reducible (refine streamFrameM_ldZ_update r _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine streamFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply streamFrameM_ite
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
