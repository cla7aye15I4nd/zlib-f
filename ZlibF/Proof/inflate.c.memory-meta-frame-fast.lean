import ZlibF.Proof.«inflate.c.memory-meta-frame-tables»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem memoryMetaFrameM_fast_shl32 (r : ZStreamRef) (value shift : UInt32) : MemoryMetaFrameM r (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_fast_shl64 (r : ZStreamRef) (value shift : UInt64) : MemoryMetaFrameM r (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_fast_shr64 (r : ZStreamRef) (value shift : UInt64) : MemoryMetaFrameM r (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_fast_chk64 (r : ZStreamRef) (value : Int) : MemoryMetaFrameM r (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_fast_subn (r : ZStreamRef) (pointer : BPtr) (count : UInt32) : MemoryMetaFrameM r (Zlib.Inffast.subn pointer count) :=
  memoryMetaFrameM_ptr_add r _ _

theorem memoryMetaFrameM_fast_pull (r : ZStreamRef) (state : Zlib.Inffast.L) : MemoryMetaFrameM r (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact memoryMetaFrameM_bind (memoryMetaFrameM_ptr_load r _) (fun _ =>
    memoryMetaFrameM_bind (memoryMetaFrameM_ptr_add r _ _) (fun _ =>
      memoryMetaFrameM_bind (memoryMetaFrameM_fast_shl64 r _ _) (fun _ => memoryMetaFrameM_pure r _)))

theorem memoryMetaFrameM_fast_copy1 (r : ZStreamRef) (state : Zlib.Inffast.L) : MemoryMetaFrameM r (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact memoryMetaFrameM_bind (memoryMetaFrameM_ptr_load r _) (fun _ =>
    memoryMetaFrameM_bind (memoryMetaFrameM_ptr_add r _ _) (fun _ =>
      memoryMetaFrameM_bind (memoryMetaFrameM_store8 r _ _) (fun _ =>
        memoryMetaFrameM_bind (memoryMetaFrameM_ptr_add r _ _) (fun _ => memoryMetaFrameM_pure r _))))

theorem memoryMetaFrameM_fast_copyOp (r : ZStreamRef) (state : Zlib.Inffast.L) : MemoryMetaFrameM r (Zlib.Inffast.copyOp state) :=
  memoryMetaFrameM_cdoWhile (memoryMetaFrameM_fast_copy1 r) (fun _ => memoryMetaFrameM_pure r _) state

/-- Actual fast-decoder diagnostics retain the allocation metadata. -/
theorem memoryMetaFrameM_fast_badData (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : MemoryMetaFrameM r (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  refine memoryMetaFrameM_bind (memoryMetaFrameM_strLit r _) (fun pointer => ?_)
  refine memoryMetaFrameM_ldZ_update r (fun z => { z with msg := pointer }) _ (fun _ => rfl) (fun _ => ?_)
  exact memoryMetaFrameM_bind (memoryMetaFrameM_ldS r _) (fun _ => memoryMetaFrameM_stS r _ _)

/-- Successful actual fast copyMatch execution preserves allocation metadata. -/
theorem memoryMetaFrameM_fast_copyMatch (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    MemoryMetaFrameM r (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact memoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact memoryMetaFrameM_fast_copyOp r _
    | with_reducible exact memoryMetaFrameM_fast_copy1 r _
    | with_reducible exact memoryMetaFrameM_fast_pull r _
    | with_reducible exact memoryMetaFrameM_fast_subn r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact memoryMetaFrameM_fast_chk64 r _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_stS r _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact memoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible exact memoryMetaFrameM_ub r _
    | with_reducible (refine memoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine memoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves allocation metadata. -/
theorem memoryMetaFrameM_fast_dodist (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    MemoryMetaFrameM r (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact memoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact memoryMetaFrameM_fast_copyOp r _
    | with_reducible exact memoryMetaFrameM_fast_copy1 r _
    | with_reducible exact memoryMetaFrameM_fast_pull r _
    | with_reducible exact memoryMetaFrameM_fast_subn r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact memoryMetaFrameM_fast_chk64 r _
    | with_reducible exact memoryMetaFrameM_fast_copyMatch r _ root _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_stS r _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact memoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible exact memoryMetaFrameM_ub r _
    | with_reducible (refine memoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine memoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves allocation metadata. -/
theorem memoryMetaFrameM_fast_dolen (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    MemoryMetaFrameM r (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact memoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact memoryMetaFrameM_fast_copyOp r _
    | with_reducible exact memoryMetaFrameM_fast_copy1 r _
    | with_reducible exact memoryMetaFrameM_fast_pull r _
    | with_reducible exact memoryMetaFrameM_fast_subn r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact memoryMetaFrameM_fast_chk64 r _
    | with_reducible exact memoryMetaFrameM_fast_copyMatch r _ root _
    | with_reducible exact memoryMetaFrameM_fast_dodist r _ root _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_stS r _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact memoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible exact memoryMetaFrameM_ub r _
    | with_reducible (refine memoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine memoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves allocation metadata. -/
theorem memoryMetaFrameM_fast_body (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    MemoryMetaFrameM r (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact memoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact memoryMetaFrameM_fast_copyOp r _
    | with_reducible exact memoryMetaFrameM_fast_copy1 r _
    | with_reducible exact memoryMetaFrameM_fast_pull r _
    | with_reducible exact memoryMetaFrameM_fast_subn r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact memoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact memoryMetaFrameM_fast_chk64 r _
    | with_reducible exact memoryMetaFrameM_fast_copyMatch r _ root _
    | with_reducible exact memoryMetaFrameM_fast_dodist r _ root _
    | with_reducible exact memoryMetaFrameM_fast_dolen r _ root _
    | with_reducible exact memoryMetaFrameM_store8 r _ _
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_stS r _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact memoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible exact memoryMetaFrameM_ub r _
    | with_reducible (refine memoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine memoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves read-only flags and the
allocation frontier on every successful run. No raw-buffer or callee-safety
contract is assumed by this frame. -/
theorem memoryMetaFrameM_inflate_fast (r : ZStreamRef) (start : UInt32) :
    MemoryMetaFrameM r (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact memoryMetaFrameM_fast_body r _ rfl _
    | with_reducible exact memoryMetaFrameM_fast_subn r _ _
    | with_reducible exact memoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_fast_chk64 r _
    | with_reducible exact memoryMetaFrameM_ldZ r _
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_stS r _ _
    | with_reducible exact memoryMetaFrameM_castI r _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact memoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible exact memoryMetaFrameM_ub r _
    | with_reducible (refine memoryMetaFrameM_ldZ_update r _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine memoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
