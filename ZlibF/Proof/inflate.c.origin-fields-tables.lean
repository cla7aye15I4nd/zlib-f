import ZlibF.Proof.«inflate.c.origin-fields-updates»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem originFieldFrameM_table_chk32 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : OriginFieldFrameM r owner (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_table_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : OriginFieldFrameM r owner (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_table_shr32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : OriginFieldFrameM r owner (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_table_shl1i32 (r : ZStreamRef) (owner : InflateStatePtr) (shift : UInt32) : OriginFieldFrameM r owner (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_table_geta (r : ZStreamRef) (owner : InflateStatePtr) (array : Array UInt16) (index : Nat) : OriginFieldFrameM r owner (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact originFieldFrameM_pure r owner _
  · exact originFieldFrameM_ub r owner _

theorem originFieldFrameM_table_seta (r : ZStreamRef) (owner : InflateStatePtr) (array : Array UInt16) (index : Nat) (value : UInt16) :
    OriginFieldFrameM r owner (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_table_storeCode (r : ZStreamRef) (owner : InflateStatePtr) (pointer : CodePtr) (index : Nat) (value : Code) :
    OriginFieldFrameM r owner (Zlib.Inftrees.storeCode pointer index value) :=
  originFieldFrameM_bind (originFieldFrameM_ptr_add r owner _ _) (fun next => originFieldFrameM_storeCode r owner next value)

/-- Every successful actual constructor step preserves every decoder origin field. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem originFieldFrameM_table_buildStep (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    OriginFieldFrameM r owner (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact originFieldFrameM_table_chk32 r owner _
    | with_reducible exact originFieldFrameM_table_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_table_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_table_shl1i32 r owner _
    | with_reducible exact originFieldFrameM_table_geta r owner _ _
    | with_reducible exact originFieldFrameM_table_seta r owner _ _ _
    | with_reducible exact originFieldFrameM_table_storeCode r owner _ _ _
    | with_reducible exact originFieldFrameM_store16 r owner _ _
    | with_reducible exact originFieldFrameM_storeCode r owner _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves fixed stream
fields across all alphabets, partial writes and rejection returns. -/
theorem originFieldFrameM_inflate_table (r : ZStreamRef) (owner : InflateStatePtr) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    OriginFieldFrameM r owner (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact originFieldFrameM_table_buildStep r owner _ _
    | with_reducible exact originFieldFrameM_table_chk32 r owner _
    | with_reducible exact originFieldFrameM_table_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_table_shr32 r owner _ _
    | with_reducible exact originFieldFrameM_table_shl1i32 r owner _
    | with_reducible exact originFieldFrameM_table_geta r owner _ _
    | with_reducible exact originFieldFrameM_table_seta r owner _ _ _
    | with_reducible exact originFieldFrameM_table_storeCode r owner _ _ _
    | with_reducible exact originFieldFrameM_store16 r owner _ _
    | with_reducible exact originFieldFrameM_storeCode r owner _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs
