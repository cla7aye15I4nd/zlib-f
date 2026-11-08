import ZlibF.Proof.«inflate.c.window-pointer-updates»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem windowFrameM_table_chk32 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shr32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shl1i32 (r : ZStreamRef) (owner : InflateStatePtr) (shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_geta (r : ZStreamRef) (owner : InflateStatePtr) (array : Array UInt16) (index : Nat) : WindowFrameM r owner (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact windowFrameM_pure r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_table_seta (r : ZStreamRef) (owner : InflateStatePtr) (array : Array UInt16) (index : Nat) (value : UInt16) :
    WindowFrameM r owner (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_storeCode (r : ZStreamRef) (owner : InflateStatePtr) (pointer : CodePtr) (index : Nat) (value : Code) :
    WindowFrameM r owner (Zlib.Inftrees.storeCode pointer index value) :=
  windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun next => windowFrameM_storeCode r owner next value)

/-- Every successful actual constructor step preserves every decoder window pointer. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem windowFrameM_table_buildStep (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    WindowFrameM r owner (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact windowFrameM_table_chk32 r owner _
    | with_reducible exact windowFrameM_table_shl32 r owner _ _
    | with_reducible exact windowFrameM_table_shr32 r owner _ _
    | with_reducible exact windowFrameM_table_shl1i32 r owner _
    | with_reducible exact windowFrameM_table_geta r owner _ _
    | with_reducible exact windowFrameM_table_seta r owner _ _ _
    | with_reducible exact windowFrameM_table_storeCode r owner _ _ _
    | with_reducible exact windowFrameM_store16 r owner _ _
    | with_reducible exact windowFrameM_storeCode r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves fixed stream
fields across all alphabets, partial writes and rejection returns. -/
theorem windowFrameM_inflate_table (r : ZStreamRef) (owner : InflateStatePtr) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    WindowFrameM r owner (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact windowFrameM_table_buildStep r owner _ _
    | with_reducible exact windowFrameM_table_chk32 r owner _
    | with_reducible exact windowFrameM_table_shl32 r owner _ _
    | with_reducible exact windowFrameM_table_shr32 r owner _ _
    | with_reducible exact windowFrameM_table_shl1i32 r owner _
    | with_reducible exact windowFrameM_table_geta r owner _ _
    | with_reducible exact windowFrameM_table_seta r owner _ _ _
    | with_reducible exact windowFrameM_table_storeCode r owner _ _ _
    | with_reducible exact windowFrameM_store16 r owner _ _
    | with_reducible exact windowFrameM_storeCode r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs
