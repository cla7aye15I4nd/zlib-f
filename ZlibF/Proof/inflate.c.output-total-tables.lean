import ZlibF.Proof.«inflate.c.output-total-checksums»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem outputTotalFrameM_table_chk32 (r : ZStreamRef) (value : Int) : OutputTotalFrameM r (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_table_shl32 (r : ZStreamRef) (value shift : UInt32) : OutputTotalFrameM r (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_table_shr32 (r : ZStreamRef) (value shift : UInt32) : OutputTotalFrameM r (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_table_shl1i32 (r : ZStreamRef) (shift : UInt32) : OutputTotalFrameM r (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_table_geta (r : ZStreamRef) (array : Array UInt16) (index : Nat) : OutputTotalFrameM r (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact outputTotalFrameM_pure r _
  · exact outputTotalFrameM_ub r _

theorem outputTotalFrameM_table_seta (r : ZStreamRef) (array : Array UInt16) (index : Nat) (value : UInt16) :
    OutputTotalFrameM r (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact outputTotalFrameM_ite (outputTotalFrameM_pure r _) (outputTotalFrameM_ub r _)

theorem outputTotalFrameM_table_storeCode (r : ZStreamRef) (pointer : CodePtr) (index : Nat) (value : Code) :
    OutputTotalFrameM r (Zlib.Inftrees.storeCode pointer index value) :=
  outputTotalFrameM_bind (outputTotalFrameM_ptr_add r _ _) (fun next => outputTotalFrameM_storeCode r next value)

/-- Actual fixed-table installation writes only private decoder fields. -/
theorem outputTotalFrameM_inflate_fixed (r : ZStreamRef) (pointer : InflateStatePtr) :
    OutputTotalFrameM r (Zlib.Inftrees.inflate_fixed pointer) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact outputTotalFrameM_ldS r _
    | with_reducible exact outputTotalFrameM_stS r _ _
    | with_reducible (refine outputTotalFrameM_bind ?_ (fun _ => ?_))

/-- Every successful actual constructor step preserves the public output total. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem outputTotalFrameM_table_buildStep (r : ZStreamRef) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    OutputTotalFrameM r (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact outputTotalFrameM_table_chk32 r _
    | with_reducible exact outputTotalFrameM_table_shl32 r _ _
    | with_reducible exact outputTotalFrameM_table_shr32 r _ _
    | with_reducible exact outputTotalFrameM_table_shl1i32 r _
    | with_reducible exact outputTotalFrameM_table_geta r _ _
    | with_reducible exact outputTotalFrameM_table_seta r _ _ _
    | with_reducible exact outputTotalFrameM_table_storeCode r _ _ _
    | with_reducible exact outputTotalFrameM_store16 r _ _
    | with_reducible exact outputTotalFrameM_storeCode r _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_ptr_diff r _ _
    | with_reducible exact outputTotalFrameM_pure r _
    | with_reducible exact outputTotalFrameM_ub r _
    | with_reducible (refine outputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputTotalFrameM_ite
    | with_reducible (refine outputTotalFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves the public output total across all alphabets, partial writes and rejection returns. -/
theorem outputTotalFrameM_inflate_table (r : ZStreamRef) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    OutputTotalFrameM r (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact outputTotalFrameM_table_buildStep r _ _
    | with_reducible exact outputTotalFrameM_table_chk32 r _
    | with_reducible exact outputTotalFrameM_table_shl32 r _ _
    | with_reducible exact outputTotalFrameM_table_shr32 r _ _
    | with_reducible exact outputTotalFrameM_table_shl1i32 r _
    | with_reducible exact outputTotalFrameM_table_geta r _ _
    | with_reducible exact outputTotalFrameM_table_seta r _ _ _
    | with_reducible exact outputTotalFrameM_table_storeCode r _ _ _
    | with_reducible exact outputTotalFrameM_store16 r _ _
    | with_reducible exact outputTotalFrameM_storeCode r _ _
    | with_reducible exact outputTotalFrameM_ptr_load r _
    | with_reducible exact outputTotalFrameM_ptr_index r _ _
    | with_reducible exact outputTotalFrameM_ptr_add r _ _
    | with_reducible exact outputTotalFrameM_ptr_diff r _ _
    | with_reducible exact outputTotalFrameM_pure r _
    | with_reducible exact outputTotalFrameM_ub r _
    | with_reducible (refine outputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputTotalFrameM_ite
    | with_reducible (refine outputTotalFrameM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs
