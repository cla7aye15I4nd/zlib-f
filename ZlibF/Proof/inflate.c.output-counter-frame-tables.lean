import ZlibF.Proof.«inflate.c.output-counter-frame-checksums»

namespace Zlib.Inflate.Proofs.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem outputCounterM_table_chk32 (r : ZStreamRef) (value : Int) : OutputCounterM r (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_table_shl32 (r : ZStreamRef) (value shift : UInt32) : OutputCounterM r (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_table_shr32 (r : ZStreamRef) (value shift : UInt32) : OutputCounterM r (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_table_shl1i32 (r : ZStreamRef) (shift : UInt32) : OutputCounterM r (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_table_geta (r : ZStreamRef) (array : Array UInt16) (index : Nat) : OutputCounterM r (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact outputCounterM_pure r _
  · exact outputCounterM_ub r _

theorem outputCounterM_table_seta (r : ZStreamRef) (array : Array UInt16) (index : Nat) (value : UInt16) :
    OutputCounterM r (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact outputCounterM_ite (outputCounterM_pure r _) (outputCounterM_ub r _)

theorem outputCounterM_table_storeCode (r : ZStreamRef) (pointer : CodePtr) (index : Nat) (value : Code) :
    OutputCounterM r (Zlib.Inftrees.storeCode pointer index value) :=
  outputCounterM_bind (outputCounterM_ptr_add r _ _) (fun next => outputCounterM_storeCode r next value)

theorem outputCounterM_inflate_fixed (r : ZStreamRef) (pointer : InflateStatePtr) :
    OutputCounterM r (Zlib.Inftrees.inflate_fixed pointer) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact outputCounterM_ldS r _
    | with_reducible exact outputCounterM_stS r _ _
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

theorem outputCounterM_table_buildStep (r : ZStreamRef) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    OutputCounterM r (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact outputCounterM_table_chk32 r _
    | with_reducible exact outputCounterM_table_shl32 r _ _
    | with_reducible exact outputCounterM_table_shr32 r _ _
    | with_reducible exact outputCounterM_table_shl1i32 r _
    | with_reducible exact outputCounterM_table_geta r _ _
    | with_reducible exact outputCounterM_table_seta r _ _ _
    | with_reducible exact outputCounterM_table_storeCode r _ _ _
    | with_reducible exact outputCounterM_store16 r _ _
    | with_reducible exact outputCounterM_storeCode r _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_ptr_diff r _ _
    | with_reducible exact outputCounterM_pure r _
    | with_reducible exact outputCounterM_ub r _
    | with_reducible (refine outputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputCounterM_ite
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

theorem outputCounterM_inflate_table (r : ZStreamRef) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    OutputCounterM r (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact outputCounterM_table_buildStep r _ _
    | with_reducible exact outputCounterM_table_chk32 r _
    | with_reducible exact outputCounterM_table_shl32 r _ _
    | with_reducible exact outputCounterM_table_shr32 r _ _
    | with_reducible exact outputCounterM_table_shl1i32 r _
    | with_reducible exact outputCounterM_table_geta r _ _
    | with_reducible exact outputCounterM_table_seta r _ _ _
    | with_reducible exact outputCounterM_table_storeCode r _ _ _
    | with_reducible exact outputCounterM_store16 r _ _
    | with_reducible exact outputCounterM_storeCode r _ _
    | with_reducible exact outputCounterM_ptr_load r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_ptr_diff r _ _
    | with_reducible exact outputCounterM_pure r _
    | with_reducible exact outputCounterM_ub r _
    | with_reducible (refine outputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputCounterM_ite
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs.OutputCounter
