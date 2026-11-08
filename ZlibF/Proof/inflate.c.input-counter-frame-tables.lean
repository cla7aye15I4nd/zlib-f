import ZlibF.Proof.«inflate.c.input-counter-frame-checksums»

namespace Zlib.Inflate.Proofs.InputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputCounterM_table_chk32 (r : ZStreamRef) (value : Int) : InputCounterM r (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_table_shl32 (r : ZStreamRef) (value shift : UInt32) : InputCounterM r (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_table_shr32 (r : ZStreamRef) (value shift : UInt32) : InputCounterM r (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_table_shl1i32 (r : ZStreamRef) (shift : UInt32) : InputCounterM r (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_table_geta (r : ZStreamRef) (array : Array UInt16) (index : Nat) : InputCounterM r (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact inputCounterM_pure r _
  · exact inputCounterM_ub r _

theorem inputCounterM_table_seta (r : ZStreamRef) (array : Array UInt16) (index : Nat) (value : UInt16) :
    InputCounterM r (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact inputCounterM_ite (inputCounterM_pure r _) (inputCounterM_ub r _)

theorem inputCounterM_table_storeCode (r : ZStreamRef) (pointer : CodePtr) (index : Nat) (value : Code) :
    InputCounterM r (Zlib.Inftrees.storeCode pointer index value) :=
  inputCounterM_bind (inputCounterM_ptr_add r _ _) (fun next => inputCounterM_storeCode r next value)

theorem inputCounterM_inflate_fixed (r : ZStreamRef) (pointer : InflateStatePtr) :
    InputCounterM r (Zlib.Inftrees.inflate_fixed pointer) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact inputCounterM_ldS r _
    | with_reducible exact inputCounterM_stS r _ _
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_table_buildStep (r : ZStreamRef) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    InputCounterM r (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact inputCounterM_table_chk32 r _
    | with_reducible exact inputCounterM_table_shl32 r _ _
    | with_reducible exact inputCounterM_table_shr32 r _ _
    | with_reducible exact inputCounterM_table_shl1i32 r _
    | with_reducible exact inputCounterM_table_geta r _ _
    | with_reducible exact inputCounterM_table_seta r _ _ _
    | with_reducible exact inputCounterM_table_storeCode r _ _ _
    | with_reducible exact inputCounterM_store16 r _ _
    | with_reducible exact inputCounterM_storeCode r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_ptr_diff r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible exact inputCounterM_ub r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

theorem inputCounterM_inflate_table (r : ZStreamRef) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    InputCounterM r (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact inputCounterM_table_buildStep r _ _
    | with_reducible exact inputCounterM_table_chk32 r _
    | with_reducible exact inputCounterM_table_shl32 r _ _
    | with_reducible exact inputCounterM_table_shr32 r _ _
    | with_reducible exact inputCounterM_table_shl1i32 r _
    | with_reducible exact inputCounterM_table_geta r _ _
    | with_reducible exact inputCounterM_table_seta r _ _ _
    | with_reducible exact inputCounterM_table_storeCode r _ _ _
    | with_reducible exact inputCounterM_store16 r _ _
    | with_reducible exact inputCounterM_storeCode r _ _
    | with_reducible exact inputCounterM_ptr_load r _
    | with_reducible exact inputCounterM_ptr_index r _ _
    | with_reducible exact inputCounterM_ptr_add r _ _
    | with_reducible exact inputCounterM_ptr_diff r _ _
    | with_reducible exact inputCounterM_pure r _
    | with_reducible exact inputCounterM_ub r _
    | with_reducible (refine inputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputCounterM_ite
    | with_reducible (refine inputCounterM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs.InputCounter
