import ZlibF.Proof.«inflate.c.input-total-checksums»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inputTotalFrameM_table_chk32 (r : ZStreamRef) (value : Int) : InputTotalFrameM r (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_table_shl32 (r : ZStreamRef) (value shift : UInt32) : InputTotalFrameM r (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_table_shr32 (r : ZStreamRef) (value shift : UInt32) : InputTotalFrameM r (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_table_shl1i32 (r : ZStreamRef) (shift : UInt32) : InputTotalFrameM r (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_table_geta (r : ZStreamRef) (array : Array UInt16) (index : Nat) : InputTotalFrameM r (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact inputTotalFrameM_pure r _
  · exact inputTotalFrameM_ub r _

theorem inputTotalFrameM_table_seta (r : ZStreamRef) (array : Array UInt16) (index : Nat) (value : UInt16) :
    InputTotalFrameM r (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact inputTotalFrameM_ite (inputTotalFrameM_pure r _) (inputTotalFrameM_ub r _)

theorem inputTotalFrameM_table_storeCode (r : ZStreamRef) (pointer : CodePtr) (index : Nat) (value : Code) :
    InputTotalFrameM r (Zlib.Inftrees.storeCode pointer index value) :=
  inputTotalFrameM_bind (inputTotalFrameM_ptr_add r _ _) (fun next => inputTotalFrameM_storeCode r next value)

/-- Actual fixed-table installation writes only private decoder fields. -/
theorem inputTotalFrameM_inflate_fixed (r : ZStreamRef) (pointer : InflateStatePtr) :
    InputTotalFrameM r (Zlib.Inftrees.inflate_fixed pointer) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact inputTotalFrameM_ldS r _
    | with_reducible exact inputTotalFrameM_stS r _ _
    | with_reducible (refine inputTotalFrameM_bind ?_ (fun _ => ?_))

/-- Every successful actual constructor step preserves the public input total. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem inputTotalFrameM_table_buildStep (r : ZStreamRef) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    InputTotalFrameM r (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact inputTotalFrameM_table_chk32 r _
    | with_reducible exact inputTotalFrameM_table_shl32 r _ _
    | with_reducible exact inputTotalFrameM_table_shr32 r _ _
    | with_reducible exact inputTotalFrameM_table_shl1i32 r _
    | with_reducible exact inputTotalFrameM_table_geta r _ _
    | with_reducible exact inputTotalFrameM_table_seta r _ _ _
    | with_reducible exact inputTotalFrameM_table_storeCode r _ _ _
    | with_reducible exact inputTotalFrameM_store16 r _ _
    | with_reducible exact inputTotalFrameM_storeCode r _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_ptr_diff r _ _
    | with_reducible exact inputTotalFrameM_pure r _
    | with_reducible exact inputTotalFrameM_ub r _
    | with_reducible (refine inputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputTotalFrameM_ite
    | with_reducible (refine inputTotalFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves the public input total across all alphabets, partial writes and rejection returns. -/
theorem inputTotalFrameM_inflate_table (r : ZStreamRef) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    InputTotalFrameM r (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact inputTotalFrameM_table_buildStep r _ _
    | with_reducible exact inputTotalFrameM_table_chk32 r _
    | with_reducible exact inputTotalFrameM_table_shl32 r _ _
    | with_reducible exact inputTotalFrameM_table_shr32 r _ _
    | with_reducible exact inputTotalFrameM_table_shl1i32 r _
    | with_reducible exact inputTotalFrameM_table_geta r _ _
    | with_reducible exact inputTotalFrameM_table_seta r _ _ _
    | with_reducible exact inputTotalFrameM_table_storeCode r _ _ _
    | with_reducible exact inputTotalFrameM_store16 r _ _
    | with_reducible exact inputTotalFrameM_storeCode r _ _
    | with_reducible exact inputTotalFrameM_ptr_load r _
    | with_reducible exact inputTotalFrameM_ptr_index r _ _
    | with_reducible exact inputTotalFrameM_ptr_add r _ _
    | with_reducible exact inputTotalFrameM_ptr_diff r _ _
    | with_reducible exact inputTotalFrameM_pure r _
    | with_reducible exact inputTotalFrameM_ub r _
    | with_reducible (refine inputTotalFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine inputTotalFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply inputTotalFrameM_ite
    | with_reducible (refine inputTotalFrameM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs
