import ZlibF.Proof.«inflate.c.stream-frame-checksums»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem streamFrameM_table_chk32 (r : ZStreamRef) (value : Int) : StreamFrameM r (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_table_shl32 (r : ZStreamRef) (value shift : UInt32) : StreamFrameM r (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_table_shr32 (r : ZStreamRef) (value shift : UInt32) : StreamFrameM r (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_table_shl1i32 (r : ZStreamRef) (shift : UInt32) : StreamFrameM r (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_table_geta (r : ZStreamRef) (array : Array UInt16) (index : Nat) : StreamFrameM r (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact streamFrameM_pure r _
  · exact streamFrameM_ub r _

theorem streamFrameM_table_seta (r : ZStreamRef) (array : Array UInt16) (index : Nat) (value : UInt16) :
    StreamFrameM r (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact streamFrameM_ite (streamFrameM_pure r _) (streamFrameM_ub r _)

theorem streamFrameM_table_storeCode (r : ZStreamRef) (pointer : CodePtr) (index : Nat) (value : Code) :
    StreamFrameM r (Zlib.Inftrees.storeCode pointer index value) :=
  streamFrameM_bind (streamFrameM_ptr_add r _ _) (fun next => streamFrameM_storeCode r next value)

/-- Actual fixed-table installation writes only private decoder fields. -/
theorem streamFrameM_inflate_fixed (r : ZStreamRef) (pointer : InflateStatePtr) :
    StreamFrameM r (Zlib.Inftrees.inflate_fixed pointer) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact streamFrameM_ldS r _
    | with_reducible exact streamFrameM_stS r _ _
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

/-- Every successful actual constructor step preserves stream allocation
and root fields. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem streamFrameM_table_buildStep (r : ZStreamRef) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    StreamFrameM r (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact streamFrameM_table_chk32 r _
    | with_reducible exact streamFrameM_table_shl32 r _ _
    | with_reducible exact streamFrameM_table_shr32 r _ _
    | with_reducible exact streamFrameM_table_shl1i32 r _
    | with_reducible exact streamFrameM_table_geta r _ _
    | with_reducible exact streamFrameM_table_seta r _ _ _
    | with_reducible exact streamFrameM_table_storeCode r _ _ _
    | with_reducible exact streamFrameM_store16 r _ _
    | with_reducible exact streamFrameM_storeCode r _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_ptr_diff r _ _
    | with_reducible exact streamFrameM_pure r _
    | with_reducible exact streamFrameM_ub r _
    | with_reducible (refine streamFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine streamFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply streamFrameM_ite
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves fixed stream
fields across all alphabets, partial writes and rejection returns. -/
theorem streamFrameM_inflate_table (r : ZStreamRef) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    StreamFrameM r (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact streamFrameM_table_buildStep r _ _
    | with_reducible exact streamFrameM_table_chk32 r _
    | with_reducible exact streamFrameM_table_shl32 r _ _
    | with_reducible exact streamFrameM_table_shr32 r _ _
    | with_reducible exact streamFrameM_table_shl1i32 r _
    | with_reducible exact streamFrameM_table_geta r _ _
    | with_reducible exact streamFrameM_table_seta r _ _ _
    | with_reducible exact streamFrameM_table_storeCode r _ _ _
    | with_reducible exact streamFrameM_store16 r _ _
    | with_reducible exact streamFrameM_storeCode r _ _
    | with_reducible exact streamFrameM_ptr_load r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_ptr_diff r _ _
    | with_reducible exact streamFrameM_pure r _
    | with_reducible exact streamFrameM_ub r _
    | with_reducible (refine streamFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine streamFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply streamFrameM_ite
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs
