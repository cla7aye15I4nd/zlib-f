import ZlibF.Proof.«inflate.c.live-frame-checksums»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem fastMemoryMetaFrameM_table_chk32 (r : ZStreamRef) (value : Int) : FastMemoryMetaFrameM r (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_table_shl32 (r : ZStreamRef) (value shift : UInt32) : FastMemoryMetaFrameM r (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_table_shr32 (r : ZStreamRef) (value shift : UInt32) : FastMemoryMetaFrameM r (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_table_shl1i32 (r : ZStreamRef) (shift : UInt32) : FastMemoryMetaFrameM r (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_table_geta (r : ZStreamRef) (array : Array UInt16) (index : Nat) : FastMemoryMetaFrameM r (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact fastMemoryMetaFrameM_pure r _
  · exact fastMemoryMetaFrameM_ub r _

theorem fastMemoryMetaFrameM_table_seta (r : ZStreamRef) (array : Array UInt16) (index : Nat) (value : UInt16) :
    FastMemoryMetaFrameM r (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_table_storeCode (r : ZStreamRef) (pointer : CodePtr) (index : Nat) (value : Code) :
    FastMemoryMetaFrameM r (Zlib.Inftrees.storeCode pointer index value) :=
  fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_add r _ _) (fun next => fastMemoryMetaFrameM_storeCode r next value)

/-- Actual fixed-table installation writes only private decoder fields. -/
theorem fastMemoryMetaFrameM_inflate_fixed (r : ZStreamRef) (pointer : InflateStatePtr) :
    FastMemoryMetaFrameM r (Zlib.Inftrees.inflate_fixed pointer) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Every successful actual constructor step preserves stream allocation
and root fields. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem fastMemoryMetaFrameM_table_buildStep (r : ZStreamRef) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    FastMemoryMetaFrameM r (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_table_chk32 r _
    | with_reducible exact fastMemoryMetaFrameM_table_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_table_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_table_shl1i32 r _
    | with_reducible exact fastMemoryMetaFrameM_table_geta r _ _
    | with_reducible exact fastMemoryMetaFrameM_table_seta r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_table_storeCode r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_store16 r _ _
    | with_reducible exact fastMemoryMetaFrameM_storeCode r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves fixed stream
fields across all alphabets, partial writes and rejection returns. -/
theorem fastMemoryMetaFrameM_inflate_table (r : ZStreamRef) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    FastMemoryMetaFrameM r (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_table_buildStep r _ _
    | with_reducible exact fastMemoryMetaFrameM_table_chk32 r _
    | with_reducible exact fastMemoryMetaFrameM_table_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_table_shr32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_table_shl1i32 r _
    | with_reducible exact fastMemoryMetaFrameM_table_geta r _ _
    | with_reducible exact fastMemoryMetaFrameM_table_seta r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_table_storeCode r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_store16 r _ _
    | with_reducible exact fastMemoryMetaFrameM_storeCode r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs
