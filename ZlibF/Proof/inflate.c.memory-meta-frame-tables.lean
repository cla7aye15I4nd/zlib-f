import ZlibF.Proof.«inflate.c.memory-meta-frame-checksums»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem memoryMetaFrameM_table_chk32 (r : ZStreamRef) (value : Int) : MemoryMetaFrameM r (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_table_shl32 (r : ZStreamRef) (value shift : UInt32) : MemoryMetaFrameM r (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_table_shr32 (r : ZStreamRef) (value shift : UInt32) : MemoryMetaFrameM r (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_table_shl1i32 (r : ZStreamRef) (shift : UInt32) : MemoryMetaFrameM r (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_table_geta (r : ZStreamRef) (array : Array UInt16) (index : Nat) : MemoryMetaFrameM r (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact memoryMetaFrameM_pure r _
  · exact memoryMetaFrameM_ub r _

theorem memoryMetaFrameM_table_seta (r : ZStreamRef) (array : Array UInt16) (index : Nat) (value : UInt16) :
    MemoryMetaFrameM r (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact memoryMetaFrameM_ite (memoryMetaFrameM_pure r _) (memoryMetaFrameM_ub r _)

theorem memoryMetaFrameM_table_storeCode (r : ZStreamRef) (pointer : CodePtr) (index : Nat) (value : Code) :
    MemoryMetaFrameM r (Zlib.Inftrees.storeCode pointer index value) :=
  memoryMetaFrameM_bind (memoryMetaFrameM_ptr_add r _ _) (fun next => memoryMetaFrameM_storeCode r next value)

/-- Actual fixed-table installation writes only private decoder fields. -/
theorem memoryMetaFrameM_inflate_fixed (r : ZStreamRef) (pointer : InflateStatePtr) :
    MemoryMetaFrameM r (Zlib.Inftrees.inflate_fixed pointer) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_stS r _ _
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Every successful actual constructor step preserves stream allocation
and root fields. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem memoryMetaFrameM_table_buildStep (r : ZStreamRef) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    MemoryMetaFrameM r (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact memoryMetaFrameM_table_chk32 r _
    | with_reducible exact memoryMetaFrameM_table_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_table_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_table_shl1i32 r _
    | with_reducible exact memoryMetaFrameM_table_geta r _ _
    | with_reducible exact memoryMetaFrameM_table_seta r _ _ _
    | with_reducible exact memoryMetaFrameM_table_storeCode r _ _ _
    | with_reducible exact memoryMetaFrameM_store16 r _ _
    | with_reducible exact memoryMetaFrameM_storeCode r _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible exact memoryMetaFrameM_ub r _
    | with_reducible (refine memoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine memoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves fixed stream
fields across all alphabets, partial writes and rejection returns. -/
theorem memoryMetaFrameM_inflate_table (r : ZStreamRef) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    MemoryMetaFrameM r (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact memoryMetaFrameM_table_buildStep r _ _
    | with_reducible exact memoryMetaFrameM_table_chk32 r _
    | with_reducible exact memoryMetaFrameM_table_shl32 r _ _
    | with_reducible exact memoryMetaFrameM_table_shr32 r _ _
    | with_reducible exact memoryMetaFrameM_table_shl1i32 r _
    | with_reducible exact memoryMetaFrameM_table_geta r _ _
    | with_reducible exact memoryMetaFrameM_table_seta r _ _ _
    | with_reducible exact memoryMetaFrameM_table_storeCode r _ _ _
    | with_reducible exact memoryMetaFrameM_store16 r _ _
    | with_reducible exact memoryMetaFrameM_storeCode r _ _
    | with_reducible exact memoryMetaFrameM_ptr_load r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible exact memoryMetaFrameM_ub r _
    | with_reducible (refine memoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine memoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

end Zlib.Inflate.Proofs
