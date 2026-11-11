import ZlibF.Proof.«inflate.c.completes-keep-x»

/-! Table construction keeps `Keeps` (mirrors `inflate.c.borrow-stable-dispatch-tables`). -/
namespace Zlib.Inflate.KeepProofs
open C Zlib.Inflate Zlib.Inftrees
set_option autoImplicit false

theorem keep_table_chk32 (v : Int) : KeepM (Zlib.Inftrees.chk32 v) := by
  unfold Zlib.Inftrees.chk32
  repeat' first
    | keep_m_step

theorem keep_table_shl32 (x n : UInt32) : KeepM (Zlib.Inftrees.shl32 x n) := by
  unfold Zlib.Inftrees.shl32
  repeat' first
    | with_reducible exact keep_table_chk32 _
    | keep_m_step

theorem keep_table_shr32 (x n : UInt32) : KeepM (Zlib.Inftrees.shr32 x n) := by
  unfold Zlib.Inftrees.shr32
  repeat' first
    | with_reducible exact keep_table_shl32 _ _
    | with_reducible exact keep_table_chk32 _
    | keep_m_step

theorem keep_table_shl1i32 (n : UInt32) : KeepM (Zlib.Inftrees.shl1i32 n) := by
  unfold Zlib.Inftrees.shl1i32
  repeat' first
    | with_reducible exact keep_table_shr32 _ _
    | with_reducible exact keep_table_shl32 _ _
    | with_reducible exact keep_table_chk32 _
    | keep_m_step

theorem keep_table_geta (a : Array UInt16) (i : Nat) : KeepM (Zlib.Inftrees.geta a i) := by
  unfold Zlib.Inftrees.geta
  split
  · exact KeepM.pure _
  · exact KeepM.ub _

theorem keep_table_seta (a : Array UInt16) (i : Nat) (v : UInt16) : KeepM (Zlib.Inftrees.seta a i v) := by
  unfold Zlib.Inftrees.seta
  repeat' first
    | with_reducible exact keep_table_geta _ _
    | with_reducible exact keep_table_shl1i32 _
    | with_reducible exact keep_table_shr32 _ _
    | with_reducible exact keep_table_shl32 _ _
    | with_reducible exact keep_table_chk32 _
    | keep_m_step

theorem keep_table_storeCode (p : CodePtr) (i : Nat) (v : Code) : KeepM (Zlib.Inftrees.storeCode p i v) := by
  unfold Zlib.Inftrees.storeCode
  repeat' first
    | with_reducible exact keep_table_seta _ _ _
    | with_reducible exact keep_table_geta _ _
    | with_reducible exact keep_table_shl1i32 _
    | with_reducible exact keep_table_shr32 _ _
    | with_reducible exact keep_table_shl32 _ _
    | with_reducible exact keep_table_chk32 _
    | keep_m_step

-- The branch-expanded table step needs a finite elaboration budget.
set_option maxHeartbeats 1000000 in
theorem keep_table_buildStep (c : Zlib.Inftrees.Ctx) (s : TS) : KeepM (Zlib.Inftrees.buildStep c s) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact keep_table_storeCode _ _ _
    | with_reducible exact keep_table_seta _ _ _
    | with_reducible exact keep_table_geta _ _
    | with_reducible exact keep_table_shl1i32 _
    | with_reducible exact keep_table_shr32 _ _
    | with_reducible exact keep_table_shl32 _ _
    | with_reducible exact keep_table_chk32 _
    | keep_m_step

-- The branch-expanded table step needs a finite elaboration budget.
set_option maxHeartbeats 1000000 in
theorem keep_table_inflate_table (ty : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32) (work : WPtr) : KeepM (Zlib.Inftrees.inflate_table ty lens codes table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact keep_table_buildStep _ _
    | with_reducible exact keep_table_storeCode _ _ _
    | with_reducible exact keep_table_seta _ _ _
    | with_reducible exact keep_table_geta _ _
    | with_reducible exact keep_table_shl1i32 _
    | with_reducible exact keep_table_shr32 _ _
    | with_reducible exact keep_table_shl32 _ _
    | with_reducible exact keep_table_chk32 _
    | keep_m_step

theorem keep_table_inflate_fixed (state : InflateStatePtr) : KeepM (Zlib.Inftrees.inflate_fixed state) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact keep_table_inflate_table _ _ _ _ _ _
    | with_reducible exact keep_table_buildStep _ _
    | with_reducible exact keep_table_storeCode _ _ _
    | with_reducible exact keep_table_seta _ _ _
    | with_reducible exact keep_table_geta _ _
    | with_reducible exact keep_table_shl1i32 _
    | with_reducible exact keep_table_shr32 _ _
    | with_reducible exact keep_table_shl32 _ _
    | with_reducible exact keep_table_chk32 _
    | keep_m_step


#print axioms keep_table_buildStep
#print axioms keep_table_inflate_table
#print axioms keep_table_inflate_fixed
end Zlib.Inflate.KeepProofs
