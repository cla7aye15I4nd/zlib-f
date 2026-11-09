import ZlibF.Proof.«inflate.c.borrow-stable-dispatch-primitives»

/-! Actual table construction loops and their stores preserve libc borrow metadata. -/
namespace Zlib.Inflate.BorrowProofs
open C C.LibcBorrow Zlib.Inflate Zlib.Inftrees

theorem stable_table_chk32 (v : Int) : StableM (Zlib.Inftrees.chk32 v) := by
  unfold Zlib.Inftrees.chk32
  repeat' first
    | inflate_borrow_m_step

theorem stable_table_shl32 (x n : UInt32) : StableM (Zlib.Inftrees.shl32 x n) := by
  unfold Zlib.Inftrees.shl32
  repeat' first
    | with_reducible exact stable_table_chk32 _
    | inflate_borrow_m_step

theorem stable_table_shr32 (x n : UInt32) : StableM (Zlib.Inftrees.shr32 x n) := by
  unfold Zlib.Inftrees.shr32
  repeat' first
    | with_reducible exact stable_table_shl32 _ _
    | with_reducible exact stable_table_chk32 _
    | inflate_borrow_m_step

theorem stable_table_shl1i32 (n : UInt32) : StableM (Zlib.Inftrees.shl1i32 n) := by
  unfold Zlib.Inftrees.shl1i32
  repeat' first
    | with_reducible exact stable_table_shr32 _ _
    | with_reducible exact stable_table_shl32 _ _
    | with_reducible exact stable_table_chk32 _
    | inflate_borrow_m_step

theorem stable_table_geta (a : Array UInt16) (i : Nat) : StableM (Zlib.Inftrees.geta a i) := by
  unfold Zlib.Inftrees.geta
  split
  · exact StableM.pure _
  · exact StableM.ub _

theorem stable_table_seta (a : Array UInt16) (i : Nat) (v : UInt16) : StableM (Zlib.Inftrees.seta a i v) := by
  unfold Zlib.Inftrees.seta
  repeat' first
    | with_reducible exact stable_table_geta _ _
    | with_reducible exact stable_table_shl1i32 _
    | with_reducible exact stable_table_shr32 _ _
    | with_reducible exact stable_table_shl32 _ _
    | with_reducible exact stable_table_chk32 _
    | inflate_borrow_m_step

theorem stable_table_storeCode (p : CodePtr) (i : Nat) (v : Code) : StableM (Zlib.Inftrees.storeCode p i v) := by
  unfold Zlib.Inftrees.storeCode
  repeat' first
    | with_reducible exact stable_table_seta _ _ _
    | with_reducible exact stable_table_geta _ _
    | with_reducible exact stable_table_shl1i32 _
    | with_reducible exact stable_table_shr32 _ _
    | with_reducible exact stable_table_shl32 _ _
    | with_reducible exact stable_table_chk32 _
    | inflate_borrow_m_step

theorem stable_table_buildStep (c : Zlib.Inftrees.Ctx) (s : TS) : StableM (Zlib.Inftrees.buildStep c s) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact stable_table_storeCode _ _ _
    | with_reducible exact stable_table_seta _ _ _
    | with_reducible exact stable_table_geta _ _
    | with_reducible exact stable_table_shl1i32 _
    | with_reducible exact stable_table_shr32 _ _
    | with_reducible exact stable_table_shl32 _ _
    | with_reducible exact stable_table_chk32 _
    | inflate_borrow_m_step

theorem stable_table_inflate_table (ty : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32) (work : WPtr) : StableM (Zlib.Inftrees.inflate_table ty lens codes table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact stable_table_buildStep _ _
    | with_reducible exact stable_table_storeCode _ _ _
    | with_reducible exact stable_table_seta _ _ _
    | with_reducible exact stable_table_geta _ _
    | with_reducible exact stable_table_shl1i32 _
    | with_reducible exact stable_table_shr32 _ _
    | with_reducible exact stable_table_shl32 _ _
    | with_reducible exact stable_table_chk32 _
    | inflate_borrow_m_step

theorem stable_table_inflate_fixed (state : InflateStatePtr) : StableM (Zlib.Inftrees.inflate_fixed state) := by
  unfold Zlib.Inftrees.inflate_fixed
  repeat' first
    | with_reducible exact stable_table_inflate_table _ _ _ _ _ _
    | with_reducible exact stable_table_buildStep _ _
    | with_reducible exact stable_table_storeCode _ _ _
    | with_reducible exact stable_table_seta _ _ _
    | with_reducible exact stable_table_geta _ _
    | with_reducible exact stable_table_shl1i32 _
    | with_reducible exact stable_table_shr32 _ _
    | with_reducible exact stable_table_shl32 _ _
    | with_reducible exact stable_table_chk32 _
    | inflate_borrow_m_step


#print axioms stable_table_buildStep
#print axioms stable_table_inflate_table
#print axioms stable_table_inflate_fixed
end Zlib.Inflate.BorrowProofs
