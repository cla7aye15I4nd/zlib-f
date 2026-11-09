import ZlibF.Proof.«deflate.c.borrow-stable-base»

/-! # Actual longest-match searches retain borrowed libc text -/

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false

theorem stable_ptr_lt {R T : Type} [Space Heap R T] [DecidableEq R]
    (p q : Ptr R) : StableM (Ptr.lt p q) := by
  intro h v after hr
  unfold Ptr.lt at hr
  repeat' first | split at hr | (cases hr; rfl) | contradiction

theorem stable_ptr_diff {R T : Type} [Space Heap R T] [DecidableEq R]
    (p q : Ptr R) : StableM (Ptr.diff p q) := by
  intro h v after hr
  unfold Ptr.diff at hr
  repeat' first | split at hr | (cases hr; rfl) | contradiction

theorem stable_lm_cond (limit scan match_ : BPtr) : StableM (lm_cond limit scan match_) := by
  unfold lm_cond
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply StableM.bind
  · apply StableM.list_forIn
    intro value member current
    repeat' first | exact stable_load8 _ | deflate_borrow_step
  · rintro ⟨result, scan, match_⟩
    cases result <;> dsimp only
    all_goals repeat' first | exact stable_ptr_lt _ _ | deflate_borrow_step

theorem stable_lm_body (p : DeflateStatePtr) (st : LMState) : StableM (lm_body p st) := by
  unfold lm_body
  repeat' first
    | with_reducible exact stable_lm_cond _ _ _
    | with_reducible exact stable_ptr_diff _ _
    | with_reducible exact stable_isub _ _
    | deflate_borrow_step

theorem stable_longest_match (p : DeflateStatePtr) (cur : UInt32) : StableM (longest_match p cur) := by
  unfold longest_match
  repeat' first
    | with_reducible exact stable_lm_body _ _
    | with_reducible exact stable_isub _ _
    | deflate_borrow_step

end Zlib.Deflate.BorrowProofs
