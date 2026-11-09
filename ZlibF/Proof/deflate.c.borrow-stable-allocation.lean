import ZlibF.Proof.«deflate.c.borrow-stable-base»

/-! # Actual default allocator calls retain borrowed libc text -/

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false

theorem stable_allocW (n : Nat) : StableM (allocW n) := by
  intro h v after hr
  unfold allocW at hr
  repeat' first | split at hr | (cases hr; rfl) | contradiction

theorem stable_freeW (p : WPtr) : StableM (freeW p) := by
  intro h v after hr
  unfold freeW at hr
  repeat' first | split at hr | (cases hr; rfl) | contradiction

theorem stable_allocDeflateState : StableM allocDeflateState := by
  intro h v after hr
  unfold allocDeflateState at hr
  repeat' first | split at hr | (cases hr; rfl) | contradiction

theorem stable_freeDeflateState (p : DeflateStatePtr) : StableM (freeDeflateState p) := by
  intro h v after hr
  unfold freeDeflateState at hr
  repeat' first | split at hr | (cases hr; rfl) | contradiction

theorem stable_zalloc_default (p : ZStreamPtr) : StableM (zalloc_default p) := by
  unfold zalloc_default
  deflate_borrow_steps

theorem stable_zfree_default (p : ZStreamPtr) : StableM (zfree_default p) := by
  unfold zfree_default
  deflate_borrow_steps

theorem stable_ZALLOC_bytes (p : ZStreamPtr) (items size : UInt32) :
    StableM (ZALLOC_bytes p items size) := by
  unfold ZALLOC_bytes Zlib.Zutil.zcalloc
  repeat' first
    | exact stable_zalloc_default _
    | exact stable_allocB _
    | deflate_borrow_step

theorem stable_ZALLOC_words (p : ZStreamPtr) (items : UInt32) : StableM (ZALLOC_words p items) := by
  unfold ZALLOC_words
  repeat' first
    | exact stable_zalloc_default _
    | exact stable_allocW _
    | deflate_borrow_step

theorem stable_ZFREE_bytes (p : ZStreamPtr) (bytes : BPtr) : StableM (ZFREE_bytes p bytes) := by
  unfold ZFREE_bytes
  repeat' first
    | exact stable_zfree_default _
    | exact stable_freeB _
    | deflate_borrow_step

theorem stable_ZFREE_words (p : ZStreamPtr) (words : WPtr) : StableM (ZFREE_words p words) := by
  unfold ZFREE_words
  repeat' first
    | exact stable_zfree_default _
    | exact stable_freeW _
    | deflate_borrow_step

theorem stable_deflateEnd (p : ZStreamPtr) : StableM (deflateEnd p) := by
  unfold deflateEnd
  repeat' first
    | exact stable_deflateStateCheck _
    | exact stable_ZFREE_bytes _ _
    | exact stable_ZFREE_words _ _
    | exact stable_zfree_default _
    | exact stable_freeDeflateState _
    | deflate_borrow_step

end Zlib.Deflate.BorrowProofs
