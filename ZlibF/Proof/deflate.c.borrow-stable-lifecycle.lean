import ZlibF.Proof.«deflate.c.borrow-stable-publish»
import ZlibF.Proof.«deflate.c.borrow-stable-allocation»

/-! # Actual initialization and reset retain borrowed libc text -/

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false
set_option maxRecDepth 10000

theorem stable_lm_init (p : DeflateStatePtr) : StableM (lm_init p) := by
  unfold lm_init
  repeat' first
    | with_reducible exact stable_CLEAR_HASH _
    | with_reducible exact stable_config_at _
    | deflate_borrow_step

theorem stable_deflateResetKeep (p : ZStreamPtr) : StableM (deflateResetKeep p) := by
  unfold deflateResetKeep
  repeat' first
    | with_reducible exact stable_deflateStateCheck _
    | with_reducible exact stable_ineg _
    | with_reducible exact Zlib.Trees.BorrowProofs.stable__tr_init _
    | deflate_borrow_step

theorem stable_deflateReset (p : ZStreamPtr) : StableM (deflateReset p) := by
  unfold deflateReset
  repeat' first
    | with_reducible exact stable_deflateResetKeep _
    | with_reducible exact stable_lm_init _
    | deflate_borrow_step

set_option maxHeartbeats 1000000 in
theorem stable_deflateInit2_ (p : ZStreamPtr) (level method windowBits memLevel strategy : Int32)
    (version : BPtr) (stream_size : Int32) :
    StableM (deflateInit2_ p level method windowBits memLevel strategy version stream_size) := by
  unfold deflateInit2_
  repeat' first
    | with_reducible exact stable_zalloc_default _
    | with_reducible exact stable_allocDeflateState
    | with_reducible exact stable_ZALLOC_bytes _ _ _
    | with_reducible exact stable_ZALLOC_words _ _
    | with_reducible exact stable_ERR_MSG _
    | with_reducible exact stable_deflateEnd _
    | with_reducible exact stable_deflateReset _
    | with_reducible exact stable_iadd _ _
    | with_reducible exact stable_isub _ _
    | with_reducible exact stable_ineg _
    | with_reducible exact stable_ishl _ _
    | with_reducible exact stable_load8 _
    | deflate_borrow_step

theorem stable_deflateInit_ (p : ZStreamPtr) (level : Int32) (version : BPtr) (stream_size : Int32) :
    StableM (deflateInit_ p level version stream_size) := stable_deflateInit2_ _ _ _ _ _ _ _ _

end Zlib.Deflate.BorrowProofs
