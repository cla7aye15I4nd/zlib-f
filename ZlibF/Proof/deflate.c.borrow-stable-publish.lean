import ZlibF.Proof.«trees.c.borrow-stable»
import ZlibF.Proof.«deflate.c.borrow-stable-helpers»

/-! # Actual block publication and header loops retain borrowed libc text -/

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false
set_option maxRecDepth 10000

theorem stable_flush_pending (p : ZStreamPtr) : StableM (flush_pending p) := by
  unfold flush_pending
  repeat' first
    | exact Zlib.Trees.BorrowProofs.stable__tr_flush_bits _
    | deflate_borrow_step

theorem stable_FLUSH_BLOCK_ONLY (p : DeflateStatePtr) (last : Int32) :
    StableM (FLUSH_BLOCK_ONLY p last) := by
  unfold FLUSH_BLOCK_ONLY
  repeat' first
    | exact Zlib.Trees.BorrowProofs.stable__tr_flush_block _ _ _ _
    | exact stable_flush_pending _
    | deflate_borrow_step

theorem stable_FLUSH_BLOCK (p : DeflateStatePtr) (last : Int32) : StableM (FLUSH_BLOCK p last) := by
  unfold FLUSH_BLOCK
  repeat' first
    | exact stable_FLUSH_BLOCK_ONLY _ _
    | deflate_borrow_step

theorem stable_finish_tail (p : DeflateStatePtr) (flush : Int32) : StableM (finish_tail p flush) := by
  unfold finish_tail
  repeat' first
    | exact stable_FLUSH_BLOCK _ _
    | split
    | deflate_borrow_step

theorem stable_gz_string_loop (p : ZStreamPtr) (s : DeflateStatePtr) (select : GzHeader → BPtr) :
    StableM (gz_string_loop p s select) := by
  unfold gz_string_loop
  repeat' first
    | exact stable_HCRC_UPDATE _ _ _
    | exact stable_flush_pending _
    | exact stable_ldGzHeader _
    | exact stable_put_byte _ _
    | deflate_borrow_step

end Zlib.Deflate.BorrowProofs
