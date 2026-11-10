import ZlibF.Proof.«deflate.c.borrow-stable-strategies»
import ZlibF.Proof.«deflate.c.engine.common-fast-search-source»

/-! Actual borrowed-view preservation for the exact existing fast source cuts.
These facts concern returning computations, with no stream/configuration or
callee-contract premise. They assert neither safety nor termination. -/
namespace Zlib.Deflate.BorrowProofs.Private
open C C.LibcBorrow Zlib.Deflate Zlib.Deflate.Engine.Proofs Zlib.Deflate.BorrowProofs
set_option autoImplicit false

theorem stable_fastFind (s : DeflateStatePtr) (head : UInt32) :
    StableM (fastFind s head) := by
  unfold fastFind
  repeat' strategy_borrow_step

theorem stable_fastSearch (s : DeflateStatePtr) : StableM (fastSearch s) := by
  unfold fastSearch
  repeat' first
    | with_reducible exact stable_fastFind _ _
    | strategy_borrow_step

theorem stable_fastInsertBody (s : DeflateStatePtr) (head : UInt32) :
    StableM (fastInsertBody s head) := by
  unfold fastInsertBody
  repeat' strategy_borrow_step

theorem stable_fastInsertCond (s : DeflateStatePtr) (head : UInt32) :
    StableM (fastInsertCond s head) := by
  unfold fastInsertCond
  repeat' strategy_borrow_step

theorem stable_fastMatchAdvance (s : DeflateStatePtr) (head : UInt32) :
    StableM (fastMatchAdvance s head) := by
  unfold fastMatchAdvance fillInsertSeed
  repeat' first
    | with_reducible exact stable_fastInsertBody _ _
    | with_reducible exact stable_fastInsertCond _ _
    | strategy_borrow_step

end Zlib.Deflate.BorrowProofs.Private
#print axioms Zlib.Deflate.BorrowProofs.Private.stable_fastFind
#print axioms Zlib.Deflate.BorrowProofs.Private.stable_fastSearch
#print axioms Zlib.Deflate.BorrowProofs.Private.stable_fastInsertBody
#print axioms Zlib.Deflate.BorrowProofs.Private.stable_fastInsertCond
#print axioms Zlib.Deflate.BorrowProofs.Private.stable_fastMatchAdvance
