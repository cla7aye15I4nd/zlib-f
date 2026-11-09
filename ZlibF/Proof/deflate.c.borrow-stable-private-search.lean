import ZlibF.Proof.«deflate.c.engine.slow-source»
import ZlibF.Proof.«deflate.c.borrow-stable-strategies»

/-! Borrow preservation of the exact existing private slow-source cutpoints.
These success-only facts introduce no caller or representation premise. -/
namespace Zlib.Deflate.BorrowProofs.Private
open C C.LibcBorrow Zlib.Deflate Zlib.Deflate.Engine.Proofs Zlib.Deflate.BorrowProofs
set_option autoImplicit false

theorem stable_slowFind (s : DeflateStatePtr) (head : UInt32) : StableM (slowFind s head) := by
  unfold slowFind
  repeat' strategy_borrow_step

theorem stable_slowSearch (s : DeflateStatePtr) : StableM (slowSearch s) := by
  unfold slowSearch
  repeat' first
    | with_reducible exact stable_slowFind _ _
    | strategy_borrow_step

theorem stable_slowMatchBody (s : DeflateStatePtr) (max_insert head : UInt32) :
    StableM (slowMatchBody s max_insert head) := by
  unfold slowMatchBody
  repeat' strategy_borrow_step

theorem stable_slowMatchCond (s : DeflateStatePtr) (head : UInt32) : StableM (slowMatchCond s head) := by
  unfold slowMatchCond
  repeat' strategy_borrow_step

theorem stable_slowMatchAdvance (s : DeflateStatePtr) (max_insert head : UInt32) :
    StableM (slowMatchAdvance s max_insert head) := by
  unfold slowMatchAdvance
  repeat' first
    | with_reducible exact stable_slowMatchBody _ _ _
    | with_reducible exact stable_slowMatchCond _ _
    | strategy_borrow_step

theorem stable_slowDecision (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (head : UInt32) :
    StableM (slowDecision s flush st head) := by
  unfold slowDecision
  repeat' first
    | with_reducible exact stable_slowMatchAdvance _ _ _
    | strategy_borrow_step
end Zlib.Deflate.BorrowProofs.Private
