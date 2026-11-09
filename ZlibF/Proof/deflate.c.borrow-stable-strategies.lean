import Lean
import ZlibF.Proof.«deflate.c.borrow-stable-publish»

/-!
# Actual compression strategies retain borrowed libc text

The result covers every returning branch. Safety and encoding remain the
separate existing execution obligations; no invariant is assumed here.
-/

namespace Zlib.Deflate.BorrowProofs
open C C.LibcBorrow Zlib.Deflate
set_option autoImplicit false
set_option maxRecDepth 1000
set_option maxHeartbeats 200000

theorem stable_forever (st : LoopS) : StableM (forever st) := StableM.pure _

/-- Dispatch on the syntactic computation head before applying a kernel-checked
composition lemma. This tactic does not establish any fact by computation. -/
elab "strategy_borrow_head" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  if target.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro x))
  else
    unless target.isAppOf ``C.LibcBorrow.StableM do
      throwError "Expected StableM or a pointwise composition premise"
    let computation := target.getAppArgs.back!
    let head := computation.getAppFn.constName?
    let candidates : List Lean.Name := [
      ``stable_forever,
      ``stable_finish_tail,
      ``stable_fill_window,
      ``stable_read_buf,
      ``stable_slide_hash,
      ``stable_CLEAR_HASH,
      ``stable_INSERT_STRING,
      ``stable_UPDATE_HASH,
      ``stable_longest_match,
      ``stable_tally_lit,
      ``stable_tally_dist,
      ``stable_FLUSH_BLOCK_ONLY,
      ``stable_FLUSH_BLOCK,
      ``stable_flush_pending,
      ``Zlib.Trees.BorrowProofs.stable__tr_stored_block,
      ``stable_isub,
      ``stable_ladd,
      ``stable_ptr_lt,
      ``stable_ptr_diff,
      ``stable_load8,
      ``stable_ldDeflateState,
      ``stable_stDeflateState,
      ``stable_castDeflateState,
      ``stable_ldZStream,
      ``stable_stZStream,
      ``stable_wr,
      ``stable_rd,
      ``stable_zwr,
      ``stable_zrd,
      ``stable_storeW,
      ``stable_storeTree,
      ``stable_fillW,
      ``stable_memsetB,
      ``stable_store8,
      ``stable_ushl,
      ``stable_lsub,
      ``stable_adler32,
      ``stable_crc32,
      ``stable_memcpyB,
      ``stable_padd,
      ``stable_psub,
      ``stable_ptr_add,
      ``stable_ptr_index,
      ``stable_ptr_load,
      ``stable_index8,
      ``stable_strLitRef,
      ``StableM.pure,
      ``StableM.ub,
      ``StableM.cwhile,
      ``StableM.cdoWhile,
      ``StableM.ite,
      ``StableM.bind,
      ``StableM.list_forIn]
    let mut found := false
    for name in candidates do
      let info ← Lean.getConstInfo name
      let result := info.type.getForallBody
      if result.isAppOf ``C.LibcBorrow.StableM then
        let actual := result.getAppArgs.back!
        if actual.getAppFn.constName? == head then
          Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent name)))
          found := true
          break
    if !found && head == some ``ForIn.forIn then
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply StableM.list_forIn))
      found := true
    unless found do
      throwError "No producer for actual computation head {head}"

macro "strategy_borrow_step" : tactic => `(tactic|
  first
    | strategy_borrow_head
    | split
    | dsimp only)

theorem stable_deflate_stored (s : DeflateStatePtr) (flush : Int32) :
    StableM (deflate_stored s flush) := by
  unfold deflate_stored
  repeat' strategy_borrow_step

theorem stable_deflate_fast_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    StableM (deflate_fast_body s flush st) := by
  unfold deflate_fast_body
  repeat' strategy_borrow_step

theorem stable_deflate_fast (s : DeflateStatePtr) (flush : Int32) : StableM (deflate_fast s flush) := by
  unfold deflate_fast
  repeat' first
    | with_reducible exact stable_deflate_fast_body _ _ _
    | strategy_borrow_step

theorem stable_deflate_slow_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    StableM (deflate_slow_body s flush st) := by
  unfold deflate_slow_body
  repeat' strategy_borrow_step

theorem stable_deflate_slow (s : DeflateStatePtr) (flush : Int32) : StableM (deflate_slow s flush) := by
  unfold deflate_slow
  repeat' first
    | with_reducible exact stable_deflate_slow_body _ _ _
    | strategy_borrow_step

theorem stable_deflate_rle_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    StableM (deflate_rle_body s flush st) := by
  unfold deflate_rle_body
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' strategy_borrow_step

theorem stable_deflate_rle (s : DeflateStatePtr) (flush : Int32) : StableM (deflate_rle s flush) := by
  unfold deflate_rle
  repeat' first
    | with_reducible exact stable_deflate_rle_body _ _ _
    | strategy_borrow_step

theorem stable_deflate_huff_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    StableM (deflate_huff_body s flush st) := by
  unfold deflate_huff_body
  repeat' strategy_borrow_step

theorem stable_deflate_huff (s : DeflateStatePtr) (flush : Int32) : StableM (deflate_huff s flush) := by
  unfold deflate_huff
  repeat' first
    | with_reducible exact stable_deflate_huff_body _ _ _
    | strategy_borrow_step

end Zlib.Deflate.BorrowProofs
