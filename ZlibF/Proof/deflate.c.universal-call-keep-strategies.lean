import ZlibF.Proof.«deflate.c.universal-call-keep-publish»
import ZlibF.Proof.«deflate.c.engine.slow-source»

/-!
# deflate.c: `KeepRel` for the matcher and the compression strategies

Port of `deflate.c.universal-params-strategies`: `longest_match`, `deflate_stored`,
`deflate_fast`, `deflate_slow`, `deflate_rle` and `deflate_huff` are in `KeepM`.
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem keep_forever (st : LoopS) : KeepM (forever st) := KeepM.pure _

theorem keep_tally_dist (s : DeflateStatePtr) (distance length : UInt32) :
    KeepM (tally_dist s distance length) := by
  let len : UInt8 := length.toUInt8
  let dist : UInt16 := distance.toUInt16
  let rest : M Bool := match s with
    | none => ub "null deflate_state"
    | some (.tab id) => do
      let lc ← index8 (.ref BRef.st_length_code 0) len.toNat
      freq_inc (.dstate_dyn_ltree id) (lc.toNat + 256 + 1)
      let dc ← d_code (dist - 1)
      freq_inc (.dstate_dyn_dtree id) dc.toNat
      let d ← ldDeflateState s
      return d.sym_next == d.sym_end
  have grouped : tally_dist s distance length = (do
      let d ← ldDeflateState s
      let x ← (do
        store_at d.sym_buf d.sym_next.toNat dist.toUInt8
        store_at d.sym_buf (d.sym_next + 1).toNat (dist >>> 8).toUInt8
        store_at d.sym_buf (d.sym_next + 2).toNat len)
      stDeflateState s { d with sym_next := d.sym_next + 3 }
      rest) := by
    unfold tally_dist
    simp only [M_bind_assoc, rest]
    cases s with
    | none => rfl
    | some r => cases r; rfl
  rw [grouped]
  refine keep_ld_st s _ (fun d (_ : Unit) => { d with sym_next := d.sym_next + 3 }) (fun _ _ => rest)
    (fun _ _ => ⟨rfl, rfl⟩) ?_ ?_
  · intro d
    exact KeepM.bind (keep_store_at _ _ _) (fun _ =>
      KeepM.bind (keep_store_at _ _ _) (fun _ => keep_store_at _ _ _))
  · intro d x
    cases s with
    | none => exact KeepM.ub _
    | some r =>
      cases r
      dsimp only [rest]
      repeat' first
        | exact keep_freq_inc _ _
        | exact keep_d_code _
        | k_step

theorem keep_lm_cond (limit scan match_ : BPtr) : KeepM (lm_cond limit scan match_) := by
  unfold lm_cond
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply KeepM.bind
  · apply KeepM.list_forIn
    intro value member current
    k_steps
  · rintro ⟨result, scan, match_⟩
    cases result <;> dsimp only
    all_goals k_steps

theorem keep_lm_body (s : DeflateStatePtr) (st : LMState) : KeepM (lm_body s st) := by
  unfold lm_body
  repeat' first
    | with_reducible exact keep_lm_cond _ _ _
    | k_step

theorem keep_longest_match (s : DeflateStatePtr) (cur : UInt32) : KeepM (longest_match s cur) := by
  unfold longest_match
  repeat' first
    | with_reducible exact keep_lm_body _ _
    | k_step

theorem KeepM.list_forIn_plain {α β : Type} (values : List α) (body : α → β → M (ForInStep β))
    (exact : ∀ value state, KeepM (body value state)) (initial : β) :
    KeepM (forIn values initial body) := by
  induction values generalizing initial with
  | nil => simp only [List.forIn_nil]; exact KeepM.pure _
  | cons head tail ih =>
    simp only [List.forIn_cons]
    apply KeepM.bind (exact head initial)
    intro decision
    cases decision with
    | done value => exact KeepM.pure _
    | yield next => exact ih next

/-- The strategies' callees as steps. -/
macro "k_strategy_step" : tactic => `(tactic|
  first
    | keep_join
    | with_reducible exact keep_tally_lit _ _
    | with_reducible exact keep_tally_dist _ _ _
    | with_reducible exact keep_INSERT_STRING _ _
    | with_reducible exact keep_UPDATE_HASH _ _
    | with_reducible exact keep_longest_match _ _
    | with_reducible exact keep_FLUSH_BLOCK _ _
    | with_reducible exact keep_FLUSH_BLOCK_ONLY _ _
    | with_reducible exact keep_finish_tail _ _
    | with_reducible exact keep_fill_window _
    | with_reducible exact keep_read_buf _ _ _
    | with_reducible exact keep_flush_pending _
    | with_reducible exact keep_put_byte _ _
    | with_reducible exact keep_store_at _ _ _
    | with_reducible exact Zlib.Trees.KeepProofs.keep__tr_stored_block _ _ _ _
    | with_reducible exact keep_slide_hash _
    | with_reducible exact keep_CLEAR_HASH _
    | with_reducible apply KeepM.list_forIn
    | with_reducible apply KeepM.list_forIn_plain
    | with_reducible exact keep_forever _
    | k_step)

theorem keep_deflate_stored (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_stored s flush) := by
  unfold deflate_stored
  repeat' k_strategy_step

set_option maxRecDepth 200000 in
theorem keep_deflate_fast_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    KeepM (deflate_fast_body s flush st) := by
  unfold deflate_fast_body
  repeat' first
    | with_reducible exact keep_tally_lit _ _
    | with_reducible exact keep_tally_dist _ _ _
    | with_reducible exact keep_INSERT_STRING _ _
    | with_reducible exact keep_UPDATE_HASH _ _
    | with_reducible exact keep_longest_match _ _
    | with_reducible exact keep_FLUSH_BLOCK _ _
    | with_reducible exact keep_fill_window _
    | with_reducible exact keep_forever _
    | k_step

theorem keep_deflate_fast (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_fast s flush) := by
  unfold deflate_fast
  repeat' first
    | with_reducible exact keep_deflate_fast_body _ _ _
    | k_strategy_step

/-- The callees of the lazy strategy as steps. -/
macro "k_slow_step" : tactic => `(tactic|
  first
    | with_reducible exact keep_tally_lit _ _
    | with_reducible exact keep_tally_dist _ _ _
    | with_reducible exact keep_INSERT_STRING _ _
    | with_reducible exact keep_longest_match _ _
    | with_reducible exact keep_FLUSH_BLOCK _ _
    | with_reducible exact keep_FLUSH_BLOCK_ONLY _ _
    | with_reducible exact keep_fill_window _
    | k_step)

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowFind (s : DeflateStatePtr) (head : UInt32) : KeepM (slowFind s head) := by
  unfold slowFind; repeat' k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowSearch (s : DeflateStatePtr) : KeepM (slowSearch s) := by
  unfold slowSearch
  repeat' first | with_reducible exact keep_slowFind _ _ | k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowMatchBody (s : DeflateStatePtr) (max_insert head : UInt32) :
    KeepM (slowMatchBody s max_insert head) := by
  unfold slowMatchBody; repeat' k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowMatchCond (s : DeflateStatePtr) (head : UInt32) : KeepM (slowMatchCond s head) := by
  unfold slowMatchCond; repeat' k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowMatchAdvance (s : DeflateStatePtr) (max_insert head : UInt32) :
    KeepM (slowMatchAdvance s max_insert head) := by
  unfold slowMatchAdvance
  repeat' first
    | with_reducible exact keep_slowMatchBody _ _ _
    | with_reducible exact keep_slowMatchCond _ _
    | k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowDecision (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (head : UInt32) :
    KeepM (slowDecision s flush st head) := by
  unfold slowDecision
  repeat' first
    | with_reducible exact keep_slowMatchAdvance _ _ _
    | k_slow_step

theorem keep_deflate_slow_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    KeepM (deflate_slow_body s flush st) := by
  rw [Zlib.Deflate.Engine.Proofs.slow_body_source]
  repeat' first
    | with_reducible exact keep_slowSearch _
    | with_reducible exact keep_slowDecision _ _ _ _
    | k_slow_step

theorem keep_deflate_slow (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_slow s flush) := by
  unfold deflate_slow
  repeat' first
    | with_reducible exact keep_deflate_slow_body _ _ _
    | k_strategy_step

theorem keep_deflate_rle_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    KeepM (deflate_rle_body s flush st) := by
  unfold deflate_rle_body
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' k_strategy_step

theorem keep_deflate_rle (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_rle s flush) := by
  unfold deflate_rle
  repeat' first
    | with_reducible exact keep_deflate_rle_body _ _ _
    | k_strategy_step

theorem keep_deflate_huff_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    KeepM (deflate_huff_body s flush st) := by
  unfold deflate_huff_body
  repeat' k_strategy_step

theorem keep_deflate_huff (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_huff s flush) := by
  unfold deflate_huff
  repeat' first
    | with_reducible exact keep_deflate_huff_body _ _ _
    | k_strategy_step

end Zlib.Deflate.Universal.Keep
