import ZlibF.Proof.«deflate.c.engine.match-chains»
import ZlibF.Proof.«deflate.c.engine.fill-source»

/-! # Source cut points of the default slow strategy

The search preserves source-order insertion, lazy-match field updates,
matching and the short-match filter. The complete body equality retains
all deferred-literal, match-emission and flush branches as well.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def slowFind (s : DeflateStatePtr) (hash_head : UInt32) : M Unit := do
  let d ← ldDeflateState s
  -- if (hash_head != NIL && s->prev_length < s->max_lazy_match && s->strstart - hash_head <= MAX_DIST(s)) { ... }
  if hash_head != 0 && d.prev_length < d.max_lazy_match && d.strstart - hash_head ≤ d.w_size - MIN_LOOKAHEAD_u then
    let ml ← longest_match s hash_head
    wr s (fun d => { d with match_length := ml })
    let d ← ldDeflateState s
    -- if (s->match_length <= 5 && (s->strategy == Z_FILTERED || (s->match_length == MIN_MATCH && s->strstart - s->match_start > TOO_FAR)))
    if d.match_length ≤ 5 && (d.strategy == Z_FILTERED ||
        (d.match_length == MIN_MATCH_u && d.strstart - d.match_start > TOO_FAR)) then
      wr s (fun d => { d with match_length := MIN_MATCH_u - 1 })

def slowSearch (s : DeflateStatePtr) : M UInt32 := do
  -- hash_head = NIL; if (s->lookahead >= MIN_MATCH) INSERT_STRING(s, s->strstart, hash_head);
  let mut hash_head : UInt32 := 0
  if (← rd s (·.lookahead)) ≥ MIN_MATCH_u then
    hash_head ← INSERT_STRING s (← rd s (·.strstart))
  -- s->prev_length = s->match_length, s->prev_match = s->match_start; s->match_length = MIN_MATCH-1;
  wr s (fun d => { d with prev_length := d.match_length, prev_match := d.match_start, match_length := MIN_MATCH_u - 1 })
  slowFind s hash_head
  return hash_head

def slowMatchBody (s : DeflateStatePtr) (max_insert : UInt32) (hh : UInt32) : M UInt32 := do
  wr s (fun d => { d with strstart := d.strstart + 1 })
  let ss ← rd s (·.strstart)
  if ss ≤ max_insert then INSERT_STRING s ss else pure hh

def slowMatchCond (s : DeflateStatePtr) (hh : UInt32) : M (Bool × UInt32) := do
  wr s (fun d => { d with prev_length := d.prev_length - 1 })
  pure ((← rd s (·.prev_length)) != 0, hh)

def slowMatchAdvance (s : DeflateStatePtr) (max_insert hash_head : UInt32) : M UInt32 := do
  wr s (fun d => { d with lookahead := d.lookahead - (d.prev_length - 1), prev_length := d.prev_length - 2 })
  let hh ← cdoWhile (slowMatchBody s max_insert) (slowMatchCond s) hash_head
  wr s (fun d => { d with match_available := 0, match_length := MIN_MATCH_u - 1, strstart := d.strstart + 1 })
  return hh

def slowDecision (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (hash_head : UInt32) : M LoopS := do
  let mut hash_head := hash_head
  let d ← ldDeflateState s
  let mut bflush := false
  -- if (s->prev_length >= MIN_MATCH && s->match_length <= s->prev_length) { ... }
  if d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length then
    -- uInt max_insert = s->strstart + s->lookahead - MIN_MATCH;
    let max_insert : UInt32 := d.strstart + d.lookahead - MIN_MATCH_u
    -- _tr_tally_dist(s, s->strstart - 1 - s->prev_match, s->prev_length - MIN_MATCH, bflush);
    bflush ← tally_dist s (d.strstart - 1 - d.prev_match) (d.prev_length - MIN_MATCH_u)
    hash_head ← slowMatchAdvance s max_insert hash_head
    -- if (bflush) FLUSH_BLOCK(s, 0);
    if bflush then
      if let some r := (← FLUSH_BLOCK s 0) then return { st with hash_head, bflush, ret := some r }
  else if d.match_available != 0 then
    -- _tr_tally_lit(s, s->window[s->strstart - 1], bflush);
    let c ← index8 d.window (d.strstart - 1).toNat
    bflush ← tally_lit s c
    -- if (bflush) { FLUSH_BLOCK_ONLY(s, 0); }
    if bflush then FLUSH_BLOCK_ONLY s 0
    -- s->strstart++; s->lookahead--;
    wr s (fun d => { d with strstart := d.strstart + 1, lookahead := d.lookahead - 1 })
    -- if (s->strm->avail_out == 0) return need_more;
    if (← zrd d.strm (·.avail_out)) == 0 then return { st with hash_head, bflush, ret := some need_more }
  else
    -- s->match_available = 1; s->strstart++; s->lookahead--;
    wr s (fun d => { d with match_available := 1, strstart := d.strstart + 1, lookahead := d.lookahead - 1 })
  return { st with hash_head, bflush }

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
Every statement of its loop body is represented by this equality. -/
theorem slow_body_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    deflate_slow_body s flush st = (do
    if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then
      fill_window s
      let la ← rd s (·.lookahead)
      if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }
      if la == 0 then return { st with brk := true }
    let hash_head ← slowSearch s
    slowDecision s flush st hash_head) := by
  unfold deflate_slow_body slowSearch slowFind slowDecision slowMatchAdvance slowMatchBody slowMatchCond
  simp only [M_bind_assoc, M_pure_bind, fill_ite_bind]
  rfl

end Zlib.Deflate.Engine.Proofs
