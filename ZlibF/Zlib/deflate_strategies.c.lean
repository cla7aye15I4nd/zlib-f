import ZlibF.Zlib.«deflate_base.c»

/-!
# deflate.c, part 2: `longest_match` and the five compression functions

`longest_match` (the `#ifndef FASTEST`, not `UNALIGNED_OK` version), `deflate_stored`, `deflate_fast`,
`deflate_slow`, `deflate_rle`, `deflate_huff`. See `deflate_base.c.lean` for the conventions.

Control flow: `for (;;)` with `break` and `return` inside is a `cwhile` over a `LoopS`; `ret = some v` is
`return v`, `brk = true` is `break` (both skip the rest of the body, as `return` in the body function does). A `continue`
of `longest_match`'s `do ... while` jumps to its condition.
-/

namespace Zlib.Deflate
open C
open Zlib.Trees («_tr_init» «_tr_flush_bits» «_tr_flush_block» «_tr_stored_block» «_tr_align»)
open Zlib.Crc32 (crc32 crc32_z)

/-! ## `longest_match` -/

/-- Loop-carried locals of `longest_match`; `brk` is the `break`. -/
structure LMState where
  cur_match : UInt32
  chain_length : UInt32
  best_len : Int32
  nice_match : Int32
  scan : BPtr
  scan_end1 : UInt8
  scan_end : UInt8
  brk : Bool

/-- The condition of the inner `do { } while (*++scan == *++match && ... (8 times) && scan < strend)`; the C unrolls the
comparisons eight times, the loop here repeats the same step eight times. -/
def lm_cond (strend scan match_ : BPtr) : M (Bool × BPtr × BPtr) := do
  let mut scan := scan
  let mut m := match_
  for _ in [0:8] do
    scan ← padd scan 1                       -- ++scan
    m ← padd m 1                             -- ++match
    if (← load8 scan) != (← load8 m) then return (false, scan, m)
  return (← Ptr.lt scan strend, scan, m)     -- scan < strend

/-- The body of the `do` of `longest_match`, up to the end of the compound statement; `continue` is `return st`. -/
def lm_body (s : DeflateStatePtr) (st : LMState) : M LMState := do
  let d ← ldDeflateState s
  -- match = s->window + cur_match;
  let mut match_ ← padd d.window st.cur_match.toNat
  let scan := st.scan
  -- if (match[best_len] != scan_end || match[best_len - 1] != scan_end1 || *match != *scan || *++match != scan[1]) continue;
  if (← index8 match_ st.best_len.toInt) != st.scan_end then return st
  if (← index8 match_ (← isub st.best_len 1).toInt) != st.scan_end1 then return st
  if (← load8 match_) != (← load8 scan) then return st
  match_ ← padd match_ 1
  if (← load8 match_) != (← index8 scan 1) then return st
  -- scan += 2, match++;
  let scan ← padd scan 2
  match_ ← padd match_ 1
  -- strend = s->window + s->strstart + MAX_MATCH;
  let strend ← padd (← padd d.window d.strstart.toNat) MAX_MATCH_u.toNat
  -- do { } while (*++scan == *++match && ... && scan < strend);
  let (scan, _) ← cdoWhile (fun x => pure x)
    (fun (scan, m) => do
      let (c, scan, m) ← lm_cond strend scan m
      pure (c, (scan, m)))
    (scan, match_)
  -- len = MAX_MATCH - (int)(strend - scan);
  let diff ← Ptr.diff strend scan
  let len ← isub 258 diff.toInt32
  -- scan = strend - MAX_MATCH;
  let scan ← psub strend MAX_MATCH_u.toNat
  let mut st := { st with scan }
  -- if (len > best_len) { ... }
  if len > st.best_len then
    wr s (fun d => { d with match_start := st.cur_match })      -- s->match_start = cur_match;
    st := { st with best_len := len }                            -- best_len = len;
    if len ≥ st.nice_match then return { st with brk := true }   -- if (len >= nice_match) break;
    -- scan_end1 = scan[best_len - 1]; scan_end = scan[best_len];
    let e1 ← index8 st.scan (← isub st.best_len 1).toInt
    let e ← index8 st.scan st.best_len.toInt
    st := { st with scan_end1 := e1, scan_end := e }
  return st

/-- `local uInt longest_match(deflate_state *s, IPos cur_match)` -/
def longest_match (s : DeflateStatePtr) (cur_match : UInt32) : M UInt32 := do
  let d ← ldDeflateState s
  let mut chain_length : UInt32 := d.max_chain_length      -- unsigned chain_length = s->max_chain_length;
  let scan ← padd d.window d.strstart.toNat                -- Bytef *scan = s->window + s->strstart;
  let best_len : Int32 := d.prev_length.toInt32            -- int best_len = (int)s->prev_length;
  let mut nice_match : Int32 := d.nice_match               -- int nice_match = s->nice_match;
  -- IPos limit = s->strstart > (IPos)MAX_DIST(s) ? s->strstart - (IPos)MAX_DIST(s) : NIL;
  let maxd : UInt32 := d.w_size - MIN_LOOKAHEAD_u
  let limit : UInt32 := if d.strstart > maxd then d.strstart - maxd else 0
  let prev := d.prev                                       -- Posf *prev = s->prev;
  let wmask := d.w_mask                                    -- uInt wmask = s->w_mask;
  -- Bytef *strend = s->window + s->strstart + MAX_MATCH;
  let _strend ← padd (← padd d.window d.strstart.toNat) MAX_MATCH_u.toNat
  -- Byte scan_end1 = scan[best_len - 1]; Byte scan_end = scan[best_len];
  let scan_end1 ← index8 scan (← isub best_len 1).toInt
  let scan_end ← index8 scan best_len.toInt
  -- if (s->prev_length >= s->good_match) chain_length >>= 2;
  if d.prev_length ≥ d.good_match then chain_length := chain_length >>> 2
  -- if ((uInt)nice_match > s->lookahead) nice_match = (int)s->lookahead;
  if nice_match.toUInt32 > d.lookahead then nice_match := d.lookahead.toInt32
  -- do { ... } while ((cur_match = prev[cur_match & wmask]) > limit && --chain_length != 0);
  let st ← cdoWhile (lm_body s)
    (fun st => do
      if st.brk then return (false, st)                       -- break leaves the loop
      let cm : UInt32 := (← Ptr.index prev (st.cur_match &&& wmask).toNat).toUInt32
      let st := { st with cur_match := cm }
      if cm > limit then
        let cl := st.chain_length - 1                          -- --chain_length
        return (cl != 0, { st with chain_length := cl })
      return (false, st))
    { cur_match, chain_length, best_len, nice_match, scan, scan_end1, scan_end, brk := false }
  -- if ((uInt)best_len <= s->lookahead) return (uInt)best_len; return s->lookahead;
  let lookahead ← rd s (·.lookahead)
  if st.best_len.toUInt32 ≤ lookahead then return st.best_len.toUInt32
  return lookahead

/-! ## Loop state of the compression functions -/

structure LoopS where
  hash_head : UInt32 := 0
  bflush : Bool := false
  ret : Option block_state := none
  brk : Bool := false

/-- `for (;;)`: continues until `break` or `return`. -/
def forever (st : LoopS) : M (Bool × LoopS) := pure (!(st.brk || st.ret.isSome), st)

/-- `MIN(a, b)` is `((a) > (b) ? (b) : (a))` -/
def MIN {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] (a b : α) : α := if b < a then b else a

/-- The part of the compression functions after the loop that ends with `flush == Z_FINISH`, `s->sym_next`, ...:
`if (flush == Z_FINISH) { FLUSH_BLOCK(s, 1); return finish_done; } if (s->sym_next) FLUSH_BLOCK(s, 0); return block_done;` -/
def finish_tail (s : DeflateStatePtr) (flush : Int32) : M block_state := do
  if flush == Z_FINISH then
    if let some r := (← FLUSH_BLOCK s 1) then return r
    return finish_done
  if (← rd s (·.sym_next)) != 0 then
    if let some r := (← FLUSH_BLOCK s 0) then return r
  return block_done

/-! ## `deflate_stored` -/

/-- Locals of the first `do { } while (last == 0)` of `deflate_stored`. -/
structure StoredS where
  last : Int32
  len : UInt32
  left : UInt32
  have_ : UInt32
  all : Bool
  brk : Bool

/-- `local block_state deflate_stored(deflate_state *s, int flush)` -/
def deflate_stored (s : DeflateStatePtr) (flush : Int32) : M block_state := do
  let d ← ldDeflateState s
  -- unsigned min_block = (unsigned)(MIN(s->pending_buf_size - 5, s->w_size));
  let mut min_block : UInt32 := (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32
  let strm := d.strm
  -- unsigned used = s->strm->avail_in;
  let mut used ← zrd strm (·.avail_in)
  let st ← cdoWhile
    (fun (st : StoredS) => do
      -- len = MAX_STORED;
      let mut st := { st with len := MAX_STORED }
      let d ← ldDeflateState s
      -- have = ((unsigned)s->bi_valid + 42) >> 3;
      let hv : UInt32 := (d.bi_valid.toUInt32 + 42) >>> 3
      let z ← ldZStream strm
      -- if (s->strm->avail_out < have) break;
      if z.avail_out < hv then return { st with have_ := hv, brk := true }
      -- have = s->strm->avail_out - have;
      let mut have_ := z.avail_out - hv
      -- left = (unsigned)(s->strstart - s->block_start);
      let left : UInt32 := (← lsub d.strstart.toUInt64.toInt64 d.block_start).toUInt64.toUInt32
      let mut len := st.len
      -- if (left < len && s->strm->avail_in < len - left) len = left + s->strm->avail_in;
      if left < len && z.avail_in < len - left then len := left + z.avail_in
      -- if (len > have) len = have;
      if len > have_ then len := have_
      -- all = len >= left && len - left == s->strm->avail_in;
      let all := len ≥ left && len - left == z.avail_in
      -- if (len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH || !all)) break;
      if len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH || !all) then
        return { st with len, left, have_, all, brk := true }
      -- last = flush == Z_FINISH && all ? 1 : 0;
      let last : Int32 := if flush == Z_FINISH && all then 1 else 0
      -- _tr_stored_block(s, (char *)0, 0L, last);
      _tr_stored_block s (Ptr.null : BPtr) 0 last
      -- s->pending_buf[s->pending - 4] = (Bytef)len; ... [-3] = (Bytef)(len >> 8); [-2] = (Bytef)~len; [-1] = (Bytef)(~len >> 8);
      let d ← ldDeflateState s
      store8 (← padd d.pending_buf (d.pending - 4).toNat) len.toUInt8
      store8 (← padd d.pending_buf (d.pending - 3).toNat) (len >>> 8).toUInt8
      store8 (← padd d.pending_buf (d.pending - 2).toNat) (~~~len).toUInt8
      store8 (← padd d.pending_buf (d.pending - 1).toNat) ((~~~len) >>> 8).toUInt8
      -- flush_pending(s->strm);
      flush_pending strm
      let mut left := left
      -- if (left) { ... }
      if left != 0 then
        if left > len then left := len
        let d ← ldDeflateState s
        let z ← ldZStream strm
        -- zmemcpy(s->strm->next_out, s->window + s->block_start, left);
        memcpyB z.next_out (← Ptr.add d.window d.block_start.toInt) left.toNat
        let no ← padd z.next_out left.toNat
        zwr strm (fun z => { z with next_out := no, avail_out := z.avail_out - left,
                                    total_out := z.total_out + left.toUInt64 })
        let bs ← ladd d.block_start left.toUInt64.toInt64      -- s->block_start += left;
        wr s (fun d => { d with block_start := bs })
        len := len - left
      -- if (len) { read_buf(s->strm, s->strm->next_out, len); ... }
      if len != 0 then
        let _ ← read_buf strm (← zrd strm (·.next_out)) len
        let no ← padd (← zrd strm (·.next_out)) len.toNat
        zwr strm (fun z => { z with next_out := no, avail_out := z.avail_out - len,
                                    total_out := z.total_out + len.toUInt64 })
      pure { st with last, len, left, have_, all, brk := false })
    (fun st => pure (!st.brk && st.last == 0, st))             -- while (last == 0)
    { last := 0, len := 0, left := 0, have_ := 0, all := false, brk := false }
  let mut last := st.last
  -- used -= s->strm->avail_in;
  used := used - (← zrd strm (·.avail_in))
  if used != 0 then
    let d ← ldDeflateState s
    if used ≥ d.w_size then
      -- s->matches = 2; zmemcpy(s->window, s->strm->next_in - s->w_size, s->w_size);
      memcpyB d.window (← psub (← zrd strm (·.next_in)) d.w_size.toNat) d.w_size.toNat
      -- s->strstart = s->w_size; s->insert = s->strstart;
      wr s (fun d => { d with «matches» := 2, strstart := d.w_size, insert := d.w_size })
    else
      -- if (s->window_size - s->strstart <= used) { ... }
      if d.window_size - d.strstart.toUInt64 ≤ used.toUInt64 then
        let ss := d.strstart - d.w_size                          -- s->strstart -= s->w_size;
        memcpyB d.window (← padd d.window d.w_size.toNat) ss.toNat -- zmemcpy(s->window, s->window + s->w_size, s->strstart);
        wr s (fun d => { d with
          strstart := ss,
          «matches» := if d.«matches» < 2 then d.«matches» + 1 else d.«matches»,
          insert := if d.insert > ss then ss else d.insert })
      -- zmemcpy(s->window + s->strstart, s->strm->next_in - used, used);
      let d ← ldDeflateState s
      memcpyB (← padd d.window d.strstart.toNat) (← psub (← zrd strm (·.next_in)) used.toNat) used.toNat
      -- s->strstart += used; s->insert += MIN(used, s->w_size - s->insert);
      wr s (fun d => { d with strstart := d.strstart + used,
                              insert := d.insert + MIN used (d.w_size - d.insert) })
    -- s->block_start = s->strstart;
    wr s (fun d => { d with block_start := d.strstart.toUInt64.toInt64 })
  -- if (s->high_water < s->strstart) s->high_water = s->strstart;
  wr s (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water })
  -- if (last) { s->bi_used = 8; return finish_done; }
  if last != 0 then
    wr s (fun d => { d with bi_used := 8 })
    return finish_done
  -- if (flush != Z_NO_FLUSH && flush != Z_FINISH && s->strm->avail_in == 0 && (long)s->strstart == s->block_start) return block_done;
  let d ← ldDeflateState s
  if flush != Z_NO_FLUSH && flush != Z_FINISH && (← zrd strm (·.avail_in)) == 0 &&
      d.strstart.toUInt64.toInt64 == d.block_start then
    return block_done
  -- have = (unsigned)(s->window_size - s->strstart);
  let mut have_ : UInt32 := (d.window_size - d.strstart.toUInt64).toUInt32
  -- if (s->strm->avail_in > have && s->block_start >= (long)s->w_size) { ... }
  if (← zrd strm (·.avail_in)) > have_ && d.block_start ≥ d.w_size.toUInt64.toInt64 then
    let bs ← lsub d.block_start d.w_size.toUInt64.toInt64        -- s->block_start -= s->w_size;
    let ss := d.strstart - d.w_size                              -- s->strstart -= s->w_size;
    memcpyB d.window (← padd d.window d.w_size.toNat) ss.toNat
    wr s (fun d => { d with
      block_start := bs, strstart := ss,
      «matches» := if d.«matches» < 2 then d.«matches» + 1 else d.«matches»,
      insert := if d.insert > ss then ss else d.insert })
    have_ := have_ + d.w_size                                    -- have += s->w_size;
  -- if (have > s->strm->avail_in) have = s->strm->avail_in;
  let ai ← zrd strm (·.avail_in)
  if have_ > ai then have_ := ai
  -- if (have) { read_buf(s->strm, s->window + s->strstart, have); ... }
  if have_ != 0 then
    let d ← ldDeflateState s
    let _ ← read_buf strm (← padd d.window d.strstart.toNat) have_
    wr s (fun d => { d with strstart := d.strstart + have_,
                            insert := d.insert + MIN have_ (d.w_size - d.insert) })
  wr s (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water })
  let d ← ldDeflateState s
  -- have = ((unsigned)s->bi_valid + 42) >> 3;
  have_ := (d.bi_valid.toUInt32 + 42) >>> 3
  -- have = (unsigned)MIN(s->pending_buf_size - have, MAX_STORED);
  have_ := (MIN (d.pending_buf_size - have_.toUInt64) MAX_STORED.toUInt64).toUInt32
  -- min_block = MIN(have, s->w_size);
  min_block := MIN have_ d.w_size
  -- left = (unsigned)(s->strstart - s->block_start);
  let left : UInt32 := (← lsub d.strstart.toUInt64.toInt64 d.block_start).toUInt64.toUInt32
  let ai ← zrd strm (·.avail_in)
  -- if (left >= min_block || ((left || flush == Z_FINISH) && flush != Z_NO_FLUSH && s->strm->avail_in == 0 && left <= have)) { ... }
  if left ≥ min_block ||
      ((left != 0 || flush == Z_FINISH) && flush != Z_NO_FLUSH && ai == 0 && left ≤ have_) then
    let len := MIN left have_                                    -- len = MIN(left, have);
    -- last = flush == Z_FINISH && s->strm->avail_in == 0 && len == left ? 1 : 0;
    last := if flush == Z_FINISH && ai == 0 && len == left then 1 else 0
    -- _tr_stored_block(s, (charf *)s->window + s->block_start, len, last);
    _tr_stored_block s (← Ptr.add d.window d.block_start.toInt) len.toUInt64 last
    let bs ← ladd d.block_start len.toUInt64.toInt64             -- s->block_start += len;
    wr s (fun d => { d with block_start := bs })
    flush_pending strm
  -- if (last) s->bi_used = 8;
  if last != 0 then wr s (fun d => { d with bi_used := 8 })
  -- return last ? finish_started : need_more;
  return if last != 0 then finish_started else need_more

/-! ## `deflate_fast` -/

/-- One iteration of `for (;;)` in `deflate_fast`. -/
def deflate_fast_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) : M LoopS := do
  -- if (s->lookahead < MIN_LOOKAHEAD) { ... }
  if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then
    fill_window s
    let la ← rd s (·.lookahead)
    if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }
    if la == 0 then return { st with brk := true }
  -- hash_head = NIL; if (s->lookahead >= MIN_MATCH) INSERT_STRING(s, s->strstart, hash_head);
  let mut hash_head : UInt32 := 0
  if (← rd s (·.lookahead)) ≥ MIN_MATCH_u then
    hash_head ← INSERT_STRING s (← rd s (·.strstart))
  -- if (hash_head != NIL && s->strstart - hash_head <= MAX_DIST(s)) { s->match_length = longest_match(s, hash_head); }
  let d ← ldDeflateState s
  if hash_head != 0 && d.strstart - hash_head ≤ d.w_size - MIN_LOOKAHEAD_u then
    let ml ← longest_match s hash_head
    wr s (fun d => { d with match_length := ml })
  let d ← ldDeflateState s
  let mut bflush := false
  if d.match_length ≥ MIN_MATCH_u then
    -- _tr_tally_dist(s, s->strstart - s->match_start, s->match_length - MIN_MATCH, bflush);
    bflush ← tally_dist s (d.strstart - d.match_start) (d.match_length - MIN_MATCH_u)
    -- s->lookahead -= s->match_length;
    wr s (fun d => { d with lookahead := d.lookahead - d.match_length })
    let d ← ldDeflateState s
    -- if (s->match_length <= s->max_insert_length && s->lookahead >= MIN_MATCH) {   (max_insert_length is max_lazy_match)
    if d.match_length ≤ d.max_lazy_match && d.lookahead ≥ MIN_MATCH_u then
      wr s (fun d => { d with match_length := d.match_length - 1 })      -- s->match_length--;
      -- do { s->strstart++; INSERT_STRING(s, s->strstart, hash_head); } while (--s->match_length != 0);
      let hh ← cdoWhile
        (fun (_ : UInt32) => do
          wr s (fun d => { d with strstart := d.strstart + 1 })
          INSERT_STRING s (← rd s (·.strstart)))
        (fun hh => do
          wr s (fun d => { d with match_length := d.match_length - 1 })
          pure ((← rd s (·.match_length)) != 0, hh))
        hash_head
      hash_head := hh
      wr s (fun d => { d with strstart := d.strstart + 1 })             -- s->strstart++;
    else
      -- s->strstart += s->match_length; s->match_length = 0;
      wr s (fun d => { d with strstart := d.strstart + d.match_length, match_length := 0 })
      -- s->ins_h = s->window[s->strstart];
      let d ← ldDeflateState s
      let c ← index8 d.window d.strstart.toNat
      wr s (fun d => { d with ins_h := c.toUInt32 })
      -- UPDATE_HASH(s, s->ins_h, s->window[s->strstart + 1]);
      UPDATE_HASH s (← index8 d.window (d.strstart + 1).toNat)
  else
    -- _tr_tally_lit(s, s->window[s->strstart], bflush);
    let c ← index8 d.window d.strstart.toNat
    bflush ← tally_lit s c
    wr s (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
  -- if (bflush) FLUSH_BLOCK(s, 0);
  if bflush then
    if let some r := (← FLUSH_BLOCK s 0) then return { st with hash_head, bflush, ret := some r }
  return { st with hash_head, bflush }

/-- `local block_state deflate_fast(deflate_state *s, int flush)` -/
def deflate_fast (s : DeflateStatePtr) (flush : Int32) : M block_state := do
  let st ← cwhile forever (deflate_fast_body s flush) {}
  if let some r := st.ret then return r
  -- s->insert = s->strstart < MIN_MATCH-1 ? s->strstart : MIN_MATCH-1;
  wr s (fun d => { d with insert := if d.strstart < MIN_MATCH_u - 1 then d.strstart else MIN_MATCH_u - 1 })
  finish_tail s flush

/-! ## `deflate_slow` -/

/-- One iteration of `for (;;)` in `deflate_slow`. -/
def deflate_slow_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) : M LoopS := do
  if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then
    fill_window s
    let la ← rd s (·.lookahead)
    if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }
    if la == 0 then return { st with brk := true }
  -- hash_head = NIL; if (s->lookahead >= MIN_MATCH) INSERT_STRING(s, s->strstart, hash_head);
  let mut hash_head : UInt32 := 0
  if (← rd s (·.lookahead)) ≥ MIN_MATCH_u then
    hash_head ← INSERT_STRING s (← rd s (·.strstart))
  -- s->prev_length = s->match_length, s->prev_match = s->match_start; s->match_length = MIN_MATCH-1;
  wr s (fun d => { d with prev_length := d.match_length, prev_match := d.match_start, match_length := MIN_MATCH_u - 1 })
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
  let d ← ldDeflateState s
  let mut bflush := false
  -- if (s->prev_length >= MIN_MATCH && s->match_length <= s->prev_length) { ... }
  if d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length then
    -- uInt max_insert = s->strstart + s->lookahead - MIN_MATCH;
    let max_insert : UInt32 := d.strstart + d.lookahead - MIN_MATCH_u
    -- _tr_tally_dist(s, s->strstart - 1 - s->prev_match, s->prev_length - MIN_MATCH, bflush);
    bflush ← tally_dist s (d.strstart - 1 - d.prev_match) (d.prev_length - MIN_MATCH_u)
    -- s->lookahead -= s->prev_length - 1; s->prev_length -= 2;
    wr s (fun d => { d with lookahead := d.lookahead - (d.prev_length - 1), prev_length := d.prev_length - 2 })
    -- do { if (++s->strstart <= max_insert) { INSERT_STRING(s, s->strstart, hash_head); } } while (--s->prev_length != 0);
    let hh ← cdoWhile
      (fun (hh : UInt32) => do
        wr s (fun d => { d with strstart := d.strstart + 1 })
        let ss ← rd s (·.strstart)
        if ss ≤ max_insert then INSERT_STRING s ss else pure hh)
      (fun hh => do
        wr s (fun d => { d with prev_length := d.prev_length - 1 })
        pure ((← rd s (·.prev_length)) != 0, hh))
      hash_head
    hash_head := hh
    -- s->match_available = 0; s->match_length = MIN_MATCH-1; s->strstart++;
    wr s (fun d => { d with match_available := 0, match_length := MIN_MATCH_u - 1, strstart := d.strstart + 1 })
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

/-- `local block_state deflate_slow(deflate_state *s, int flush)` -/
def deflate_slow (s : DeflateStatePtr) (flush : Int32) : M block_state := do
  let st ← cwhile forever (deflate_slow_body s flush) {}
  if let some r := st.ret then return r
  -- if (s->match_available) { _tr_tally_lit(s, s->window[s->strstart - 1], bflush); s->match_available = 0; }
  let d ← ldDeflateState s
  if d.match_available != 0 then
    let c ← index8 d.window (d.strstart - 1).toNat
    let _ ← tally_lit s c
    wr s (fun d => { d with match_available := 0 })
  -- s->insert = s->strstart < MIN_MATCH-1 ? s->strstart : MIN_MATCH-1;
  wr s (fun d => { d with insert := if d.strstart < MIN_MATCH_u - 1 then d.strstart else MIN_MATCH_u - 1 })
  finish_tail s flush

/-! ## `deflate_rle` -/

/-- One iteration of `for (;;)` in `deflate_rle`. -/
def deflate_rle_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) : M LoopS := do
  -- if (s->lookahead <= MAX_MATCH) { ... }
  if (← rd s (·.lookahead)) ≤ MAX_MATCH_u then
    fill_window s
    let la ← rd s (·.lookahead)
    if la ≤ MAX_MATCH_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }
    if la == 0 then return { st with brk := true }
  -- s->match_length = 0;
  wr s (fun d => { d with match_length := 0 })
  let d ← ldDeflateState s
  -- if (s->lookahead >= MIN_MATCH && s->strstart > 0) { ... }
  if d.lookahead ≥ MIN_MATCH_u && d.strstart > 0 then
    -- scan = s->window + s->strstart - 1; prev = *scan;
    let mut scan ← psub (← padd d.window d.strstart.toNat) 1
    let prev : UInt32 := (← load8 scan).toUInt32
    -- if (prev == *++scan && prev == *++scan && prev == *++scan) { ... }
    scan ← padd scan 1
    let mut ok := prev == (← load8 scan).toUInt32
    if ok then
      scan ← padd scan 1
      ok := prev == (← load8 scan).toUInt32
    if ok then
      scan ← padd scan 1
      ok := prev == (← load8 scan).toUInt32
    if ok then
      -- strend = s->window + s->strstart + MAX_MATCH;
      let strend ← padd (← padd d.window d.strstart.toNat) MAX_MATCH_u.toNat
      -- do { } while (prev == *++scan && ... (8 times) && scan < strend);
      let scan2 ← cdoWhile (fun x => pure x)
        (fun scan => do
          let mut scan := scan
          for _ in [0:8] do
            scan ← padd scan 1
            if prev != (← load8 scan).toUInt32 then return (false, scan)
          return (← Ptr.lt scan strend, scan))
        scan
      -- s->match_length = MAX_MATCH - (uInt)(strend - scan);
      let diff ← Ptr.diff strend scan2
      let ml : UInt32 := MAX_MATCH_u - diff.toUInt64.toUInt32
      wr s (fun d => { d with match_length := ml })
      -- if (s->match_length > s->lookahead) s->match_length = s->lookahead;
      wr s (fun d => { d with match_length := if d.match_length > d.lookahead then d.lookahead else d.match_length })
  let d ← ldDeflateState s
  let mut bflush := false
  -- if (s->match_length >= MIN_MATCH) { ... } else { ... }
  if d.match_length ≥ MIN_MATCH_u then
    bflush ← tally_dist s 1 (d.match_length - MIN_MATCH_u)      -- _tr_tally_dist(s, 1, s->match_length - MIN_MATCH, bflush);
    wr s (fun d => { d with lookahead := d.lookahead - d.match_length,
                            strstart := d.strstart + d.match_length, match_length := 0 })
  else
    let c ← index8 d.window d.strstart.toNat
    bflush ← tally_lit s c
    wr s (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
  if bflush then
    if let some r := (← FLUSH_BLOCK s 0) then return { st with bflush, ret := some r }
  return { st with bflush }

/-- `local block_state deflate_rle(deflate_state *s, int flush)` -/
def deflate_rle (s : DeflateStatePtr) (flush : Int32) : M block_state := do
  let st ← cwhile forever (deflate_rle_body s flush) {}
  if let some r := st.ret then return r
  wr s (fun d => { d with insert := 0 })                         -- s->insert = 0;
  finish_tail s flush

/-! ## `deflate_huff` -/

/-- One iteration of `for (;;)` in `deflate_huff`. -/
def deflate_huff_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) : M LoopS := do
  -- if (s->lookahead == 0) { fill_window(s); if (s->lookahead == 0) { if (flush == Z_NO_FLUSH) return need_more; break; } }
  if (← rd s (·.lookahead)) == 0 then
    fill_window s
    if (← rd s (·.lookahead)) == 0 then
      if flush == Z_NO_FLUSH then return { st with ret := some need_more }
      return { st with brk := true }
  -- s->match_length = 0;
  wr s (fun d => { d with match_length := 0 })
  -- _tr_tally_lit(s, s->window[s->strstart], bflush);
  let d ← ldDeflateState s
  let c ← index8 d.window d.strstart.toNat
  let bflush ← tally_lit s c
  wr s (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
  if bflush then
    if let some r := (← FLUSH_BLOCK s 0) then return { st with bflush, ret := some r }
  return { st with bflush }

/-- `local block_state deflate_huff(deflate_state *s, int flush)` -/
def deflate_huff (s : DeflateStatePtr) (flush : Int32) : M block_state := do
  let st ← cwhile forever (deflate_huff_body s flush) {}
  if let some r := st.ret then return r
  wr s (fun d => { d with insert := 0 })                         -- s->insert = 0;
  finish_tail s flush

end Zlib.Deflate
