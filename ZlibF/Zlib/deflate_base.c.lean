import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Tables
import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«zutil.c»
import ZlibF.Zlib.«trees.c»
import ZlibF.Zlib.«crc32.c»

/-!
# deflate.c, part 1: shared definitions, hash macros, `slide_hash`, `read_buf`, `fill_window`, `flush_pending`

Source: `deflate.c` and `deflate.h` of the verified source (no patch touches them), default x86_64 Linux build
(LP64; `GZIP` defined; `LIT_MEM`, `FASTEST`, `UNALIGNED_OK`, `ZLIB_DEBUG`, `Z_SOLO` undefined). The other parts of
the file are `deflate_strategies.c.lean` (`longest_match`, `deflate_stored`, `deflate_fast`, `deflate_slow`,
`deflate_rle`, `deflate_huff`) and `deflate.c.lean` (the public functions).

Decisions (each is also marked where it is used):

* A `deflate_state *` is a `DeflateStatePtr`, a `z_streamp` a `ZStreamPtr`. `s->f` is `rd s (·.f)`, and `s->f = v` is
  `wr s (fun d => { d with f := v })`: a load of the record, a record update and a store, so every access faults on a
  null, dangling or wrong-kind pointer.
* `ZALLOC`/`ZFREE` call through `strm->zalloc`/`zfree`. Only the default `zcalloc`/`zcfree` (`FnPtr.fn "zcalloc"`,
  `"zcfree"`, installed by `deflateInit2_`) are modelled; any other function is `ub "custom allocator not modelled"`.
  `Posf *` blocks (`prev`, `head`) are blocks of the `words` table, so `ZALLOC(strm, n, sizeof(Pos))` is `allocW`
  of the number of 16-bit words in the `n * 2` bytes (the product is taken in `unsigned`, as in `zcalloc`)
  and `zmemzero` of such a block counts words.
* Signed `int` and `long` arithmetic is checked (`iadd`, `isub`, `ishl`, ...: overflow and invalid shifts are
  `Fault.ub`); unsigned arithmetic wraps.
* An `unsigned char *` or `char *` is a `BPtr`; `p + n` is `Ptr.add`, `*p` is `Ptr.load`, `p[i]` is `index8`.
* Output parameters (`unsigned *pending`, `uInt *dictLength`, `z_size_t *destLen`) are modelled in the files that
  use them as an input value and a result.
* The control tags of loops with `break` or `return` are fields of the loop state.
-/

namespace Zlib.Deflate
open C
open Zlib.Trees («_tr_init» «_tr_flush_bits» «_tr_flush_block» «_tr_stored_block» «_tr_align»)
open Zlib.Crc32 (crc32 crc32_z)

/-! ## Constants of `deflate.c` and `deflate.h` -/

def MIN_MATCH_u : UInt32 := 3          -- MIN_MATCH
def MAX_MATCH_u : UInt32 := 258        -- MAX_MATCH
def MIN_LOOKAHEAD_u : UInt32 := 262    -- MIN_LOOKAHEAD = MAX_MATCH+MIN_MATCH+1
def WIN_INIT_u : UInt64 := 258         -- WIN_INIT = MAX_MATCH
def MAX_STORED : UInt32 := 65535
def TOO_FAR : UInt32 := 4096
def sizeof_z_stream : Int32 := 112     -- sizeof(z_stream), LP64

/-- `block_state` (`enum`, so `unsigned`). -/
abbrev block_state := UInt32
def need_more : block_state := 0
def block_done : block_state := 1
def finish_started : block_state := 2
def finish_done : block_state := 3

/-- Which function `config.func` points to (D-6: function pointers to the local compressors are an enum). -/
inductive CompressFunc where
  | stored | fast | slow
  deriving DecidableEq, Inhabited

/-- `struct config_s` -/
structure Config where
  good_length : UInt16
  max_lazy : UInt16
  nice_length : UInt16
  max_chain : UInt16
  func : CompressFunc
  deriving Inhabited

/-- `local const config configuration_table[10]` -/
def configuration_table : Array Config := #[
  -- level 0
  ⟨0, 0, 0, 0, .stored⟩,
  -- level 1
  ⟨4, 4, 8, 4, .fast⟩,
  -- level 2
  ⟨4, 5, 16, 8, .fast⟩,
  -- level 3
  ⟨4, 6, 32, 32, .fast⟩,
  -- level 4
  ⟨4, 4, 16, 16, .slow⟩,
  -- level 5
  ⟨8, 16, 32, 32, .slow⟩,
  -- level 6
  ⟨8, 16, 128, 128, .slow⟩,
  -- level 7
  ⟨8, 32, 128, 256, .slow⟩,
  -- level 8
  ⟨32, 128, 258, 1024, .slow⟩,
  -- level 9
  ⟨32, 258, 258, 4096, .slow⟩]

/-- `configuration_table[level]`: an index outside `0..9` is undefined. -/
def config_at (level : Int32) : M Config :=
  if 0 ≤ level.toInt ∧ level.toInt < 10 then pure configuration_table[level.toInt.toNat]!
  else ub "configuration_table index out of range"

/-! ## Checked signed arithmetic and shifts -/

def chk32 (v : Int) : M Int32 :=
  if -2147483648 ≤ v ∧ v ≤ 2147483647 then pure (Int32.ofInt v) else ub "signed int overflow"
def chk64 (v : Int) : M Int64 :=
  if -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807 then pure (Int64.ofInt v) else ub "signed long overflow"
def iadd (a b : Int32) : M Int32 := chk32 (a.toInt + b.toInt)
def isub (a b : Int32) : M Int32 := chk32 (a.toInt - b.toInt)
def ineg (a : Int32) : M Int32 := chk32 (-a.toInt)
def ladd (a b : Int64) : M Int64 := chk64 (a.toInt + b.toInt)
def lsub (a b : Int64) : M Int64 := chk64 (a.toInt - b.toInt)
/-- `a << n` for `int`: the count must be in `0..31` and the result representable (`a >= 0`). -/
def ishl (a : Int32) (n : Int) : M Int32 :=
  if 0 ≤ n ∧ n < 32 ∧ 0 ≤ a.toInt then chk32 (a.toInt * 2 ^ n.toNat) else ub "invalid shift of an int"
/-- `a << n` for `unsigned`: the count must be in `0..31`. -/
def ushl (a : UInt32) (n : UInt32) : M UInt32 :=
  if n < 32 then pure (a <<< n) else ub "invalid shift of an unsigned"

/-! ## Field access -/

/-- `s->f` (read). -/
@[inline] def rd {α : Type} (s : DeflateStatePtr) (f : DeflateState → α) : M α := do
  return f (← ldDeflateState s)
/-- `s->f = v` and the like (a record update). -/
@[inline] def wr (s : DeflateStatePtr) (f : DeflateState → DeflateState) : M Unit := do
  let d ← ldDeflateState s
  stDeflateState s (f d)
/-- `strm->f` (read). -/
@[inline] def zrd {α : Type} (strm : ZStreamPtr) (f : ZStream → α) : M α := do
  return f (← ldZStream strm)
/-- `strm->f = v` and the like. -/
@[inline] def zwr (strm : ZStreamPtr) (f : ZStream → ZStream) : M Unit := do
  let z ← ldZStream strm
  stZStream strm (f z)

/-- `p + n` for a pointer and a nonnegative count. -/
@[inline] def padd {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : M (Ptr R) := Ptr.add p (n : Int)
/-- `p - n`. -/
@[inline] def psub {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : M (Ptr R) := Ptr.add p (-(n : Int))
/-- `p[i] = v` for a byte pointer and an index. -/
@[inline] def store_at (p : BPtr) (i : Nat) (v : UInt8) : M Unit := do
  store8 (← padd p i) v

/-- `ZALLOC`/`ZFREE` of the default allocator only. -/
def zalloc_default (strm : ZStreamPtr) : M Unit := do
  let z ← ldZStream strm
  if z.zalloc != FnPtr.fn "zcalloc" then ub "custom allocator not modelled"
def zfree_default (strm : ZStreamPtr) : M Unit := do
  let z ← ldZStream strm
  if z.zfree != FnPtr.fn "zcfree" then ub "custom allocator not modelled"

/-- `ZALLOC(strm, items, size)` for a byte block (`zcalloc`: `malloc(items * size)`, product in `unsigned`). -/
def ZALLOC_bytes (strm : ZStreamPtr) (items size : UInt32) : M BPtr := do
  zalloc_default strm
  let z ← ldZStream strm
  Zlib.Zutil.zcalloc z.«opaque» items size
/-- `ZALLOC(strm, items, sizeof(Pos))` for a `Posf *` block (a block of 16-bit words). -/
def ZALLOC_words (strm : ZStreamPtr) (items : UInt32) : M WPtr := do
  zalloc_default strm
  -- zcalloc: malloc(items * size) with the product in `unsigned`; the block of `Pos` has that many bytes / 2 words
  let bytes : UInt32 := items * 2
  allocW (bytes.toNat / 2)
/-- `ZFREE(strm, addr)` of a byte block. -/
def ZFREE_bytes (strm : ZStreamPtr) (p : BPtr) : M Unit := do
  zfree_default strm
  freeB p
/-- `ZFREE(strm, addr)` of a block of words. -/
def ZFREE_words (strm : ZStreamPtr) (p : WPtr) : M Unit := do
  zfree_default strm
  freeW p

/-- `ERR_MSG(err)` -/
def ERR_MSG (err : Int32) : M BPtr := Zlib.Zutil.zError err

/-! ## Macros of `deflate.c` and `deflate.h` -/

/-- `put_byte(s, c)`: `{s->pending_buf[s->pending++] = (Bytef)(c);}` (no capacity test, I-1). -/
def put_byte (s : DeflateStatePtr) (c : UInt8) : M Unit := do
  let d ← ldDeflateState s
  store_at d.pending_buf d.pending.toNat c
  stDeflateState s { d with pending := d.pending + 1 }

/-- `UPDATE_HASH(s, s->ins_h, c)`: `s->ins_h = ((s->ins_h << s->hash_shift) ^ (c)) & s->hash_mask` (`c` is an
`int` made of a byte). -/
def UPDATE_HASH (s : DeflateStatePtr) (c : UInt8) : M Unit := do
  let d ← ldDeflateState s
  let sh ← ushl d.ins_h d.hash_shift
  stDeflateState s { d with ins_h := (sh ^^^ c.toUInt32) &&& d.hash_mask }

/-- `INSERT_STRING(s, str, match_head)`: returns the new `match_head`.
`(UPDATE_HASH(s, s->ins_h, s->window[(str) + (MIN_MATCH-1)]),
  match_head = s->prev[(str) & s->w_mask] = s->head[s->ins_h], s->head[s->ins_h] = (Pos)(str))` -/
def INSERT_STRING (s : DeflateStatePtr) (str : UInt32) : M UInt32 := do
  let d ← ldDeflateState s
  let c ← index8 d.window (str + (MIN_MATCH_u - 1)).toNat
  UPDATE_HASH s c
  let d ← ldDeflateState s
  let v ← Ptr.index d.head d.ins_h.toNat
  Ptr.store (← padd d.prev (str &&& d.w_mask).toNat) v
  Ptr.store (← padd d.head d.ins_h.toNat) str.toUInt16
  return v.toUInt32

/-- `CLEAR_HASH(s)`: `s->head[s->hash_size - 1] = NIL; zmemzero(s->head, (unsigned)(s->hash_size - 1)*sizeof(*s->head));
s->slid = 0;` (the `memset` of `2 * (hash_size - 1)` bytes is `hash_size - 1` words). -/
def CLEAR_HASH (s : DeflateStatePtr) : M Unit := do
  let d ← ldDeflateState s
  Ptr.store (← padd d.head (d.hash_size - 1).toNat) (0 : UInt16)
  Ptr.fill d.head (0 : UInt16) (d.hash_size - 1).toNat
  wr s (fun d => { d with slid := 0 })

/-- `d_code(dist)`: `((dist) < 256 ? _dist_code[dist] : _dist_code[256+((dist)>>7)])` (`dist` is a `ush`). -/
def d_code (dist : UInt16) : M UInt8 :=
  if dist.toNat < 256 then index8 (.ref BRef.st_dist_code 0) dist.toNat
  else index8 (.ref BRef.st_dist_code 0) (256 + (dist >>> 7).toNat)

/-- `s->tree[i].Freq++` for the tree array `r` (`ush`, wraps). -/
def freq_inc (r : CtDataRef) (i : Nat) : M Unit := do
  let p : CtDataPtr := .ref r 0
  let q ← padd p i
  let e ← Ptr.load q
  Ptr.store q { e with fc := e.fc + 1 }

/-- `_tr_tally_lit(s, c, flush)` (`flush` is the result). -/
def tally_lit (s : DeflateStatePtr) (c : UInt8) : M Bool := do
  let cc := c   -- uch cc = (c);
  let d ← ldDeflateState s
  -- s->sym_buf[s->sym_next++] = 0; (twice) = cc;
  store_at d.sym_buf d.sym_next.toNat 0
  store_at d.sym_buf (d.sym_next + 1).toNat 0
  store_at d.sym_buf (d.sym_next + 2).toNat cc
  stDeflateState s { d with sym_next := d.sym_next + 3 }
  -- s->dyn_ltree[cc].Freq++;
  match s with
  | none => ub "null deflate_state"
  | some (.tab id) =>
    freq_inc (.dstate_dyn_ltree id) cc.toNat
    -- flush = (s->sym_next == s->sym_end);
    let d ← ldDeflateState s
    return d.sym_next == d.sym_end

/-- `_tr_tally_dist(s, distance, length, flush)` (the arguments are `unsigned` expressions). -/
def tally_dist (s : DeflateStatePtr) (distance length : UInt32) : M Bool := do
  let len : UInt8 := length.toUInt8            -- uch len = (uch)(length);
  let dist : UInt16 := distance.toUInt16       -- ush dist = (ush)(distance);
  let d ← ldDeflateState s
  store_at d.sym_buf d.sym_next.toNat dist.toUInt8
  store_at d.sym_buf (d.sym_next + 1).toNat (dist >>> 8).toUInt8
  store_at d.sym_buf (d.sym_next + 2).toNat len
  stDeflateState s { d with sym_next := d.sym_next + 3 }
  let dist : UInt16 := dist - 1                -- dist--;
  match s with
  | none => ub "null deflate_state"
  | some (.tab id) =>
    -- s->dyn_ltree[_length_code[len]+LITERALS+1].Freq++;
    let lc ← index8 (.ref BRef.st_length_code 0) len.toNat
    freq_inc (.dstate_dyn_ltree id) (lc.toNat + 256 + 1)
    -- s->dyn_dtree[d_code(dist)].Freq++;
    let dc ← d_code dist
    freq_inc (.dstate_dyn_dtree id) dc.toNat
    let d ← ldDeflateState s
    return d.sym_next == d.sym_end

/-! ## `slide_hash` -/

/-- `local void slide_hash(deflate_state *s)` -/
def slide_hash (s : DeflateStatePtr) : M Unit := do
  let d ← ldDeflateState s
  let wsize : UInt32 := d.w_size                 -- uInt wsize = s->w_size;
  let n : UInt32 := d.hash_size                  -- n = s->hash_size;
  let p : WPtr ← padd d.head n.toNat             -- p = &s->head[n];
  -- do { m = *--p; *p = (Pos)(m >= wsize ? m - wsize : NIL); } while (--n);
  let (_, _) ← cdoWhile
    (fun (n, p) => do
      let p ← psub p 1
      let m : UInt32 := (← Ptr.load p).toUInt32
      Ptr.store p (if m ≥ wsize then (m - wsize).toUInt16 else (0 : UInt16))
      pure (n, p))
    (fun (n, p) => let n := n - 1; pure (n != 0, (n, p)))
    (n, p)
  -- #ifndef FASTEST
  let n : UInt32 := wsize                        -- n = wsize;
  let p : WPtr ← padd d.prev n.toNat             -- p = &s->prev[n];
  let (_, _) ← cdoWhile
    (fun (n, p) => do
      let p ← psub p 1
      let m : UInt32 := (← Ptr.load p).toUInt32
      Ptr.store p (if m ≥ wsize then (m - wsize).toUInt16 else (0 : UInt16))
      pure (n, p))
    (fun (n, p) => let n := n - 1; pure (n != 0, (n, p)))
    (n, p)
  -- s->slid = 1;
  wr s (fun d => { d with slid := 1 })

/-! ## `read_buf` and `fill_window` -/

/-- `local unsigned read_buf(z_streamp strm, Bytef *buf, unsigned size)` -/
def read_buf (strm : ZStreamPtr) (buf : BPtr) (size : UInt32) : M UInt32 := do
  let mut len ← zrd strm (·.avail_in)            -- unsigned len = strm->avail_in;
  if len > size then len := size
  if len == 0 then return 0
  -- strm->avail_in -= len;
  zwr strm (fun z => { z with avail_in := z.avail_in - len })
  -- zmemcpy(buf, strm->next_in, len);
  memcpyB buf (← zrd strm (·.next_in)) len.toNat
  let sp ← castDeflateState (← zrd strm (·.state))
  let wrap ← rd sp (·.wrap)
  if wrap == 1 then
    -- strm->adler = adler32(strm->adler, buf, len);
    let a ← zrd strm (·.adler)
    let r ← Zlib.Adler32.adler32 a buf len
    zwr strm (fun z => { z with adler := r })
  else if wrap == 2 then
    -- strm->adler = crc32(strm->adler, buf, len);
    let a ← zrd strm (·.adler)
    let r ← crc32 a buf len
    zwr strm (fun z => { z with adler := r })
  -- strm->next_in += len; strm->total_in += len;
  let ni ← padd (← zrd strm (·.next_in)) len.toNat
  zwr strm (fun z => { z with next_in := ni, total_in := z.total_in + len.toUInt64 })
  return len

/-- `local void fill_window(deflate_state *s)`.
The loop `do { ... } while (cond)` has two `break`s; the state of the outer loop is the flag `brk`. The
`if (sizeof(int) <= 2)` block is dead (`sizeof(int)` is 4). -/
def fill_window (s : DeflateStatePtr) : M Unit := do
  let wsize ← rd s (·.w_size)                    -- uInt wsize = s->w_size;
  let _ ← cdoWhile
    (fun (_ : Bool) => do
      let d ← ldDeflateState s
      -- more = (unsigned)(s->window_size -(ulg)s->lookahead -(ulg)s->strstart);
      let mut more : UInt32 := (d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64).toUInt32
      -- if (s->strstart >= wsize + MAX_DIST(s)) { ... }   (MAX_DIST(s) = w_size - MIN_LOOKAHEAD)
      if d.strstart ≥ wsize + (d.w_size - MIN_LOOKAHEAD_u) then
        -- zmemcpy(s->window, s->window + wsize, (unsigned)wsize - more);
        memcpyB d.window (← padd d.window wsize.toNat) (wsize - more).toNat
        wr s (fun d => { d with match_start := d.match_start - wsize }) -- s->match_start -= wsize;
        wr s (fun d => { d with strstart := d.strstart - wsize })       -- s->strstart -= wsize;
        let block_start ← lsub (← rd s (·.block_start)) wsize.toUInt64.toInt64
        wr s (fun d => { d with block_start })                         -- s->block_start -= (long) wsize;
        -- if (s->insert > s->strstart) s->insert = s->strstart;
        wr s (fun d => { d with insert := if d.insert > d.strstart then d.strstart else d.insert })
        slide_hash s
        more := more + wsize                                             -- more += wsize;
      -- if (s->strm->avail_in == 0) break;
      let strm ← rd s (·.strm)
      if (← zrd strm (·.avail_in)) == 0 then return true
      -- n = read_buf(s->strm, s->window + s->strstart + s->lookahead, more);
      let d ← ldDeflateState s
      let dst ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
      let n ← read_buf strm dst more
      wr s (fun d => { d with lookahead := d.lookahead + n })            -- s->lookahead += n;
      -- if (s->lookahead + s->insert >= MIN_MATCH) { ... }
      let d ← ldDeflateState s
      if d.lookahead + d.insert ≥ MIN_MATCH_u then
        let str : UInt32 := d.strstart - d.insert                    -- uInt str = s->strstart - s->insert;
        -- s->ins_h = s->window[str];
        let c0 ← index8 d.window str.toNat
        wr s (fun d => { d with ins_h := c0.toUInt32 })
        -- UPDATE_HASH(s, s->ins_h, s->window[str + 1]);
        UPDATE_HASH s (← index8 d.window (str + 1).toNat)
        -- while (s->insert) { ... }
        let (_, _) ← cwhile
          (fun (str, brk) => do
            let ins ← rd s (·.insert)
            pure (ins != 0 && !brk, (str, brk)))
          (fun (str, brk) => do
            let d ← ldDeflateState s
            -- UPDATE_HASH(s, s->ins_h, s->window[str + MIN_MATCH-1]);
            UPDATE_HASH s (← index8 d.window (str + (MIN_MATCH_u - 1)).toNat)
            let d ← ldDeflateState s
            -- s->prev[str & s->w_mask] = s->head[s->ins_h];
            let v ← Ptr.index d.head d.ins_h.toNat
            Ptr.store (← padd d.prev (str &&& d.w_mask).toNat) v
            -- s->head[s->ins_h] = (Pos)str;
            Ptr.store (← padd d.head d.ins_h.toNat) str.toUInt16
            -- str++; s->insert--;
            let str := str + 1
            wr s (fun d => { d with insert := d.insert - 1 })
            -- if (s->lookahead + s->insert < MIN_MATCH) break;
            let d ← ldDeflateState s
            pure (str, d.lookahead + d.insert < MIN_MATCH_u))
          (str, false)
      pure false)
    (fun brk => do
      if brk then return (false, brk)
      -- while (s->lookahead < MIN_LOOKAHEAD && s->strm->avail_in != 0)
      let d ← ldDeflateState s
      if d.lookahead < MIN_LOOKAHEAD_u then
        return ((← zrd d.strm (·.avail_in)) != 0, brk)
      return (false, brk))
    false
  -- if (s->high_water < s->window_size) { ... }
  let d ← ldDeflateState s
  if d.high_water < d.window_size then
    let curr : UInt64 := d.strstart.toUInt64 + d.lookahead.toUInt64   -- ulg curr = s->strstart + (ulg)(s->lookahead);
    if d.high_water < curr then
      -- init = s->window_size - curr; if (init > WIN_INIT) init = WIN_INIT;
      let mut init : UInt64 := d.window_size - curr
      if init > WIN_INIT_u then init := WIN_INIT_u
      -- zmemzero(s->window + curr, (unsigned)init);
      memsetB (← padd d.window curr.toNat) 0 init.toUInt32.toNat
      wr s (fun d => { d with high_water := curr + init })              -- s->high_water = curr + init;
    else if d.high_water < curr + WIN_INIT_u then
      -- init = (ulg)curr + WIN_INIT - s->high_water;
      let mut init : UInt64 := curr + WIN_INIT_u - d.high_water
      -- if (init > s->window_size - s->high_water) init = s->window_size - s->high_water;
      if init > d.window_size - d.high_water then init := d.window_size - d.high_water
      -- zmemzero(s->window + s->high_water, (unsigned)init);
      memsetB (← padd d.window d.high_water.toNat) 0 init.toUInt32.toNat
      wr s (fun d => { d with high_water := d.high_water + init })      -- s->high_water += init;

/-! ## `putShortMSB`, `flush_pending` -/

/-- `local void putShortMSB(deflate_state *s, uInt b)` -/
def putShortMSB (s : DeflateStatePtr) (b : UInt32) : M Unit := do
  put_byte s (b >>> 8).toUInt8        -- put_byte(s, (Byte)(b >> 8));
  put_byte s (b &&& 0xff).toUInt8     -- put_byte(s, (Byte)(b & 0xff));

/-- `local void flush_pending(z_streamp strm)` -/
def flush_pending (strm : ZStreamPtr) : M Unit := do
  let s ← castDeflateState (← zrd strm (·.state))       -- deflate_state *s = strm->state;
  _tr_flush_bits s                                       -- _tr_flush_bits(s);
  let z ← ldZStream strm
  let d ← ldDeflateState s
  -- len = s->pending > strm->avail_out ? strm->avail_out : (unsigned)s->pending;
  let len : UInt32 := if d.pending > z.avail_out.toUInt64 then z.avail_out else d.pending.toUInt32
  if len == 0 then return                                -- if (len == 0) return;
  -- zmemcpy(strm->next_out, s->pending_out, len);
  memcpyB z.next_out d.pending_out len.toNat
  -- strm->next_out += len; s->pending_out += len;
  let no ← padd z.next_out len.toNat
  let po ← padd d.pending_out len.toNat
  -- strm->total_out += len; strm->avail_out -= len;
  stZStream strm { z with next_out := no, total_out := z.total_out + len.toUInt64, avail_out := z.avail_out - len }
  -- s->pending -= len;
  let pend := d.pending - len.toUInt64
  stDeflateState s { d with pending_out := po, pending := pend }
  -- if (s->pending == 0) s->pending_out = s->pending_buf;
  if pend == 0 then wr s (fun d => { d with pending_out := d.pending_buf })

/-- `FLUSH_BLOCK_ONLY(s, last)` -/
def FLUSH_BLOCK_ONLY (s : DeflateStatePtr) (last : Int32) : M Unit := do
  let d ← ldDeflateState s
  -- (s->block_start >= 0L ? (charf *)&s->window[(unsigned)s->block_start] : (charf *)Z_NULL)
  let buf ← if d.block_start ≥ 0 then padd d.window d.block_start.toUInt64.toUInt32.toNat else pure (Ptr.null : BPtr)
  -- (ulg)((long)s->strstart - s->block_start)
  let n ← lsub d.strstart.toUInt64.toInt64 d.block_start
  «_tr_flush_block» s buf n.toUInt64 last
  -- s->block_start = s->strstart;
  wr s (fun d => { d with block_start := d.strstart.toUInt64.toInt64 })
  -- flush_pending(s->strm);
  flush_pending (← rd s (·.strm))

/-- `FLUSH_BLOCK(s, last)`: the `return`s of the macro are `some state`; `none` falls through. -/
def FLUSH_BLOCK (s : DeflateStatePtr) (last : Int32) : M (Option block_state) := do
  FLUSH_BLOCK_ONLY s last
  let d ← ldDeflateState s
  if (← zrd d.strm (·.avail_out)) == 0 then
    if last == 0 then return some need_more                 -- if (!(last)) return need_more;
    if d.pending != 0 || d.wrap != 0 then return some finish_started
  return none

end Zlib.Deflate
