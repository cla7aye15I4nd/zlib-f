import ZlibF.Spec.Public.Streams
import ZlibF.Proof.«deflate.c.engine.initial»
import ZlibF.Proof.«deflate.c.engine.symbol-ledger»
import ZlibF.Proof.«deflate.c.engine.block-initial»
import ZlibF.Proof.«deflate.c.engine.chains»

/-!
# deflate.c: the universal invariant of a deflate stream

`DInv` holds in every reachable state of a deflate stream, for every level, `memLevel`,
`windowBits`, strategy, tuning and header. Batch A establishes it after `deflateInit2_` and shows
that every stream operation and caller rebuffering keep it. The engine lemmas of batches B and C
assume it at entry and give it back at exit (`docs/progress.md`, section "Core proof skeletons").

Other modules use the interface lemmas `DInv.*` and the field accessors named in the progress
list. A missing fact is not unfolded from the definition: it is reported to batch A, which adds it
here and proves that every operation keeps it.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open ZlibF.Math.DeflateSymbols
open Zlib.Deflate.Engine.Proofs.BlockInit (BlockClear)
set_option autoImplicit false

/-! ## 1. The invariant -/

/-- Scalar shape of the window, match, block and bit state (`docs/proof/deflate.md`, D).

* `blockStart`, `blockSpan`: the current block starts at most at `strstart`; at a nonzero level it
  spans at most 258 bytes per recorded symbol plus the lazy literal. `block_start` may be far
  below 0 there: `fill_window` subtracts `w_size` at every slide, also inside one block.
* `levelZero`: `deflate_stored` keeps `0 ≤ block_start`, no lookahead and no symbols.
* `available`, `pendingMatch`, `fastLazy`: the lazy match state that `deflate_slow` and
  `deflate_fast` read at entry. The distance of a pending match is computed as in C, in `uInt`:
  it may equal `MAX_DIST` (the chain head is tested with `<=`), and then the slide in
  `fill_window` wraps `match_start` below 0, which the unsigned distance absorbs.
* `biValid`: at most 7 bits wait in `bi_buf`, because every path that sends bits ends with
  `bi_flush` (`flush_pending`, `_tr_align`, `deflatePrime`) or `bi_windup`.
* `cursor`: an empty pending buffer is read from its start (`flush_pending`, `deflateResetKeep`).
* `symRoom`: one more symbol fits (`_tr_tally` reports a full buffer and the strategy flushes).
* `windowInit`: the window is written up to the end of the data (`deflateCopy` copies only
  `high_water` bytes of it).
* `headerFlush`: before the header is written, `last_flush` is the value of a reset (-2) or of a
  call that only flushed pending bits into a full output (-1); any other call writes the header
  and leaves `INIT_STATE` or `GZIP_STATE`. So an accepted call there is not refused by the
  `RANK` test and writes the header. -/
structure Shape (d : DeflateState) : Prop where
  room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat
  insert : d.insert.toNat ≤ d.strstart.toNat
  insertDone : 3 ≤ d.lookahead.toNat → d.insert = 0
  prevLength : d.prev_length.toNat ≤ 258
  matchLength : d.match_length.toNat ≤ 258
  matchAvailable : d.match_available = 0 ∨ d.match_available = 1
  blockStart : d.block_start.toInt ≤ d.strstart.toNat
  blockSpan : d.level ≠ 0 → (d.strstart.toNat : Int) - d.block_start.toInt ≤
    258 * (d.sym_next.toNat / 3 : Nat) + d.match_available.toInt
  levelZero : d.level = 0 → 0 ≤ d.block_start.toInt ∧ d.lookahead = 0 ∧ d.sym_next = 0
  available : d.match_available ≠ 0 → 1 ≤ d.strstart.toNat
  pendingMatch : 3 ≤ d.match_length.toNat →
    1 ≤ (d.strstart - 1 - d.match_start).toNat ∧
    (d.strstart - 1 - d.match_start).toNat ≤ d.w_size.toNat - 262 ∧
    d.match_length.toNat ≤ d.lookahead.toNat + 1 ∧ d.insert = 0 ∧ 1 ≤ d.strstart.toNat
  fastLazy : 1 ≤ d.level.toInt → d.level.toInt ≤ 3 → d.strategy.toInt ≠ 2 → d.strategy.toInt ≠ 3 →
    d.match_length.toNat ≤ 2 ∧ d.prev_length.toNat ≤ 2
  highWater : d.high_water.toNat ≤ d.window_size.toNat
  windowInit : d.strstart.toNat + d.lookahead.toNat ≤ d.high_water.toNat
  lastFlush : -2 ≤ d.last_flush.toInt ∧ d.last_flush.toInt ≤ 5
  headerFlush : d.status = INIT_STATE ∨ d.status = GZIP_STATE → d.last_flush = -2 ∨ d.last_flush = -1
  trailer : d.wrap.toInt < 0 → d.status = FINISH_STATE
  biValid : d.bi_valid.toInt ≤ 7
  cursor : d.pending = 0 → d.pending_out = d.pending_buf
  symRoom : d.sym_next.toNat < d.sym_end.toNat
  slides : d.«matches».toNat ≤ 2 ∧ (d.level ≠ 0 → d.«matches» = 0)
  /-- P2. A lazy `prev_length ≥ 3` exists only in `deflate_slow`, below the current match. -/
  lazyPrev : 3 ≤ d.prev_length.toNat → 4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3 ∧
    d.prev_length.toNat < d.match_length.toNat
  /-- P3. Recorded symbols cover at least one byte of the block. -/
  symBlock : d.sym_next ≠ 0 → d.block_start.toInt < d.strstart.toNat
  /-- P5. A pending lazy literal exists only in `deflate_slow`. -/
  lazyAvail : d.match_available ≠ 0 → 4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3
  /-- P6. A pending lazy literal lies inside the current block. -/
  lazyStart : d.match_available ≠ 0 → d.block_start.toInt < d.strstart.toNat

/-- The facts that hold between calls but not inside them, kept apart from `Shape` (which the
strategies, `fill_window` and `deflateSetDictionary` use at internal points): P1 and P1b fail inside
`deflateSetDictionary` (its `fill_window` runs with `last_flush = -2`), and P4 inside a strategy is
only true because `deflate` never runs one on a finished stream. -/
structure CallFacts (d : DeflateState) : Prop where
  /-- P1: no lookahead, no symbols, no lazy state, a nonnegative block start (`lm_init`,
  `deflateSetDictionary`). -/
  fresh : d.last_flush = -2 → d.lookahead = 0 ∧ d.sym_next = 0 ∧ d.match_available = 0 ∧
    d.match_length.toNat ≤ 2 ∧ d.prev_length.toNat ≤ 2 ∧ 0 ≤ d.block_start.toInt
  /-- P1b: the block starts at `strstart`. -/
  freshStart : d.last_flush = -2 → d.block_start.toInt = d.strstart.toNat
  /-- P4: a finished stream has no symbols. -/
  finishSym : d.status = FINISH_STATE → d.sym_next = 0
  /-- A finished stream has no lookahead: deflate sets `FINISH_STATE` only after a strategy has
  consumed all of it (the loops end on `lookahead = 0`; `deflate_stored` keeps none), and a finished
  stream refuses new input. Checked on the real C (`tests/goals/deflate/invariant.c`). -/
  finishLook : d.status = FINISH_STATE → d.lookahead = 0

/-- The insertion frontier: no position at or above it has been inserted. The positions from
`strstart - insert` on wait for insertion, and a position is inserted only once its three bytes
are in the window, so none of the last two bytes of the data is inserted either. -/
def chainTop (d : DeflateState) : Nat :=
  min (d.strstart.toNat - d.insert.toNat) (d.strstart.toNat + d.lookahead.toNat - 2)

/-- H1/H2 (`docs/proof/deflate.md`): the hash chains name inserted positions below the
insertion frontier `chainTop`, for every content of the unwritten `prev` slots. -/
def Chains (h : Heap) (d : DeflateState) : Prop :=
  HeapChains h d (chainTop d)

/-- A higher frontier keeps the chains. -/
theorem chains_up {h : Heap} {d : DeflateState} {top next : Nat}
    (chains : HeapChains h d top) (ordered : top ≤ next) : HeapChains h d next := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, chains_mono H ordered (Nat.le_refl _)⟩

theorem chainTop_le (d : DeflateState) : chainTop d ≤ d.strstart.toNat - d.insert.toNat := Nat.min_le_left _ _

/-- The chains as they will be once `slide_hash` has run: every `head` and `prev` entry read
through `slideVal`. At level 0, `deflate_stored` slides the window without the tables and counts
the slides in `matches`; `deflateParams` repairs one slide with `slide_hash` and more with
`CLEAR_HASH`. -/
def SlidChains (h : Heap) (d : DeflateState) : Prop :=
  ∃ w p q wa pa qa,
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    HashChains (fun i => slideVal d.w_size (wfn qa i)) (fun i => slideVal d.w_size (wfn pa i))
      (bfn wa) d.hash_size d.hash_shift d.hash_mask d.w_size.toNat
      (d.strstart.toNat - d.insert.toNat) (d.strstart.toNat + d.lookahead.toNat)

/-- The rolling hash at `strstart` has taken in the first two bytes of the lookahead. -/
def RollingHash (h : Heap) (d : DeflateState) : Prop :=
  ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧
    InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h

/-- The hash state between calls: chains (exact, or repairable by one slide at level 0 after
one stored slide; nothing at level 0 after more), and the rolling hash once there is lookahead,
except under `Z_HUFFMAN_ONLY` and `Z_RLE`: `deflate_huff` and `deflate_rle` advance `strstart`
without updating `ins_h`. A switch to a hashing strategy goes through a flush that leaves no
lookahead (`deflateParams`), and `fill_window` restores the form. -/
structure Hashing (h : Heap) (d : DeflateState) : Prop where
  chains : d.«matches» = 0 → Chains h d
  slid : d.«matches» = 1 → SlidChains h d
  rolling : d.strategy.toInt ≠ 2 → d.strategy.toInt ≠ 3 → 3 ≤ d.lookahead.toNat → RollingHash h d

/-- The state right after `INSERT_STRING` at `strstart` has returned `cur`: the chains include
`strstart`, the head of its key is `strstart`, and its `prev` slot holds `cur`. This is the
entry condition of `longest_match` inside the strategies. -/
def Inserted (h : Heap) (d : DeflateState) (cur : Nat) : Prop :=
  HeapChains h d (d.strstart.toNat + 1) ∧
  ∃ w p q wa pa qa,
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    (wfn qa (hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat).toNat).toNat = d.strstart.toNat ∧
    (wfn pa (d.strstart.toNat &&& (d.w_size.toNat - 1))).toNat = cur

/-- The recorded symbols of the current block: the bytes of `sym_buf` and the leaf frequencies of
`dyn_ltree` and `dyn_dtree` describe the same list `xs` (`SymbolLedger`). -/
def Recorded (h : Heap) (d : DeflateState) (xs : List Symbol) : Prop :=
  ∃ b a, d.pending_buf = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ SymbolLedger a d xs

/-- Between calls the recorded symbols are counted in the tree frequencies, their distances are
within `MAX_DIST`, the block costs and the bit-length frequencies are clear (`init_block`; only
`_tr_flush_block` adds to them, and it ends with `init_block`), and the pending bytes lie below
the symbols (F9 at a call boundary). -/
structure Symbols (h : Heap) (d : DeflateState) : Prop where
  recorded : ∃ xs, Recorded h d xs ∧ ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262
  clear : BlockClear d
  below : ∀ b off, d.pending_out = .ref (.blk b) off → d.sym_next ≠ 0 →
    off + d.pending.toNat ≤ d.lit_bufsize.toNat

/-- **The header facts of a call boundary**, kept beside `DInv` (the strategies, which run in
`BUSY_STATE` and `FINISH_STATE` only, do not carry them). The header states: no symbol is recorded before the header is written (the header stages
fill `pending_buf`, which the symbols share), and a state writing the gzip header from a
caller's record keeps that record (`deflateSetHeader` is called only before `deflate` starts,
`DeflateNotStarted`; only the record branch of the gzip stage enters `EXTRA_STATE`). -/
structure HeaderInv (d : DeflateState) : Prop where
  empty : d.status = INIT_STATE ∨ d.status = GZIP_STATE ∨ d.status = EXTRA_STATE ∨ d.status = NAME_STATE ∨
    d.status = COMMENT_STATE ∨ d.status = HCRC_STATE → d.sym_next = 0
  record : d.status = EXTRA_STATE ∨ d.status = NAME_STATE ∨ d.status = COMMENT_STATE ∨
    d.status = HCRC_STATE → d.gzhead ≠ none

/-- Outside the header states the header facts say nothing. -/
theorem HeaderInv.of_busy {d : DeflateState} (busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE) :
    HeaderInv d := by
  constructor <;> intro e <;> exfalso <;> rcases busy with b | b <;> rw [b] at e <;> revert e <;> decide

/-- A state with the same status, symbol count and header record keeps the header facts. -/
theorem HeaderInv.keep {d d' : DeflateState} (header : HeaderInv d) (status : d'.status = d.status)
    (symbols : d'.sym_next = d.sym_next) (gzhead : d'.gzhead = d.gzhead) : HeaderInv d' :=
  ⟨fun e => by rw [symbols]; exact header.empty (status ▸ e),
    fun e => by rw [gzhead]; exact header.record (status ▸ e)⟩

/-- **The universal invariant of a deflate stream.** Parametric in level, `memLevel`,
`windowBits`, strategy, tuning and header. Use the interface lemmas, not the fields. -/
structure DInv (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  good : DGood h r ds z d
  alloc : DefAlloc z
  globals : LibraryGlobals h
  shape : Shape d
  hashing : Hashing h d
  symbols : Symbols h d

/-! ## 2. Interface of the invariant -/

theorem DInv.dgood {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : DGood h r ds z d := inv.good

theorem DInv.defAlloc {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : DefAlloc z := inv.alloc

/-- The static tables (CRC, trees, inflate) are the initial ones; `read_buf` with `wrap = 2`
reads the CRC tables. No stream operation writes them. -/
theorem DInv.libraryGlobals {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : LibraryGlobals h := inv.globals

theorem DInv.shape' {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : Shape d := inv.shape

theorem DInv.hashing' {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : Hashing h d := inv.hashing

/-- Off level 0 the chains are exact. -/
theorem DInv.chains {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level : d.level ≠ 0) : Chains h d :=
  inv.hashing.chains (inv.shape.slides.2 level)

theorem DInv.blockClear {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : BlockClear d := inv.symbols.clear

/-- The symbol ledger of the current block, with the distance bound. -/
theorem DInv.recorded {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) :
    ∃ xs, Recorded h d xs ∧ ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262 :=
  inv.symbols.recorded

/-- Between calls at most 7 bits wait in the bit buffer. -/
theorem DInv.bi_valid_le {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : 0 ≤ d.bi_valid.toInt ∧ d.bi_valid.toInt ≤ 7 :=
  ⟨inv.good.inv.bits.1, inv.shape.biValid⟩

/-- The stream record, the state block and the state are determined by the heap. -/
theorem DInv.unique {h : Heap} {r : ZStreamRef} {ds i : Nat} {z z' : ZStream}
    {d s : DeflateState} (inv : DInv h r ds z d) (good : DGood h r i z' s) :
    i = ds ∧ z' = z ∧ s = d := by
  have zs : z' = z := Option.some.inj (good.live.hz.symm.trans inv.good.live.hz)
  subst zs
  have is : i = ds := by
    have := good.live.zst.symm.trans inv.good.live.zst
    simpa only [Option.some.injEq, StateRef.deflate.injEq] using this
  subst is
  exact ⟨rfl, rfl, Option.some.inj (good.live.hs.symm.trans inv.good.live.hs)⟩

/-! ## 3. Shared statement parts of the engine lemmas -/

/-- What `deflate` has checked before it calls a strategy (`deflate.c`, `deflate`): the
refusals of a `NULL` output, of input without a pointer and of a full output, the pending
flush (a strategy starts with an empty pending buffer), and the status. -/
structure StrategyEntry (h : Heap) (r : ZStreamRef) (z : ZStream) (d : DeflateState) : Prop where
  buffers : StreamBuffers h r
  out : z.next_out ≠ .null
  input : z.avail_in ≠ 0 → z.next_in ≠ .null
  room : z.avail_out ≠ 0
  pending : d.pending = 0
  busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE

/-- What a callee of `deflate` changes besides the state: input and output accounting with the
totals, writes only to the stream's blocks and the delivered output range, no allocation. -/
def CallFrame (h after : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) (z z' : ZStream)
    (used produced : Nat) : Prop :=
  StreamAccounting z z' used produced ∧
  z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
  BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] ∧
  LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc

/-- The window side of the state, which a block flush keeps: the match and hash fields, the
tuning, and the contents of `window`, `prev` and `head`. -/
structure WindowSide (h after : Heap) (d d' : DeflateState) : Prop where
  strstart : d'.strstart = d.strstart
  lookahead : d'.lookahead = d.lookahead
  insert : d'.insert = d.insert
  ins_h : d'.ins_h = d.ins_h
  matchLength : d'.match_length = d.match_length
  matchStart : d'.match_start = d.match_start
  matchAvailable : d'.match_available = d.match_available
  prevLength : d'.prev_length = d.prev_length
  prevMatch : d'.prev_match = d.prev_match
  level : d'.level = d.level
  strategy : d'.strategy = d.strategy
  tuning : d'.max_chain_length = d.max_chain_length ∧ d'.max_lazy_match = d.max_lazy_match ∧
    d'.good_match = d.good_match ∧ d'.nice_match = d.nice_match
  sizes : d'.w_size = d.w_size ∧ d'.w_mask = d.w_mask ∧ d'.window_size = d.window_size ∧
    d'.hash_size = d.hash_size ∧ d'.hash_mask = d.hash_mask ∧ d'.hash_shift = d.hash_shift
  blocks : d'.window = d.window ∧ d'.prev = d.prev ∧ d'.head = d.head
  highWater : d'.high_water = d.high_water
  slides : d'.«matches» = d.«matches» ∧ d'.slid = d.slid
  stream : d'.strm = d.strm ∧ d'.status = d.status ∧ d'.wrap = d.wrap ∧ d'.last_flush = d.last_flush ∧
    d'.gzhead = d.gzhead ∧ d'.gzindex = d.gzindex
  buffers : d'.pending_buf = d.pending_buf ∧ d'.sym_buf = d.sym_buf ∧
    d'.lit_bufsize = d.lit_bufsize ∧ d'.sym_end = d.sym_end ∧ d'.pending_buf_size = d.pending_buf_size
  contents : ∀ b, (d.window = .ref (.blk b) 0 → after.bytes b = h.bytes b) ∧
    (d.prev = .ref (.blk b) 0 ∨ d.head = .ref (.blk b) 0 → after.words b = h.words b)

/-- What `FLUSH_BLOCK_ONLY` reads: the block part of the invariant. It holds inside the
strategies at every `FLUSH_BLOCK`, where the call-boundary facts of `DInv` may not (the symbol
buffer may be full, `strstart` may not yet have passed the lazy literal). -/
structure BlockState (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  good : DGood h r ds z d
  alloc : DefAlloc z
  room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat
  blockStart : d.block_start.toInt ≤ d.strstart.toNat
  biValid : d.bi_valid.toInt ≤ 7
  cursor : d.pending = 0 → d.pending_out = d.pending_buf
  symbols : Symbols h d

theorem DInv.block {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : BlockState h r ds z d :=
  ⟨inv.good, inv.alloc, inv.shape.room, inv.shape.blockStart, inv.shape.biValid, inv.shape.cursor,
    inv.symbols⟩

end Zlib.Deflate.Universal
