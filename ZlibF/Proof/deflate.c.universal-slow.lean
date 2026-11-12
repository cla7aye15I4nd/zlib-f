import ZlibF.Proof.«deflate.c.universal-strategy-specs»
import ZlibF.Proof.«deflate.c.universal-privm»
import ZlibF.Proof.«deflate.c.engine.short-match-frontier-loop»
import ZlibF.Proof.«deflate.c.engine.short-match-frontier»
import ZlibF.Proof.«deflate.c.borrow-stable-strategies»

/-!
# deflate.c, universal engine: `deflate_slow`

Batch B of the deflate skeleton. `deflate_slow` (levels 4 to 9, strategies other than
`Z_HUFFMAN_ONLY` and `Z_RLE`) looks one position ahead: the match found at `strstart - 1`
(`prev_length`, `prev_match`) is emitted only if the match at `strstart` is not longer; otherwise
the byte at `strstart - 1` is emitted as a literal (`match_available`). The lazy state between
iterations is part of `DInv` (`Shape.available`, `Shape.pendingMatch`, `Shape.blockSpan`).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The levels and strategies `deflate_slow` serves. -/
def SlowKind (d : DeflateState) : Prop :=
  4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3

theorem slow_kind_keep : ∀ d d' : DeflateState, d'.strategy = d.strategy → d'.level = d.level →
    SlowKind d → SlowKind d' := by
  intro d d' es el k
  unfold SlowKind at *
  rw [es, el]; exact k

open Zlib.Deflate.BorrowProofs in
theorem stable_slowSearch (ds : Nat) : C.LibcBorrow.StableM (slowSearch (some (.tab ds))) := by
  unfold slowSearch slowFind
  repeat' strategy_borrow_step

/-- What the search of `deflate_slow` leaves. -/
structure SlowOut (h h2 : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d d2 : DeflateState) : Prop where
  good : DGood h2 r ds z d2
  update : EngineUpdate d d2
  strstart : d2.strstart = d.strstart
  lookahead : d2.lookahead = d.lookahead
  insert : d2.insert = d.insert
  available : d2.match_available = d.match_available
  prevLength : d2.prev_length = d.match_length
  prevMatch : d2.prev_match = d.match_start
  bytes : h2.bytes = h.bytes
  frame : ByteFrame h h2 (fun i => i = ds)
  borrow : h2.libcErrorBorrow = h.libcErrorBorrow
  chains : HeapChains h2 d2 (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else chainTop d)
  form : 3 ≤ d.lookahead.toNat → ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧
    InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d2.ins_h
  matchShape : d2.match_length.toNat ≤ 258
  matchLook : d2.match_length.toNat ≤ d.lookahead.toNat ∨ d2.match_length.toNat = 2
  matched : 3 ≤ d2.match_length.toNat → d.match_length.toNat < d2.match_length.toNat →
    ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧
      GoodMatch wa d.strstart.toNat d.w_size.toNat d2.match_start.toNat d2.match_length.toNat
  priv : PrivStep h h2 r ds d

set_option maxHeartbeats 2000000 in
/-- **The search of `deflate_slow`**: insertion at `strstart`, the lazy fields, the conditional
`longest_match` and the short-match filter. -/
theorem slow_search_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head SlowKind h r ds z d) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ hh h2 d2, slowSearch (some (.tab ds)) h = .ok (hh, h2) ∧ SlowOut h h2 r ds z d d2 := by
  have inv := head.inv
  have good := inv.good
  have shape := inv.shape
  obtain ⟨_, s2, s3⟩ := head.kind
  by_cases ready : 3 ≤ d.lookahead.toNat
  · obtain ⟨w, p, q, wa, pa, qa, env, H⟩ := heap_chains_environment good (inv.chains head.level)
    obtain ⟨w0, wa0, win0, get0, form⟩ := inv.hashing.rolling s2 s3 ready
    have wid : w0 = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans env.wbytes)
    subst wa0
    obtain ⟨key, after, pos, len, run, goodA, chainsA, lenBound, lenLook, evidence, bytesA, nextForm, frameA, heapA⟩ :=
      slow_search_room_storage good env H (by have := chainTop_le d; omega) shape.room ready room
        shape.matchLength form
    have borrowA : after.libcErrorBorrow = h.libcErrorBorrow := stable_slowSearch ds h _ after run
    refine ⟨_, after, _, run, ⟨goodA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, bytesA, frameA, borrowA,
      by rw [if_pos ready]; exact chainsA, fun _ => ⟨w, wa, env.win, env.wbytes, nextForm⟩, lenBound,
      Or.inl lenLook, fun large longer => ⟨w, wa, env.win, env.wbytes, evidence large longer⟩, ?_⟩⟩
    obtain ⟨e, rfl⟩ := heapA
    exact (priv_inserted key good.live.hs env).trans
      (priv_setD _ r ds d e (show (insertedHeap h ds p q d pa qa key).dstates ds = some { d with ins_h := key } by
        simp [insertedHeap]))
  · obtain ⟨run, goodA, chainsA, frameA⟩ := slow_search_fewer_three good (inv.chains head.level) (by omega)
    refine ⟨0, _, lazyPrepare d, run, ⟨goodA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, frameA, rfl,
      by rw [if_neg ready]; exact chainsA, fun r3 => absurd r3 ready, by show (2 : UInt32).toNat ≤ 258; decide,
      Or.inr rfl, fun (large : 3 ≤ (2 : UInt32).toNat) => absurd large (by decide),
      priv_setD h r ds d _ good.live.hs⟩⟩


/-! ## The decision -/

/-- The literal at `strstart - 1` that a match did not replace. -/
def slowPending (s : DeflateStatePtr) (st : LoopS) (hash_head : UInt32) (d : DeflateState) : M LoopS := do
  let c ← index8 d.window (d.strstart - 1).toNat
  let bflush ← tally_lit s c
  if bflush then FLUSH_BLOCK_ONLY s 0
  wr s (fun d => { d with strstart := d.strstart + 1, lookahead := d.lookahead - 1 })
  if (← zrd d.strm (·.avail_out)) == 0 then return { st with hash_head, bflush, ret := some need_more }
  return { st with hash_head, bflush }

theorem slow_decision_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    slowDecision s flush st hash_head = (do
      let d ← ldDeflateState s
      if d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length then
        let bflush ← tally_dist s (d.strstart - 1 - d.prev_match) (d.prev_length - MIN_MATCH_u)
        let hh ← slowMatchAdvance s (d.strstart + d.lookahead - MIN_MATCH_u) hash_head
        lazyTail s st hh bflush
      else if d.match_available != 0 then slowPending s st hash_head d
      else
        wr s (fun d => { d with match_available := 1, strstart := d.strstart + 1, lookahead := d.lookahead - 1 })
        return { st with hash_head, bflush := false }) := by
  unfold slowDecision slowPending lazyTail
  simp only [Zlib.Deflate.Engine.Proofs.M_bind_assoc, Zlib.Deflate.Engine.Proofs.M_pure_bind, fill_ite_bind]
  rfl


/-- A state reached from the search by engine-field writes keeps the invariant once its shape and
hash state are shown; the caller ranges are kept. -/
theorem engine_after_search {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d2 d3 : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : SlowOut h h2 r ds z d d2)
    (update : EngineUpdate d2 d3) (shape : Shape d3) (hashing : Hashing (setD h2 ds d3) d3) :
    DInv (setD h2 ds d3) r ds z d3 ∧ StreamBuffers (setD h2 ds d3) r := by
  have good := engine_update_good out.good update
  have upd := out.update
  refine ⟨⟨good, inv.alloc, by unfold LibraryGlobals; rw [show (setD h2 ds d3).static = h.static from out.frame.static]; exact inv.globals,
    shape, hashing, ?_⟩, ?_⟩
  · obtain ⟨⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
    rw [update, upd]
    exact ⟨⟨xs, ⟨b, a, pbuf, by rw [setD_bytes, out.bytes]; exact get, ledger.keep rfl rfl rfl rfl⟩, dist⟩,
      ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩
  · obtain ⟨win, prev, hd, pb⟩ : d3.window = d.window ∧ d3.prev = d.prev ∧ d3.head = d.head ∧
        d3.pending_buf = d.pending_buf := by rw [update, upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz good.live.hz buffers
      (out.frame.trans (byte_frame_setD h2 ds d3))
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good good win prev hd pb) (stream_accounting_self z) out.borrow

/-- The state after `match_available = 1; strstart++; lookahead--`. -/
def markState (d2 : DeflateState) : DeflateState :=
  { d2 with match_available := 1, strstart := d2.strstart + 1, lookahead := d2.lookahead - 1 }

set_option maxHeartbeats 4000000 in
/-- **No match is emitted and no literal is pending**: the byte at `strstart` becomes the pending
literal. -/
theorem slow_mark {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d2 : DeflateState}
    (head : Head SlowKind h r ds z d) (look : 1 ≤ d.lookahead.toNat) (out : SlowOut h h2 r ds z d d2)
    (noMatch : ¬ (3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat))
    (idle : d2.match_available = 0) :
    wr (some (.tab ds)) (fun d => { d with match_available := 1, strstart := d.strstart + 1, lookahead := d.lookahead - 1 }) h2 =
        .ok ((), setD h2 ds (markState d2)) ∧
      DInv (setD h2 ds (markState d2)) r ds z (markState d2) ∧ StreamBuffers (setD h2 ds (markState d2)) r := by
  have inv := head.inv
  have shape := inv.shape
  have upd := out.update
  refine ⟨by rw [wrD_eq, out.good.live.hs]; rfl, ?_⟩
  have ssLt := d.strstart.toNat_lt
  have room := shape.room
  have wsz := inv.good.inv.wsz
  have wsHi := (slide_window_sizes inv.good).2
  have eSs := out.strstart
  have eLa := out.lookahead
  have eIns := out.insert
  have ss3 : (markState d2).strstart.toNat = d.strstart.toNat + 1 := by
    show (d2.strstart + 1).toNat = _; rw [eSs, UInt32.toNat_add]; simp; omega
  have la3 : (markState d2).lookahead.toNat = d.lookahead.toNat - 1 := by
    show (d2.lookahead - 1).toNat = _; rw [eLa]
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))
  have ePl : d2.prev_length = d.match_length := out.prevLength
  have eMa : d2.match_available = d.match_available := out.available
  have level4 : 4 ≤ d.level.toInt := head.kind.1
  have dist : 3 ≤ d2.match_length.toNat → 1 ≤ ((markState d2).strstart - 1 - (markState d2).match_start).toNat ∧
      ((markState d2).strstart - 1 - (markState d2).match_start).toNat ≤ (markState d2).w_size.toNat - 262 ∧
      d2.match_length.toNat ≤ (markState d2).lookahead.toNat + 1 ∧ (markState d2).insert = 0 ∧
      1 ≤ (markState d2).strstart.toNat := by
    intro large
    have longer : d.match_length.toNat < d2.match_length.toNat := by
      rw [ePl] at noMatch; omega
    obtain ⟨w, wa, win, get, good⟩ := out.matched large longer
    obtain ⟨lt, far, _, _⟩ := good
    have back : (markState d2).strstart - 1 = d2.strstart := by
      show d2.strstart + 1 - 1 = d2.strstart; simp
    rw [back, eSs]
    have ws2 : (markState d2).w_size = d.w_size := by show d2.w_size = d.w_size; rw [upd]
    rw [ws2, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by show d2.match_start.toNat ≤ _; omega))]
    have lk : d2.match_length.toNat ≤ d.lookahead.toNat := by
      rcases out.matchLook with l | two
      · exact l
      · omega
    refine ⟨by show 1 ≤ d.strstart.toNat - d2.match_start.toNat; omega,
      by show d.strstart.toNat - d2.match_start.toNat ≤ _; omega, by rw [la3]; omega,
      by show d2.insert = 0; rw [eIns]; exact shape.insertDone (by omega), by rw [ss3]; omega⟩
  have shapeA : Shape (markState d2) := by
    have kLv : d2.level = d.level := by rw [upd]
    have kSt : d2.strategy = d.strategy := by rw [upd]
    have bsLt : d2.block_start.toInt < ((markState d2).strstart.toNat : Int) := by
      rw [show d2.block_start = d.block_start by rw [upd], ss3]; have := shape.blockStart; omega
    have lazyK : 4 ≤ (markState d2).level.toInt ∧ (markState d2).strategy.toInt ≠ 2 ∧
        (markState d2).strategy.toInt ≠ 3 := by
      show 4 ≤ d2.level.toInt ∧ d2.strategy.toInt ≠ 2 ∧ d2.strategy.toInt ≠ 3
      rw [kLv, kSt]; exact head.kind
    refine ⟨?_, ?_, ?_, ?_, out.matchShape, Or.inr rfl, ?_, ?_, ?_, ?_, dist, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun large => ⟨lazyK.1, lazyK.2.1, lazyK.2.2, by
        change 3 ≤ d2.prev_length.toNat at large; show d2.prev_length.toNat < d2.match_length.toNat; omega⟩,
      fun _ => bsLt, fun _ => lazyK, fun _ => bsLt⟩
    · rw [ss3, la3]; show _ ≤ d2.window_size.toNat; rw [show d2.window_size = d.window_size by rw [upd]]; omega
    · rw [ss3]; show d2.insert.toNat ≤ _; rw [eIns]; have := shape.insert; omega
    · intro large; rw [la3] at large; show d2.insert = 0; rw [eIns]; exact shape.insertDone (by omega)
    · show d2.prev_length.toNat ≤ 258; rw [ePl]; exact shape.matchLength
    · show d2.block_start.toInt ≤ _; rw [show d2.block_start = d.block_start by rw [upd], ss3]
      have := shape.blockStart; omega
    · intro levelNe
      show ((markState d2).strstart.toNat : Int) - d2.block_start.toInt ≤ 258 * (d2.sym_next.toNat / 3 : Nat) +
        (1 : Int32).toInt
      rw [ss3, show d2.block_start = d.block_start by rw [upd], show d2.sym_next = d.sym_next by rw [upd]]
      have span := shape.blockSpan head.level
      rw [← eMa, idle] at span
      have z0 : (0 : Int32).toInt = 0 := rfl
      have o1 : (1 : Int32).toInt = 1 := rfl
      rw [z0] at span; rw [o1]; push_cast; omega
    · intro zero; change d2.level = 0 at zero; rw [show d2.level = d.level by rw [upd]] at zero; exact absurd zero head.level
    · intro _; rw [ss3]; omega
    · intro lo hi
      exfalso
      have e : (markState d2).level = d.level := by show d2.level = d.level; rw [upd]
      rw [e] at hi; omega
    · show d2.high_water.toNat ≤ d2.window_size.toNat
      rw [show d2.high_water = d.high_water by rw [upd], show d2.window_size = d.window_size by rw [upd]]
      exact shape.highWater
    · rw [ss3, la3]; show _ ≤ d2.high_water.toNat; rw [show d2.high_water = d.high_water by rw [upd]]
      have := shape.windowInit; omega
    · show -2 ≤ d2.last_flush.toInt ∧ d2.last_flush.toInt ≤ 5; rw [show d2.last_flush = d.last_flush by rw [upd]]; exact shape.lastFlush
    · show d2.status = INIT_STATE ∨ d2.status = GZIP_STATE → d2.last_flush = -2 ∨ d2.last_flush = -1
      rw [show d2.status = d.status by rw [upd], show d2.last_flush = d.last_flush by rw [upd]]; exact shape.headerFlush
    · show d2.wrap.toInt < 0 → d2.status = FINISH_STATE
      rw [show d2.wrap = d.wrap by rw [upd], show d2.status = d.status by rw [upd]]; exact shape.trailer
    · show d2.bi_valid.toInt ≤ 7; rw [show d2.bi_valid = d.bi_valid by rw [upd]]; exact shape.biValid
    · show d2.pending = 0 → d2.pending_out = d2.pending_buf
      rw [show d2.pending = d.pending by rw [upd], show d2.pending_out = d.pending_out by rw [upd],
        show d2.pending_buf = d.pending_buf by rw [upd]]; exact shape.cursor
    · show d2.sym_next.toNat < d2.sym_end.toNat
      rw [show d2.sym_next = d.sym_next by rw [upd], show d2.sym_end = d.sym_end by rw [upd]]; exact shape.symRoom
    · show d2.«matches».toNat ≤ 2 ∧ (d2.level ≠ 0 → d2.«matches» = 0)
      rw [show d2.«matches» = d.«matches» by rw [upd], show d2.level = d.level by rw [upd]]; exact shape.slides
  have hashingA : Hashing (setD h2 ds (markState d2)) (markState d2) := by
    have chains := out.chains
    refine ⟨fun _ => ?_, fun one => ?_, fun _ _ large => ?_⟩
    · obtain ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, H⟩ := chains
      refine ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, ?_⟩
      apply chains_mono H _ (by show _ ≤ (markState d2).strstart.toNat + (markState d2).lookahead.toNat; rw [ss3, la3, eSs, eLa]; omega)
      change _ ≤ min ((markState d2).strstart.toNat - d2.insert.toNat)
        ((markState d2).strstart.toNat + (markState d2).lookahead.toNat - 2)
      rw [ss3, la3, eIns]
      by_cases ready : 3 ≤ d.lookahead.toNat
      · rw [if_pos ready]
        have z0 : d.insert.toNat = 0 := by rw [shape.insertDone ready]; rfl
        omega
      · rw [if_neg ready]; unfold chainTop; omega
    · have zero := shape.slides.2 head.level
      change d2.«matches» = 1 at one
      rw [show d2.«matches» = d.«matches» by rw [upd], zero] at one; cases one
    · change 3 ≤ (markState d2).lookahead.toNat at large
      rw [la3] at large
      obtain ⟨w, wa, win, get, form⟩ := out.form (by omega)
      refine ⟨w, wa, by show d2.window = _; rw [show d2.window = d.window by rw [upd]]; exact win,
        by rw [setD_bytes, out.bytes]; exact get, ?_⟩
      show InsHForm d2.hash_shift d2.hash_mask (bfn wa) (markState d2).strstart.toNat d2.ins_h
      rw [ss3, show d2.hash_shift = d.hash_shift by rw [upd], show d2.hash_mask = d.hash_mask by rw [upd]]
      exact form
  exact engine_after_search inv head.buffers out rfl shapeA hashingA


/-! ## A block flush whose state is advanced afterwards

In `deflate_slow` the pending literal is tallied and the block flushed before `strstart` moves
past it; the state at the flush is not a call-boundary state (the lazy match is measured from the
next position). This flush lemma gives the parts of the invariant without the shape. -/

/-- What a strategy has at a flush whose state is advanced afterwards. -/
structure BlockLax (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (pb : Nat) (buf : Array UInt8) (xs : List Symbol) : Prop where
  good : DGood h r ds z d
  alloc : DefAlloc z
  globals : LibraryGlobals h
  trees : TreesInvAt h ds d pb buf
  ledger : SymbolLedger buf d xs
  clear : BlockInit.BlockClear d
  pending : d.pending = 0
  blockLow : -(2 : Int) ^ 62 ≤ d.block_start.toInt
  blockHigh : d.block_start.toInt ≤ d.strstart.toNat
  level : d.level ≠ 0
  buffers : StreamBuffers h r
  out : z.next_out ≠ .null
  room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat
  cursor : d.pending = 0 → d.pending_out = d.pending_buf
  biValid : d.bi_valid.toInt ≤ 7

set_option maxHeartbeats 1600000 in
theorem flush_block_lax (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (ready : BlockLax h r ds z d pb buf xs) (last : Bool) :
    ∃ produced after z' result,
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (result.pending = 0 ∨ z'.avail_out = 0) ∧ (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      result.bi_valid.toInt < 8 ∧ Block.FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.«matches» = 0 ∧ BlockInit.BlockClear result ∧
      (∃ b a, result.pending_buf = .ref (.blk b) 0 ∧ after.bytes b = some a ∧ SymbolLedger a result []) ∧
      after.static = h.static ∧ (∀ top, HeapChains h d top → HeapChains after result top) ∧
      (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧ z'.total_in = z.total_in ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] ∧
      Zlib.Deflate.Proofs.Shape h after ∧ Keys d result := by
  have good := ready.good
  obtain ⟨ob, pointer⟩ := output_reference good.live.hz ready.buffers ready.out
  obtain ⟨w, wa, win, get, size⟩ := window_block good
  have levelPos : 0 < d.level.toInt := by
    have lo := good.inv.level_lo
    have ne : d.level.toInt ≠ 0 := by
      intro zero; exact ready.level (Int32.toInt_inj.mp (by rw [zero]; rfl))
    omega
  have range : d.strstart.toNat ≤ d.window_size.toNat := by have := ready.room; omega
  obtain ⟨produced, after, z', result, run, goodA, buffersA, account, sizes, storage, clearA, ⟨bA, ledgerA⟩,
      bitsA, _, cursorA, frame, drained, matchesA, totalA, bufferA, totalInA⟩ :=
    safe good ready.trees ready.buffers levelPos pointer (ready.cursor ready.pending) ready.pending
      ready.biValid ready.ledger ready.clear win get ready.blockLow ready.blockHigh range last
  have frameW := frame.work
  have pbuf := ready.trees.base.pbuf
  have fpb : result.pending_buf = d.pending_buf := by
    have e := frame; unfold Block.FlushFrame at e; exact (congrArg DeflateState.pending_buf e).trans rfl
  obtain ⟨pbA, pbAget⟩ : ∃ a, after.bytes pb = some a := by
    have g : Space.get h (BRef.blk pb) = some buf := by simpa using ready.trees.base.bytes
    obtain ⟨next, getN, _⟩ := sizes.get (.blk pb) buf g
    exact ⟨next, by simpa using getN⟩
  refine ⟨produced, after, z', result, run, goodA, buffersA, account, drained, cursorA, bitsA, frame, matchesA,
    clearA, ⟨pb, pbA, by rw [fpb]; exact pbuf, pbAget, ledger_empty_any ledgerA⟩, storage.frame.1.symm, ?_, ?_, totalA, totalInA, bufferA, storage.shape, ?_⟩
  · intro top chains
    rcases pointer with ⟨oo, p⟩ | ⟨oo, p⟩
    · exact flush_frames_chains storage good ready.buffers p pbuf frameW chains
    · exact foreign_flush_frames_chains storage good ready.buffers p pbuf frameW chains
  · intro w0 win0
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst we
    obtain ⟨wp, pp, qp, b0, blocks⟩ := good.inv.blocks
    obtain ⟨pa, getP, _⟩ := blocks.pa
    obtain ⟨qa, getQ, _⟩ := blocks.qa
    have we : wp = w0 := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    subst wp
    rw [get]
    rcases pointer with ⟨oo, p⟩ | ⟨oo, p⟩
    · exact (storage.private_arrays good ready.buffers p win get blocks.prev getP blocks.head getQ pbuf).1
    · exact (storage.foreign_private_arrays good ready.buffers p win get blocks.prev getP blocks.head getQ pbuf).1
  · have e := frame
    unfold Block.FlushFrame at e
    exact ⟨(congrArg DeflateState.window e).trans rfl, (congrArg DeflateState.prev e).trans rfl,
      (congrArg DeflateState.head e).trans rfl, (congrArg DeflateState.pending_buf e).trans rfl,
      (congrArg DeflateState.status e).trans rfl, (congrArg DeflateState.last_flush e).trans rfl,
      (congrArg DeflateState.wrap e).trans rfl, (congrArg DeflateState.level e).trans rfl,
      (congrArg DeflateState.strategy e).trans rfl⟩


/-! ## The shape after a lazy step -/

/-- The pending match after a step past the literal at `strstart`. -/

theorem slow_dist {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d2 F : DeflateState}
    (out : SlowOut h h2 r ds z d d2) (look : 1 ≤ d.lookahead.toNat)
    (noMatch : ¬ (3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat))
    (eSs : F.strstart = d2.strstart + 1) (eMs : F.match_start = d2.match_start) (eW : F.w_size = d.w_size)
    (eLa : F.lookahead.toNat = d.lookahead.toNat - 1) (ssLt : d.strstart.toNat + 1 < 2 ^ 32) :
    3 ≤ d2.match_length.toNat → 1 ≤ (F.strstart - 1 - F.match_start).toNat ∧
      (F.strstart - 1 - F.match_start).toNat ≤ F.w_size.toNat - 262 ∧
      d2.match_length.toNat ≤ F.lookahead.toNat + 1 := by
  intro large
  have longer : d.match_length.toNat < d2.match_length.toNat := by
    rw [out.prevLength] at noMatch; omega
  obtain ⟨w, wa, win, get, good⟩ := out.matched large longer
  obtain ⟨lt, far, _, _⟩ := good
  have back : F.strstart - 1 = d.strstart := by rw [eSs, out.strstart]; simp
  rw [back, eMs, eW, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]
  have lk : d2.match_length.toNat ≤ d.lookahead.toNat := by
    rcases out.matchLook with l | two
    · exact l
    · omega
  refine ⟨by omega, by omega, by rw [eLa]; omega⟩

/-- The shape of the state after a lazy step past the literal at `strstart`, with a pending
literal, from the shape before and the fields of the step. -/
theorem slow_shape {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d2 F : DeflateState}
    (shape : Shape d) (kind : SlowKind d) (level : d.level ≠ 0) (out : SlowOut h h2 r ds z d d2)
    (look : 1 ≤ d.lookahead.toNat)
    (noMatch : ¬ (3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat))
    (eSs : F.strstart = d2.strstart + 1) (eLa : F.lookahead = d2.lookahead - 1) (eIns : F.insert = d.insert)
    (ePl : F.prev_length = d2.prev_length) (eMl : F.match_length = d2.match_length)
    (eMs : F.match_start = d2.match_start) (eMa : F.match_available = 1)
    (eLv : F.level = d.level) (eSt : F.strategy = d.strategy) (eHw : F.high_water = d.high_water)
    (eWs : F.window_size = d.window_size) (eW : F.w_size = d.w_size) (eLf : F.last_flush = d.last_flush)
    (eStat : F.status = d.status) (eWr : F.wrap = d.wrap)
    (bsLt : F.block_start.toInt < F.strstart.toNat)
    (span : (F.strstart.toNat : Int) - F.block_start.toInt ≤ 258 * (F.sym_next.toNat / 3 : Nat) + F.match_available.toInt)
    (bits : F.bi_valid.toInt ≤ 7) (cursor : F.pending = 0 → F.pending_out = F.pending_buf)
    (symRoom : F.sym_next.toNat < F.sym_end.toNat) (matches0 : F.«matches» = 0)
    (wsHi : d.window_size.toNat ≤ 65536) : Shape F := by
  have ssLt := d.strstart.toNat_lt
  have room := shape.room
  have upd := out.update
  have ss3 : F.strstart.toNat = d.strstart.toNat + 1 := by
    rw [eSs, out.strstart, UInt32.toNat_add]; simp; omega
  have la3 : F.lookahead.toNat = d.lookahead.toNat - 1 := by
    rw [eLa, out.lookahead]
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))
  have dist := slow_dist out look noMatch eSs eMs eW la3 (by omega)
  have lazyK : 4 ≤ F.level.toInt ∧ F.strategy.toInt ≠ 2 ∧ F.strategy.toInt ≠ 3 := by
    rw [eLv, eSt]; exact kind
  refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr eMa, Int.le_of_lt bsLt, fun _ => span, fun zero => absurd (eLv ▸ zero) level,
    fun _ => by rw [ss3]; omega, fun large => by
      rw [eMl] at large; have := dist large; rw [eMl, eIns]
      refine ⟨this.1, this.2.1, this.2.2, shape.insertDone ?_, by rw [ss3]; omega⟩
      have longer : d.match_length.toNat < d2.match_length.toNat := by rw [out.prevLength] at noMatch; omega
      rcases out.matchLook with l | two <;> omega,
    fun lo hi => absurd (show 4 ≤ F.level.toInt by rw [eLv]; exact kind.1) (by omega), ?_, ?_, ?_, ?_, ?_, bits,
    cursor, symRoom, ⟨by rw [matches0]; decide, fun _ => matches0⟩,
    fun large => ⟨lazyK.1, lazyK.2.1, lazyK.2.2, by rw [ePl] at large; rw [ePl, eMl]; omega⟩,
    fun _ => bsLt, fun _ => lazyK, fun _ => bsLt⟩
  · rw [ss3, la3, eWs]; omega
  · rw [ss3, eIns]; have := shape.insert; omega
  · intro large; rw [la3] at large; rw [eIns]; exact shape.insertDone (by omega)
  · rw [ePl, out.prevLength]; exact shape.matchLength
  · rw [eMl]; exact out.matchShape
  · rw [eHw, eWs]; exact shape.highWater
  · rw [ss3, la3, eHw]; have := shape.windowInit; omega
  · rw [eLf]; exact shape.lastFlush
  · rw [eStat, eLf]; exact shape.headerFlush
  · rw [eWr, eStat]; exact shape.trailer


/-! ## The pending literal -/

/-- The state after the pending literal and the step past it. -/
def advanceState (x : DeflateState) : DeflateState :=
  { x with strstart := x.strstart + 1, lookahead := x.lookahead - 1 }

set_option maxHeartbeats 16000000 in
/-- **A literal is pending and no match is emitted**: the byte at `strstart - 1` is tallied, the
block flushed when the symbol buffer is full, and the step moves past `strstart`. -/
theorem slow_pending (safe : FlushSafe) {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head SlowKind h r ds z d) (pending : d.pending = 0)
    (look : 1 ≤ d.lookahead.toNat) (out : SlowOut h h2 r ds z d d2)
    (noMatch : ¬ (3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat))
    (avail : d2.match_available ≠ 0) (st : LoopS) (hh : UInt32) :
    ∃ st' h', slowPending (some (.tab ds)) st hh d2 h2 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧ d'.pending = 0 ∧
          z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧ z'.avail_out = 0)) := by
  have inv := head.inv
  have shape := inv.shape
  have upd := out.update
  have level := head.level
  have kind := head.kind
  have wsHi := (slide_window_sizes inv.good).2
  have wsz := inv.good.inv.wsz
  have ssLt := d.strstart.toNat_lt
  have room := shape.room
  have eMa : d2.match_available = d.match_available := out.available
  have one : d.match_available = 1 := by
    rcases shape.matchAvailable with e | e
    · rw [← eMa] at e; exact absurd e avail
    · exact e
  have s1 : 1 ≤ d.strstart.toNat := shape.available (by rw [one]; decide)
  have eSs := out.strstart
  have eLa := out.lookahead
  have eIns := out.insert
  obtain ⟨w, wa, win, getW, sizeW⟩ := window_block inv.good
  have getW2 : h2.bytes w = some wa := by rw [out.bytes]; exact getW
  have win2 : d2.window = .ref (.blk w) 0 := by rw [upd]; exact win
  have back : (d2.strstart - 1).toNat = d.strstart.toNat - 1 := by
    rw [eSs]; exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using s1))
  have readC : index8 d2.window (d2.strstart - 1).toNat h2 = .ok (bfn wa (d.strstart.toNat - 1), h2) := by
    rw [win2, back]; exact index8_bfn getW2 (by simp) (by omega)
  obtain ⟨c, cdef⟩ : ∃ x, x = bfn wa (d.strstart.toNat - 1) := ⟨_, rfl⟩
  rw [← cdef] at readC
  -- the symbols of the block, on the heap after the search
  obtain ⟨⟨xs, ⟨b, buf, pbuf, getB, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
  have pbuf2 : d2.pending_buf = .ref (.blk b) 0 := by rw [upd]; exact pbuf
  have getB2 : h2.bytes b = some buf := by rw [out.bytes]; exact getB
  have trees2 : TreesInvAt h2 ds d2 b buf := trees_at_of_good out.good pbuf2 getB2
  have ledger2 : SymbolLedger buf d2 xs := by rw [upd]; exact ledger.keep rfl rfl rfl rfl
  have strict2 : d2.sym_next.toNat < d2.sym_end.toNat := by
    rw [show d2.sym_next = d.sym_next by rw [upd], show d2.sym_end = d.sym_end by rw [upd]]; exact shape.symRoom
  have roomT := literal_room out.good.inv strict2
  have tallyRun := tally_literal_run trees2.base c roomT
  let X := literalState d2 c
  obtain ⟨h3, h3def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h2 b (literalBytes buf d2 c)) ds X := ⟨_, rfl⟩
  rw [← h3def] at tallyRun
  have good3 : DGood h3 r ds z X := by rw [h3def]; exact literal_good_after out.good trees2 c roomT
  have getB3 : h3.bytes b = some (literalBytes buf d2 c) := by rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB]
  have trees3 : TreesInvAt h3 ds X b (literalBytes buf d2 c) := trees_at_of_good good3 pbuf2 getB3
  have ledger3 := ledger_literal trees2.base ledger2 roomT c
  have count3 := literal_count trees2.base roomT c
  have buffers2 : StreamBuffers h2 r := by
    obtain ⟨wn, pv, hd, pb⟩ : d2.window = d.window ∧ d2.prev = d.prev ∧ d2.head = d.head ∧
        d2.pending_buf = d.pending_buf := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz out.good.live.hz head.buffers out.frame
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good out.good wn pv hd pb) (stream_accounting_self z) out.borrow
  have buffers3 : StreamBuffers h3 r := by
    rw [h3def]; rw [h3def] at good3
    exact private_write_buffers out.good buffers2 pbuf2 ⟨rfl, rfl, rfl, rfl⟩ good3
  have wb : w ≠ b := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have be : b0 = b := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w0 b0; exact blocks.wb
  have getW3 : h3.bytes w = some wa := by
    rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ wb, getW2]
  have chains3 : HeapChains h3 X (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else chainTop d) := by
    rw [h3def]; exact pending_write_chains out.good out.chains pbuf2 _ c
  have static3 : h3.static = h.static := by rw [h3def]; exact out.frame.static
  have ld2 : ldDeflateState (some (.tab ds)) h2 = .ok (d2, h2) := ldDeflateState_tab out.good.live.hs
  have keys2 : Keys d d2 := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have priv3 : PrivStep h h3 r ds d := by
    refine out.priv.trans ?_
    rw [h3def]
    exact (priv_tally out.good pbuf2 _ X).keys keys2
  have back2 : d2.strm = some r := by rw [upd]; exact inv.good.live.back
  -- the frontier after the step
  have topOk : ∀ (F : DeflateState), F.strstart.toNat = d.strstart.toNat + 1 → F.lookahead.toNat = d.lookahead.toNat - 1 →
      F.insert = d.insert → (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else chainTop d) ≤ chainTop F := by
    intro F fs fl fi
    unfold chainTop
    rw [fs, fl, fi]
    by_cases ready : 3 ≤ d.lookahead.toNat
    · rw [if_pos ready]
      have z0 : d.insert.toNat = 0 := by rw [shape.insertDone ready]; rfl
      omega
    · rw [if_neg ready]; omega
  have formOk : ∀ (F : DeflateState) (hF : Heap), F.window = d.window → hF.bytes w = some wa →
      F.strstart.toNat = d.strstart.toNat + 1 → F.lookahead.toNat = d.lookahead.toNat - 1 →
      F.hash_shift = d.hash_shift → F.hash_mask = d.hash_mask → F.ins_h = d2.ins_h →
      F.strategy.toInt ≠ 2 → F.strategy.toInt ≠ 3 → 3 ≤ F.lookahead.toNat → RollingHash hF F := by
    intro F hF fw get fs fl fsh fm fih _ _ large
    rw [fl] at large
    obtain ⟨w0, wa0, win0, get0, form⟩ := out.form (by omega)
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans getW)
    subst aid
    refine ⟨w, wa0, by rw [fw]; exact win, get, ?_⟩
    rw [fs, fsh, fm, fih]; exact form
  have zero : d.«matches» = 0 := shape.slides.2 level
  have flagEnd : ∀ (flag : Bool) (hF : Heap) (zF : ZStream) (F : DeflateState), Head SlowKind hF r ds zF F → Fr h r ds d z hF zF F →
      zF.avail_in = z.avail_in → F.lookahead.toNat = d.lookahead.toNat - 1 → r.get hF = some zF →
      (zF.avail_out ≠ 0 → F.pending = 0) →
      ∃ st' h', (do
          if (← zrd d2.strm (·.avail_out)) == 0 then return { st with hash_head := hh, bflush := flag, ret := some need_more }
          return { st with hash_head := hh, bflush := flag } : M LoopS) hF = .ok (st', h') ∧ st'.brk = st.brk ∧
        ((st'.ret = st.ret ∧ ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧ d'.pending = 0 ∧
            z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
         (st'.ret = some need_more ∧ ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧ z'.avail_out = 0)) := by
    intro flag hF zF F headF accF inF laF getF drainF
    have readOut : zrd d2.strm (·.avail_out) hF = .ok (zF.avail_out, hF) := by rw [back2]; simp [zrd_eq, getF]
    by_cases full : zF.avail_out = 0
    · exact ⟨{ st with hash_head := hh, bflush := flag, ret := some need_more }, hF,
        by simp [bind_app, readOut, full], rfl, Or.inr ⟨rfl, zF, F, headF, accF, full⟩⟩
    · have fullB : (zF.avail_out == 0) = false := by simpa using full
      refine ⟨{ st with hash_head := hh, bflush := flag }, hF,
        by simp only [bind_app, readOut, fullB, Bool.false_eq_true, ite_false]; rfl, rfl,
        Or.inl ⟨rfl, zF, F, headF, accF, drainF full, by rw [inF, laF]; omega⟩⟩
  have la3 : (advanceState X).lookahead.toNat = d.lookahead.toNat - 1 := by
    show (d2.lookahead - 1).toNat = _; rw [eLa]
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))
  have ss3 : (advanceState X).strstart.toNat = d.strstart.toNat + 1 := by
    show (d2.strstart + 1).toNat = _; rw [eSs, UInt32.toNat_add]; simp; omega
  cases flagE : (d2.sym_next + 3 == d2.sym_end)
  · -- no flush
    let F := advanceState X
    have state3 : h3.dstates ds = some X := good3.live.hs
    have wrRun : wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + 1, lookahead := d.lookahead - 1 }) h3 =
        .ok ((), setD h3 ds F) := by rw [wrD_eq, state3]; rfl
    have good5 : DGood (setD h3 ds F) r ds z F := engine_update_good good3 rfl
    have shapeF : Shape F := by
      refine slow_shape shape kind level out look noMatch rfl rfl eIns rfl rfl rfl
        (by show d2.match_available = 1; rw [eMa, one])
        (by show d2.level = d.level; rw [upd]) (by show d2.strategy = d.strategy; rw [upd])
        (by show d2.high_water = d.high_water; rw [upd]) (by show d2.window_size = d.window_size; rw [upd])
        (by show d2.w_size = d.w_size; rw [upd]) (by show d2.last_flush = d.last_flush; rw [upd])
        (by show d2.status = d.status; rw [upd]) (by show d2.wrap = d.wrap; rw [upd]) ?_ ?_
        (by show d2.bi_valid.toInt ≤ 7; rw [show d2.bi_valid = d.bi_valid by rw [upd]]; exact shape.biValid)
        (by show d2.pending = 0 → d2.pending_out = d2.pending_buf
            rw [show d2.pending = d.pending by rw [upd], show d2.pending_out = d.pending_out by rw [upd],
              show d2.pending_buf = d.pending_buf by rw [upd]]; exact shape.cursor)
        (literal_not_full trees2 c roomT flagE)
        (by show d2.«matches» = 0; rw [show d2.«matches» = d.«matches» by rw [upd]]; exact zero) (by omega)
      · show d2.block_start.toInt < _
        rw [show d2.block_start = d.block_start by rw [upd], ss3]; have := shape.blockStart; omega
      · show ((advanceState X).strstart.toNat : Int) - d2.block_start.toInt ≤
          258 * (X.sym_next.toNat / 3 : Nat) + d2.match_available.toInt
        rw [ss3, count3, show d2.block_start = d.block_start by rw [upd],
          show d2.sym_next = d.sym_next by rw [upd], eMa, one]
        have span := shape.blockSpan level
        rw [one] at span
        have o1 : (1 : Int32).toInt = 1 := rfl
        rw [o1] at span ⊢
        have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
        rw [div]; push_cast; omega
    have hashingF : Hashing (setD h3 ds F) F := by
      refine ⟨fun _ => ?_, fun one' => ?_, fun s2 s3 large => ?_⟩
      · obtain ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, H⟩ := chains3
        refine ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, ?_⟩
        exact chains_mono H (topOk F ss3 la3 eIns) (by
          change X.strstart.toNat + X.lookahead.toNat ≤ (advanceState X).strstart.toNat + (advanceState X).lookahead.toNat
          rw [ss3, la3]; change d2.strstart.toNat + d2.lookahead.toNat ≤ _; rw [eSs, eLa]; omega)
      · change d2.«matches» = 1 at one'
        rw [show d2.«matches» = d.«matches» by rw [upd], zero] at one'; cases one'
      · exact formOk F (setD h3 ds F) (by show d2.window = d.window; rw [upd]) getW3 ss3 la3
          (by show d2.hash_shift = d.hash_shift; rw [upd]) (by show d2.hash_mask = d.hash_mask; rw [upd]) rfl
          s2 s3 large
    have symbolsF : Symbols (setD h3 ds F) F := by
      refine ⟨⟨xs ++ [({ distance := 0, value := c.toNat } : Symbol)],
          ⟨b, _, pbuf2, getB3, ledger3.keep (result := F) rfl rfl rfl rfl⟩, ?_⟩,
        ⟨fun k hk => by show (X.bl_tree[k]!).fc = 0; rw [show X.bl_tree = d.bl_tree by show d2.bl_tree = d.bl_tree; rw [upd]]; exact clear.bl k hk,
          by show d2.opt_len = 0; rw [show d2.opt_len = d.opt_len by rw [upd]]; exact clear.opt,
          by show d2.static_len = 0; rw [show d2.static_len = d.static_len by rw [upd]]; exact clear.fixed⟩, ?_⟩
      · intro s mem
        rcases List.mem_append.mp mem with old | new
        · show s.distance ≤ d2.w_size.toNat - 262; rw [show d2.w_size = d.w_size by rw [upd]]; exact dist s old
        · simp only [List.mem_singleton] at new; subst new; exact Nat.zero_le _
      · intro b0 off pout _
        change d2.pending_out = _ at pout
        rw [show d2.pending_out = d.pending_out by rw [upd], shape.cursor pending, pbuf] at pout
        simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
        change off + d2.pending.toNat ≤ d2.lit_bufsize.toNat
        rw [← pout.2, show d2.pending = d.pending by rw [upd], pending]
        exact Nat.zero_le _
    have invF : DInv (setD h3 ds F) r ds z F :=
      ⟨good5, inv.alloc, by unfold LibraryGlobals; show h3.static = _; rw [static3]; exact inv.globals,
        shapeF, hashingF, symbolsF⟩
    have buffersF : StreamBuffers (setD h3 ds F) r :=
      state_write_buffers good3 buffers3 ⟨rfl, rfl, rfl, rfl⟩ good5
    have headF : Head SlowKind (setD h3 ds F) r ds z F :=
      ⟨invF, buffersF, head.out, head.input, by show d2.level ≠ 0; rw [show d2.level = d.level by rw [upd]]; exact level,
        slow_kind_keep d F (by show d2.strategy = d.strategy; rw [upd]) (by show d2.level = d.level; rw [upd]) kind⟩
    obtain ⟨st', h', endRun, brk', cases⟩ := flagEnd false (setD h3 ds F) z F headF
      (Fr.priv head.inv.good head.buffers (priv3.trans (priv_setD h3 r ds d F good3.live.hs))
        (keys2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) rfl la3
      good5.live.hz (fun _ => by show d2.pending = 0; rw [show d2.pending = d.pending by rw [upd]]; exact pending)
    refine ⟨st', h', ?_, brk', cases⟩
    unfold slowPending
    simp only [bind_app, readC, tallyRun, flagE, Bool.false_eq_true, ite_false, wrRun]
    simp only [bind_app] at endRun
    exact endRun
  · -- the symbol buffer is full: the block is flushed before the step
    have lax : BlockLax h3 r ds z X b (literalBytes buf d2 c) (xs ++ [({ distance := 0, value := c.toNat } : Symbol)]) := by
      refine ⟨good3, inv.alloc, by unfold LibraryGlobals; rw [static3]; exact inv.globals, trees3, ledger3,
        ⟨fun k hk => by show (X.bl_tree[k]!).fc = 0; rw [show X.bl_tree = d.bl_tree by show d2.bl_tree = d.bl_tree; rw [upd]]; exact clear.bl k hk,
          by show d2.opt_len = 0; rw [show d2.opt_len = d.opt_len by rw [upd]]; exact clear.opt,
          by show d2.static_len = 0; rw [show d2.static_len = d.static_len by rw [upd]]; exact clear.fixed⟩,
        by show d2.pending = 0; rw [show d2.pending = d.pending by rw [upd]]; exact pending,
        by show -(2 : Int) ^ 62 ≤ d2.block_start.toInt; rw [show d2.block_start = d.block_start by rw [upd]]
           exact block_start_low inv level,
        by show d2.block_start.toInt ≤ d2.strstart.toNat; rw [show d2.block_start = d.block_start by rw [upd], eSs]
           exact shape.blockStart,
        by show d2.level ≠ 0; rw [show d2.level = d.level by rw [upd]]; exact level,
        buffers3, head.out, ?_, ?_, ?_⟩
      · show d2.strstart.toNat + d2.lookahead.toNat ≤ d2.window_size.toNat
        rw [eSs, eLa, show d2.window_size = d.window_size by rw [upd]]; exact room
      · show d2.pending = 0 → d2.pending_out = d2.pending_buf
        rw [show d2.pending = d.pending by rw [upd], show d2.pending_out = d.pending_out by rw [upd],
          show d2.pending_buf = d.pending_buf by rw [upd]]; exact shape.cursor
      · show d2.bi_valid.toInt ≤ 7; rw [show d2.bi_valid = d.bi_valid by rw [upd]]; exact shape.biValid
    obtain ⟨produced, h4, z4, R, run4, good4, buffers4, acc4, drained, cursor4, bits4, frame4, matches4,
      clear4, ⟨b4, a4, pb4, get4, ledger4⟩, static4, chainsT4, win4, totalO4, totalI4, buffer4, shape4, keys4⟩ :=
      flush_block_lax safe lax false
    have e := frame4
    unfold Block.FlushFrame at e
    have fS : R.strstart = d2.strstart := (congrArg DeflateState.strstart e).trans rfl
    have fL : R.lookahead = d2.lookahead := (congrArg DeflateState.lookahead e).trans rfl
    have fI : R.insert = d2.insert := (congrArg DeflateState.insert e).trans rfl
    have fH : R.ins_h = d2.ins_h := (congrArg DeflateState.ins_h e).trans rfl
    have fMl : R.match_length = d2.match_length := (congrArg DeflateState.match_length e).trans rfl
    have fMs : R.match_start = d2.match_start := (congrArg DeflateState.match_start e).trans rfl
    have fMa : R.match_available = d2.match_available := (congrArg DeflateState.match_available e).trans rfl
    have fPl : R.prev_length = d2.prev_length := (congrArg DeflateState.prev_length e).trans rfl
    have fLv : R.level = d2.level := (congrArg DeflateState.level e).trans rfl
    have fSt : R.strategy = d2.strategy := (congrArg DeflateState.strategy e).trans rfl
    have fHw : R.high_water = d2.high_water := (congrArg DeflateState.high_water e).trans rfl
    have fWs : R.window_size = d2.window_size := (congrArg DeflateState.window_size e).trans rfl
    have fW : R.w_size = d2.w_size := (congrArg DeflateState.w_size e).trans rfl
    have fLf : R.last_flush = d2.last_flush := (congrArg DeflateState.last_flush e).trans rfl
    have fStat : R.status = d2.status := (congrArg DeflateState.status e).trans rfl
    have fWr : R.wrap = d2.wrap := (congrArg DeflateState.wrap e).trans rfl
    have fBs : R.block_start = d2.strstart.toUInt64.toInt64 := (congrArg DeflateState.block_start e).trans rfl
    have fEnd : R.sym_end = d2.sym_end := (congrArg DeflateState.sym_end e).trans rfl
    have fWin : R.window = d2.window := (congrArg DeflateState.window e).trans rfl
    have fHs : R.hash_shift = d2.hash_shift := (congrArg DeflateState.hash_shift e).trans rfl
    have fHm : R.hash_mask = d2.hash_mask := (congrArg DeflateState.hash_mask e).trans rfl
    have fPb : R.pending_buf = d2.pending_buf := (congrArg DeflateState.pending_buf e).trans rfl
    have fWb : R.w_bits = d2.w_bits := (congrArg DeflateState.w_bits e).trans rfl
    have symZero : R.sym_next = 0 := by
      have := ledger4.count; simp at this; exact UInt32.toNat_inj.mp (by rw [this]; rfl)
    let F := advanceState R
    have state4 : h4.dstates ds = some R := good4.live.hs
    have wrRun : wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + 1, lookahead := d.lookahead - 1 }) h4 =
        .ok ((), setD h4 ds F) := by rw [wrD_eq, state4]; rfl
    have good5 : DGood (setD h4 ds F) r ds z4 F := engine_update_good good4 rfl
    have ssF : F.strstart.toNat = d.strstart.toNat + 1 := by
      show (R.strstart + 1).toNat = _; rw [fS, eSs, UInt32.toNat_add]; simp; omega
    have laF : F.lookahead.toNat = d.lookahead.toNat - 1 := by
      show (R.lookahead - 1).toNat = _; rw [fL, eLa]
      exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))
    have bsF : F.block_start.toInt = d.strstart.toNat := by
      show R.block_start.toInt = _; rw [fBs, eSs]; exact u32_toInt64_toInt _
    have shapeF : Shape F := by
      refine slow_shape shape kind level out look noMatch (by show R.strstart + 1 = _; rw [fS])
        (by show R.lookahead - 1 = _; rw [fL]) (by show R.insert = _; rw [fI, eIns])
        (by show R.prev_length = _; rw [fPl]) (by show R.match_length = _; rw [fMl])
        (by show R.match_start = _; rw [fMs]) (by show R.match_available = 1; rw [fMa, eMa, one])
        (by show R.level = d.level; rw [fLv, upd]) (by show R.strategy = d.strategy; rw [fSt, upd])
        (by show R.high_water = d.high_water; rw [fHw, upd]) (by show R.window_size = d.window_size; rw [fWs, upd])
        (by show R.w_size = d.w_size; rw [fW, upd]) (by show R.last_flush = d.last_flush; rw [fLf, upd])
        (by show R.status = d.status; rw [fStat, upd]) (by show R.wrap = d.wrap; rw [fWr, upd])
        (by rw [bsF, ssF]; omega) ?_ (by show R.bi_valid.toInt ≤ 7; omega) cursor4
        (by show R.sym_next.toNat < R.sym_end.toNat
            rw [symZero, fEnd, show d2.sym_end = d.sym_end by rw [upd]]; have := shape.symRoom; simp; omega)
        matches4 (by omega)
      rw [bsF, ssF]
      show _ ≤ 258 * (R.sym_next.toNat / 3 : Nat) + R.match_available.toInt
      rw [symZero, fMa, eMa, one]
      have o1 : (1 : Int32).toInt = 1 := rfl
      rw [o1]; simp; omega
    have getW4 : h4.bytes w = some wa := by rw [win4 w (by show d2.window = _; rw [upd]; exact win)]; exact getW3
    have hashingF : Hashing (setD h4 ds F) F := by
      refine ⟨fun _ => ?_, fun one' => ?_, fun s2 s3 large => ?_⟩
      · obtain ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, H⟩ := chainsT4 _ chains3
        refine ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, ?_⟩
        refine chains_mono H (topOk F ssF laF (by show R.insert = _; rw [fI, eIns])) (by
          change R.strstart.toNat + R.lookahead.toNat ≤ F.strstart.toNat + F.lookahead.toNat
          rw [ssF, laF, fS, fL, eSs, eLa]; omega)
      · change R.«matches» = 1 at one'
        rw [matches4] at one'; cases one'
      · exact formOk F (setD h4 ds F) (by show R.window = d.window; rw [fWin, upd]) getW4 ssF laF
          (by show R.hash_shift = d.hash_shift; rw [fHs, upd]) (by show R.hash_mask = d.hash_mask; rw [fHm, upd])
          (by show R.ins_h = d2.ins_h; rw [fH]) s2 s3 large
    have symbolsF : Symbols (setD h4 ds F) F := by
      refine ⟨⟨[], ⟨b4, a4, pb4, get4, ledger4.keep (result := F) rfl rfl rfl rfl⟩, by simp⟩,
        ⟨clear4.bl, clear4.opt, clear4.fixed⟩, ?_⟩
      intro _ _ _ nonzero
      exact absurd (show F.sym_next = 0 from symZero) nonzero
    have invF : DInv (setD h4 ds F) r ds z4 F :=
      ⟨good5, ⟨acc4.2.2.2.2.2.2.2.1.trans inv.alloc.1, acc4.2.2.2.2.2.2.2.2.1.trans inv.alloc.2⟩,
        by unfold LibraryGlobals; show h4.static = _; rw [static4, static3]; exact inv.globals,
        shapeF, hashingF, symbolsF⟩
    have buffersF : StreamBuffers (setD h4 ds F) r :=
      state_write_buffers good4 buffers4 ⟨rfl, rfl, rfl, rfl⟩ good5
    have inZ : z4.avail_in = z.avail_in := by
      have := acc4.2.2.1; exact UInt32.toNat_inj.mp (by omega)
    have outZ : z4.next_out ≠ .null := by rw [acc4.2.2.2.2.2.1]; exact advance_ne_null _ head.out
    have inputZ : z4.avail_in ≠ 0 → z4.next_in ≠ .null := fun nz => by
      rw [acc4.2.2.2.2.1, advance_zero]; exact head.input (by rw [← inZ]; exact nz)
    have headF : Head SlowKind (setD h4 ds F) r ds z4 F :=
      ⟨invF, buffersF, outZ, inputZ, by show R.level ≠ 0; rw [fLv, show d2.level = d.level by rw [upd]]; exact level,
        slow_kind_keep d F (by show R.strategy = d.strategy; rw [fSt, upd]) (by show R.level = d.level; rw [fLv, upd]) kind⟩
    obtain ⟨st', h', endRun, brk', cases⟩ := flagEnd true (setD h4 ds F) z4 F headF
      (Fr.trans head.inv.good head.buffers
        (Fr.priv head.inv.good head.buffers priv3 (keys2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : Keys d X))
        (Fr.trans good3 buffers3 (Fr.flush acc4 totalI4 totalO4 buffer4 shape4 keys4)
          (Fr.priv good4 buffers4 (priv_setD h4 r ds R F state4) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))) inZ laF
      good5.live.hz (fun full => by
        rcases drained with p0 | a0
        · exact p0
        · exact absurd a0 full)
    refine ⟨st', h', ?_, brk', cases⟩
    have run4' : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 h3 = .ok ((), h4) := run4
    unfold slowPending
    simp only [bind_app, readC, tallyRun, flagE, ite_true, run4', wrRun]
    simp only [bind_app] at endRun
    exact endRun

/-! ## The match emission -/

open Zlib.Deflate.BorrowProofs in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The pending match is emitted**: `_tr_tally_dist` of the match found at `strstart - 1`, the
insertions of its remaining positions, the reset of the lazy state, and the block flush when the
symbol buffer is full. -/
theorem slow_match (safe : FlushSafe) {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head SlowKind h r ds z d) (pending : d.pending = 0)
    (out : SlowOut h h2 r ds z d d2)
    (isMatch : 3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat)
    (st : LoopS) (hh : UInt32) :
    ∃ st' h', (do
        let bflush ← tally_dist (some (.tab ds)) (d2.strstart - 1 - d2.prev_match) (d2.prev_length - MIN_MATCH_u)
        let hh ← slowMatchAdvance (some (.tab ds)) (d2.strstart + d2.lookahead - MIN_MATCH_u) hh
        lazyTail (some (.tab ds)) st hh bflush) h2 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧ d'.pending = 0 ∧
          z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧ z'.avail_out = 0)) := by
  have inv := head.inv
  have shape := inv.shape
  have upd := out.update
  have level := head.level
  have kind := head.kind
  have wsHi := (slide_window_sizes inv.good).2
  have room := shape.room
  have ssLt := d.strstart.toNat_lt
  have big : 3 ≤ d.match_length.toNat := by rw [← out.prevLength]; exact isMatch.1
  obtain ⟨dlo, dhi, mlLa, insZero, s1⟩ := shape.pendingMatch big
  have mlHi : d.match_length.toNat ≤ 258 := shape.matchLength
  have eSs := out.strstart
  have eLa := out.lookahead
  have ePl := out.prevLength
  have ePm := out.prevMatch
  obtain ⟨w, wa, win, getW, _⟩ := window_block inv.good
  have getW2 : h2.bytes w = some wa := by rw [out.bytes]; exact getW
  -- the record of the match
  obtain ⟨⟨xs, ⟨b, buf, pbuf, getB, ledger⟩, dist⟩, clear, _⟩ := inv.symbols
  have pbuf2 : d2.pending_buf = .ref (.blk b) 0 := by rw [upd]; exact pbuf
  have getB2 : h2.bytes b = some buf := by rw [out.bytes]; exact getB
  have trees2 : TreesInvAt h2 ds d2 b buf := trees_at_of_good out.good pbuf2 getB2
  have ledger2 : SymbolLedger buf d2 xs := by rw [upd]; exact ledger.keep rfl rfl rfl rfl
  have strict2 : d2.sym_next.toNat < d2.sym_end.toNat := by
    rw [show d2.sym_next = d.sym_next by rw [upd], show d2.sym_end = d.sym_end by rw [upd]]; exact shape.symRoom
  have roomT := literal_room out.good.inv strict2
  obtain ⟨dist0, dist0def⟩ : ∃ x, x = d2.strstart - 1 - d2.prev_match := ⟨_, rfl⟩
  obtain ⟨len0, len0def⟩ : ∃ x, x = d2.prev_length - MIN_MATCH_u := ⟨_, rfl⟩
  have distEq : dist0 = d.strstart - 1 - d.match_start := by rw [dist0def, eSs, ePm]
  have dlo0 : 1 ≤ dist0.toNat := by rw [distEq]; exact dlo
  have dhi0 : dist0.toNat ≤ d.w_size.toNat - 262 := by rw [distEq]; exact dhi
  have lenNat : len0.toNat = d.match_length.toNat - 3 := by
    rw [len0def, ePl]
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by change 3 ≤ _; exact big))
  have tallyRun := tally_match_run trees2.base dist0 len0 dlo0 (by omega) roomT
  have ledger3 := ledger_match trees2.base ledger2 roomT dist0 len0 dlo0 (by omega) (by omega)
  let buf' := matchBytes buf d2 dist0.toUInt16 len0.toUInt8
  let d3 := matchSymbolState d2 dist0 len0
  obtain ⟨h3, h3def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h2 b buf') ds d3 := ⟨_, rfl⟩
  have tallyRun' : tally_dist (some (.tab ds)) dist0 len0 h2 = .ok (d2.sym_next + 3 == d2.sym_end, h3) := by
    rw [h3def]; exact tallyRun
  have good3 : DGood h3 r ds z d3 := by rw [h3def]; exact match_good_after out.good trees2 dist0 len0 roomT
  have getB3 : h3.bytes b = some buf' := by rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB]
  have wb : w ≠ b := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have be : b0 = b := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w0 b0; exact blocks.wb
  have getW3 : h3.bytes w = some wa := by
    rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ wb, getW2]
  have count3 : d3.sym_next.toNat = d.sym_next.toNat + 3 := by
    rw [show d.sym_next = d2.sym_next by rw [upd]]; exact literal_count trees2.base roomT 0
  have buffers2 : StreamBuffers h2 r := by
    obtain ⟨wn, pv, hd, pb⟩ : d2.window = d.window ∧ d2.prev = d.prev ∧ d2.head = d.head ∧
        d2.pending_buf = d.pending_buf := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz out.good.live.hz head.buffers out.frame
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good out.good wn pv hd pb) (stream_accounting_self z) out.borrow
  have buffers3 : StreamBuffers h3 r := by
    rw [h3def]; rw [h3def] at good3
    exact private_write_buffers out.good buffers2 pbuf2 ⟨rfl, rfl, rfl, rfl⟩ good3
  have static3 : h3.static = h.static := by rw [h3def]; exact out.frame.static
  have borrow3 : h3.libcErrorBorrow = h.libcErrorBorrow := by rw [h3def]; exact out.borrow
  -- the chains and the rolling hash before the insertions
  have T3 : HeapChains h3 d3 (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else chainTop d) := by
    rw [h3def]
    obtain ⟨w', p', q', wa', pa', qa', win', prev', hd', hw', hp', hq', H⟩ :=
      pending_write_chains out.good out.chains pbuf2 buf' 0
    exact ⟨w', p', q', wa', pa', qa', win', prev', hd', hw', hp', hq', H⟩
  have chains3 : HeapChains h3 d3 (min (d3.strstart.toNat + 1) (d3.strstart.toNat + d3.lookahead.toNat - 2)) := by
    apply chains_up T3
    change _ ≤ min (d2.strstart.toNat + 1) (d2.strstart.toNat + d2.lookahead.toNat - 2)
    rw [eSs, eLa]
    by_cases ready : 3 ≤ d.lookahead.toNat
    · rw [if_pos ready]; omega
    · rw [if_neg ready]; unfold chainTop; rw [insZero]
      have z0 : (0 : UInt32).toNat = 0 := rfl
      rw [z0]; omega
  have form3 : d3.strstart.toNat + 1 ≤ d3.strstart.toNat + d3.lookahead.toNat - 3 →
      InsHForm d3.hash_shift d3.hash_mask (bfn wa) (d3.strstart.toNat + 1) d3.ins_h := by
    intro le
    change d2.strstart.toNat + 1 ≤ d2.strstart.toNat + d2.lookahead.toNat - 3 at le
    rw [eSs, eLa] at le
    obtain ⟨w0, wa0, win0, get0, form⟩ := out.form (by omega)
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    rw [wid] at get0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans getW)
    rw [aid] at form
    change InsHForm d2.hash_shift d2.hash_mask (bfn wa) (d2.strstart.toNat + 1) d2.ins_h
    rw [show d2.hash_shift = d.hash_shift by rw [upd], show d2.hash_mask = d.hash_mask by rw [upd], eSs]
    exact form
  -- the insertions and the reset
  obtain ⟨cand, h6, R, advRun, goodR, _, chainsR, winR, getWR, maR, mlR, plR, ssR, laR, endR, roomR, formR,
      keepR, hwR, bytesR, bsR, ltR, dtR, fieldsR, frameR⟩ :=
    slow_match_advance_frontier good3 chains3
      (show d3.window = .ref (.blk w) 0 by change d2.window = _; rw [upd]; exact win) getW3
      (show 3 ≤ d3.prev_length.toNat from isMatch.1)
      (show d3.prev_length.toNat ≤ 258 by change d2.prev_length.toNat ≤ 258; rw [ePl]; exact mlHi)
      (show d3.prev_length.toNat - 1 ≤ d3.lookahead.toNat by
        change d2.prev_length.toNat - 1 ≤ d2.lookahead.toNat; rw [ePl, eLa]; omega)
      (show 3 ≤ d3.strstart.toNat + d3.lookahead.toNat by
        change 3 ≤ d2.strstart.toNat + d2.lookahead.toNat; rw [eSs, eLa]; omega)
      (show d3.strstart.toNat + d3.lookahead.toNat ≤ d3.window_size.toNat by
        change d2.strstart.toNat + d2.lookahead.toNat ≤ d2.window_size.toNat
        rw [eSs, eLa, show d2.window_size = d.window_size by rw [upd]]; exact room)
      form3 hh
  have advRun' : slowMatchAdvance (some (.tab ds)) (d2.strstart + d2.lookahead - MIN_MATCH_u) hh h3 =
      .ok (cand, h6) := advRun
  have keys2 : Keys d d2 := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have keys3 : Keys d d3 := keys2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨wP, pP, qP, bP, blocksP⟩ := inv.good.inv.blocks
  obtain ⟨privAdv, eR, getR, keysR⟩ := PrivM.slow_match_advance (r := r) blocksP.prev blocksP.head _ hh h3 cand h6
    ⟨d3, good3.live.hs, keys3⟩ advRun'
  have keysRR : Keys d R := by
    have := goodR.live.hs; rw [getR] at this; cases this; exact keysR
  have pre : Fr h r ds d z h6 z R := by
    refine Fr.priv head.inv.good head.buffers (out.priv.trans ?_) keysRR
    refine PrivStep.trans ?_ privAdv
    rw [h3def]
    exact (priv_tally out.good pbuf2 buf' d3).keys keys2
  have borrowR : h6.libcErrorBorrow = h3.libcErrorBorrow := Zlib.Deflate.BorrowProofs.Private.stable_slowMatchAdvance _ _ _ h3 _ h6 advRun'
  have f : ∀ {β : Type} (g : DeflateState → β),
      (∀ x : DeflateState, g { x with strstart := R.strstart, lookahead := R.lookahead, ins_h := R.ins_h, prev_length := R.prev_length, match_available := 0, match_length := 2 } = g x) → g R = g d3 :=
    fun g hg => (congrArg g fieldsR).trans (hg d3)
  have eLv : R.level = d.level := by rw [f DeflateState.level (fun _ => rfl)]; change d2.level = _; rw [upd]
  have eSt : R.strategy = d.strategy := by rw [f DeflateState.strategy (fun _ => rfl)]; change d2.strategy = _; rw [upd]
  have ePd : R.pending = d.pending := by rw [f DeflateState.pending (fun _ => rfl)]; change d2.pending = _; rw [upd]
  have ePo : R.pending_out = d.pending_out := by
    rw [f DeflateState.pending_out (fun _ => rfl)]; change d2.pending_out = _; rw [upd]
  have ePb : R.pending_buf = d.pending_buf := by
    rw [f DeflateState.pending_buf (fun _ => rfl)]; change d2.pending_buf = _; rw [upd]
  have eEnd : R.sym_end = d.sym_end := by rw [f DeflateState.sym_end (fun _ => rfl)]; change d2.sym_end = _; rw [upd]
  have eSym : R.sym_next = d3.sym_next := f DeflateState.sym_next (fun _ => rfl)
  have eIns : R.insert = d.insert := by
    rw [f DeflateState.insert (fun _ => rfl)]; change d2.insert = _; exact out.insert
  have eBs : R.block_start = d.block_start := by
    rw [f DeflateState.block_start (fun _ => rfl)]; change d2.block_start = _; rw [upd]
  have eWs : R.window_size = d.window_size := by
    rw [f DeflateState.window_size (fun _ => rfl)]; change d2.window_size = _; rw [upd]
  have eW : R.w_size = d.w_size := by rw [f DeflateState.w_size (fun _ => rfl)]; change d2.w_size = _; rw [upd]
  have eWin : R.window = d.window := by rw [f DeflateState.window (fun _ => rfl)]; change d2.window = _; rw [upd]
  have ePv : R.prev = d.prev := by rw [f DeflateState.prev (fun _ => rfl)]; change d2.prev = _; rw [upd]
  have eHd : R.head = d.head := by rw [f DeflateState.head (fun _ => rfl)]; change d2.head = _; rw [upd]
  have eHw : R.high_water = d.high_water := by
    rw [f DeflateState.high_water (fun _ => rfl)]; change d2.high_water = _; rw [upd]
  have eLf : R.last_flush = d.last_flush := by
    rw [f DeflateState.last_flush (fun _ => rfl)]; change d2.last_flush = _; rw [upd]
  have eWr : R.wrap = d.wrap := by rw [f DeflateState.wrap (fun _ => rfl)]; change d2.wrap = _; rw [upd]
  have eStat : R.status = d.status := by rw [f DeflateState.status (fun _ => rfl)]; change d2.status = _; rw [upd]
  have eBv : R.bi_valid = d.bi_valid := by rw [f DeflateState.bi_valid (fun _ => rfl)]; change d2.bi_valid = _; rw [upd]
  have eMt : R.«matches» = d.«matches» := by rw [f DeflateState.«matches» (fun _ => rfl)]; change d2.«matches» = _; rw [upd]
  have eLit : R.lit_bufsize = d3.lit_bufsize := f DeflateState.lit_bufsize (fun _ => rfl)
  have eLt : R.dyn_ltree = d3.dyn_ltree := f DeflateState.dyn_ltree (fun _ => rfl)
  have eDt : R.dyn_dtree = d3.dyn_dtree := f DeflateState.dyn_dtree (fun _ => rfl)
  have eBl : R.bl_tree = d.bl_tree := by rw [f DeflateState.bl_tree (fun _ => rfl)]; change d2.bl_tree = _; rw [upd]
  have eOpt : R.opt_len = d.opt_len := by rw [f DeflateState.opt_len (fun _ => rfl)]; change d2.opt_len = _; rw [upd]
  have eStc : R.static_len = d.static_len := by
    rw [f DeflateState.static_len (fun _ => rfl)]; change d2.static_len = _; rw [upd]
  have eHs : R.hash_shift = d.hash_shift := by
    rw [f DeflateState.hash_shift (fun _ => rfl)]; change d2.hash_shift = _; rw [upd]
  have eHm : R.hash_mask = d.hash_mask := by
    rw [f DeflateState.hash_mask (fun _ => rfl)]; change d2.hash_mask = _; rw [upd]
  have ssR' : R.strstart.toNat = d.strstart.toNat + d.match_length.toNat - 1 := by
    rw [ssR]; change d2.strstart.toNat + (d2.prev_length.toNat - 1) = _; rw [eSs, ePl]; omega
  have laR' : R.lookahead.toNat = d.lookahead.toNat - (d.match_length.toNat - 1) := by
    rw [laR]; change d2.lookahead.toNat - (d2.prev_length.toNat - 1) = _; rw [eLa, ePl]
  have symR : R.sym_next.toNat = d.sym_next.toNat + 3 := by rw [eSym]; exact count3
  have levelR : R.level ≠ 0 := by rw [eLv]; exact level
  have kindR : SlowKind R := slow_kind_keep d R eSt eLv kind
  have pendingR : R.pending = 0 := by rw [ePd]; exact pending
  have buffersR : StreamBuffers h6 r := by
    exact stream_buffers_private_read good3.live.hz goodR.live.hz buffers3 frameR
      (fun i mine => (stream_owned_deflate good3 i).mpr (Or.inl mine))
      (stream_owned_keys good3 goodR (by rw [eWin]; change d.window = d2.window; rw [upd])
        (by rw [ePv]; change d.prev = d2.prev; rw [upd]) (by rw [eHd]; change d.head = d2.head; rw [upd])
        (by rw [ePb]; change d.pending_buf = d2.pending_buf; rw [upd]))
      (stream_accounting_self z) borrowR
  have pbufR : R.pending_buf = .ref (.blk b) 0 := by rw [ePb]; exact pbuf
  have getBR : h6.bytes b = some buf' := by rw [bytesR]; exact getB3
  have ledgerR : SymbolLedger buf' R (xs ++ [⟨dist0.toNat, len0.toNat⟩]) := ledger3.keep eSym eLit eLt eDt
  have treesR : TreesInvAt h6 ds R b buf' := trees_at_of_good goodR pbufR getBR
  have globalsR : LibraryGlobals h6 := by
    unfold LibraryGlobals; rw [frameR.static, static3]; exact inv.globals
  have clearR : BlockInit.BlockClear R := by
    exact ⟨fun k hk => by rw [eBl]; exact clear.bl k hk, by rw [eOpt]; exact clear.opt, by rw [eStc]; exact clear.fixed⟩
  have chainsC : Chains h6 R := by
    unfold Chains chainTop
    rw [eIns, insZero]
    have z0 : (0 : UInt32).toNat = 0 := rfl
    rw [z0, Nat.sub_zero]
    exact chainsR
  have hashingR : Hashing h6 R := by
    refine ⟨fun _ => chainsC, fun one => ?_, fun _ _ large => ⟨w, wa, winR, getWR, formR large⟩⟩
    rw [eMt, shape.slides.2 level] at one; cases one
  have endR' : R.strstart.toNat + R.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [endR]; change d2.strstart.toNat + d2.lookahead.toNat = _; rw [eSs, eLa]
  have room7 : R.strstart.toNat + R.lookahead.toNat ≤ R.window_size.toNat := by rw [endR', eWs]; exact room
  have ins7 : R.insert.toNat ≤ R.strstart.toNat := by
    rw [eIns, insZero]; exact Nat.zero_le _
  have done7 : 3 ≤ R.lookahead.toNat → R.insert = 0 := fun _ => by rw [eIns]; exact insZero
  have pl7 : R.prev_length.toNat ≤ 258 := by rw [plR]; decide
  have ml7 : R.match_length.toNat ≤ 258 := by rw [mlR]; decide
  have ma7 : R.match_available = 0 ∨ R.match_available = 1 := Or.inl maR
  have bs7 : R.block_start.toInt ≤ R.strstart.toNat := by rw [eBs, ssR']; have := shape.blockStart; omega
  have sb7 : R.sym_next ≠ 0 → R.block_start.toInt < R.strstart.toNat := fun _ => by
    rw [eBs, ssR']; have := shape.blockStart; omega
  have lz7 : 3 ≤ R.prev_length.toNat → 4 ≤ R.level.toInt ∧ R.strategy.toInt ≠ 2 ∧ R.strategy.toInt ≠ 3 ∧
      R.prev_length.toNat < R.match_length.toNat := fun large => absurd large (by rw [plR]; decide)
  have av7 : R.match_available ≠ 0 → 1 ≤ R.strstart.toNat := fun ne => absurd maR ne
  have pm7 : 3 ≤ R.match_length.toNat → 1 ≤ (R.strstart - 1 - R.match_start).toNat ∧
      (R.strstart - 1 - R.match_start).toNat ≤ R.w_size.toNat - 262 ∧
      R.match_length.toNat ≤ R.lookahead.toNat + 1 ∧ R.insert = 0 ∧ 1 ≤ R.strstart.toNat := by
    intro large; rw [mlR] at large; exact absurd large (by decide)
  have fl7 : 1 ≤ R.level.toInt → R.level.toInt ≤ 3 → R.strategy.toInt ≠ 2 → R.strategy.toInt ≠ 3 →
      R.match_length.toNat ≤ 2 ∧ R.prev_length.toNat ≤ 2 :=
    fun _ hi => absurd (show 4 ≤ R.level.toInt by rw [eLv]; exact kind.1) (by omega)
  have hw7 : R.high_water.toNat ≤ R.window_size.toNat := by rw [eHw, eWs]; exact shape.highWater
  have wi7 : R.strstart.toNat + R.lookahead.toNat ≤ R.high_water.toNat := by
    rw [endR', eHw]; exact shape.windowInit
  have lf7 : -2 ≤ R.last_flush.toInt ∧ R.last_flush.toInt ≤ 5 := by rw [eLf]; exact shape.lastFlush
  have hf7 : R.status = INIT_STATE ∨ R.status = GZIP_STATE → R.last_flush = -2 ∨ R.last_flush = -1 := by
    rw [eStat, eLf]; exact shape.headerFlush
  have tr7 : R.wrap.toInt < 0 → R.status = FINISH_STATE := by rw [eWr, eStat]; exact shape.trailer
  have bv7 : R.bi_valid.toInt ≤ 7 := by rw [eBv]; exact shape.biValid
  have cu7 : R.pending = 0 → R.pending_out = R.pending_buf := by rw [ePd, ePo, ePb]; exact shape.cursor
  have sl7 : R.«matches».toNat ≤ 2 ∧ (R.level ≠ 0 → R.«matches» = 0) := by rw [eMt, eLv]; exact shape.slides
  have blockLow : -(2 : Int) ^ 62 ≤ R.block_start.toInt := by rw [eBs]; exact block_start_low inv level
  have distOk : ∀ s ∈ xs ++ [⟨dist0.toNat, len0.toNat⟩], s.distance ≤ R.w_size.toNat - 262 := by
    intro s mem
    rw [eW]
    rcases List.mem_append.mp mem with old | new
    · exact dist s old
    · simp only [List.mem_singleton] at new; subst new; exact dhi0
  have fullCase : (d2.sym_next + 3 == d2.sym_end) = true → ∃ pb buf xs, BlockReady h6 r ds z R pb buf xs :=
    fun _ => ⟨b, buf', _, ⟨goodR, inv.alloc, globalsR, treesR, ledgerR, clearR,
      flushed_shape room7 ins7 done7 pl7 ml7 ma7 (fun zero => absurd zero levelR) av7 pm7 fl7 hw7 wi7 lf7 hf7 tr7
        bv7 cu7 (by rw [eEnd]; have := shape.symRoom; omega) sl7 lz7 (fun nz => absurd maR nz) maR,
      hashingR, pendingR, blockLow, bs7, levelR, buffersR, head.out⟩⟩
  have notFullCase : (d2.sym_next + 3 == d2.sym_end) = false → DInv h6 r ds z R := by
    intro flag
    have strict : R.sym_next.toNat < R.sym_end.toNat := by
      rw [eSym, f DeflateState.sym_end (fun _ => rfl)]; exact literal_not_full trees2 0 roomT flag
    refine ⟨goodR, inv.alloc, globalsR, ⟨room7, ins7, done7, pl7, ml7, ma7, bs7, ?_,
      (fun zero => absurd zero levelR), av7, pm7, fl7, hw7, wi7, lf7, hf7, tr7, bv7, cu7, strict, sl7,
      lz7, sb7, fun nz => absurd maR nz, fun nz => absurd maR nz⟩, hashingR,
      ⟨⟨_, ⟨b, buf', pbufR, getBR, ledgerR⟩, distOk⟩, clearR, ?_⟩⟩
    · intro _
      rw [ssR', symR, eBs, maR]
      have span := shape.blockSpan level
      have avail : d.match_available.toInt ≤ 1 := by
        rcases shape.matchAvailable with e | e <;> rw [e] <;> decide
      have z0 : (0 : Int32).toInt = 0 := rfl
      rw [z0]
      have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
      rw [div]
      push_cast
      omega
    · intro b0 off pout _
      rw [ePo, shape.cursor pending, ← ePb, pbufR] at pout
      simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
      rw [← pout.2, pendingR]
      exact Nat.zero_le _
  obtain ⟨st', h', tailRun, brk', cases⟩ := lazy_tail_step safe slow_kind_keep st cand
    (d2.sym_next + 3 == d2.sym_end) buffersR head.out head.input levelR kindR pendingR fullCase notFullCase
  refine ⟨st', h', ?_, brk', ?_⟩
  · rw [← dist0def, ← len0def]
    simp only [bind_app, tallyRun', advRun']
    exact tailRun
  · rcases cases with ⟨retEq, z', d', head', acc', pending', availEq, laEq'⟩ | ⟨e1, z', d', hd', f, o⟩
    · refine Or.inl ⟨retEq, z', d', head', Fr.trans head.inv.good head.buffers pre acc', pending', ?_⟩
      rw [availEq, laEq', laR']; omega
    · exact Or.inr ⟨e1, z', d', hd', Fr.trans head.inv.good head.buffers pre f, o⟩

/-! ## One iteration and the loop -/

set_option maxHeartbeats 4000000 in
/-- One search and decision of `deflate_slow` from a loop head with lookahead and matcher room. -/
theorem slow_iter (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head SlowKind h r ds z d) (pending : d.pending = 0)
    (look : 1 ≤ d.lookahead.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (flush : Int32) (st : LoopS) :
    ∃ st' h', (do
        let hash_head ← slowSearch (some (.tab ds))
        slowDecision (some (.tab ds)) flush st hash_head) h = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧ d'.pending = 0 ∧
          z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧ z'.avail_out = 0)) := by
  obtain ⟨hh, h2, d2, searchRun, out⟩ := slow_search_run head room
  have ld2 : ldDeflateState (some (.tab ds)) h2 = .ok (d2, h2) := ldDeflateState_tab out.good.live.hs
  have start : ∀ (k : M LoopS) st' h', k h2 = .ok (st', h') →
      (do
        let d ← ldDeflateState (some (.tab ds))
        k) h2 = .ok (st', h') := by
    intro k st' h' run; rw [bind_app, ld2]; exact run
  by_cases sel : 3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat
  · have selB : (decide (d2.prev_length ≥ MIN_MATCH_u) && decide (d2.match_length ≤ d2.prev_length)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, GE.ge, UInt32.le_iff_toNat_le]; exact ⟨sel.1, sel.2⟩
    obtain ⟨st', h', run, rest⟩ := slow_match safe head pending out sel st hh
    refine ⟨st', h', ?_, rest⟩
    rw [bind_app, searchRun]
    simp only []
    rw [slow_decision_source, bind_app, ld2]
    simp only [selB, ite_true]
    exact run
  · have selB : (decide (d2.prev_length ≥ MIN_MATCH_u) && decide (d2.match_length ≤ d2.prev_length)) = false := by
      cases e : (decide (d2.prev_length ≥ MIN_MATCH_u) && decide (d2.match_length ≤ d2.prev_length))
      · rfl
      · exfalso; apply sel
        simp only [Bool.and_eq_true, decide_eq_true_eq, GE.ge, UInt32.le_iff_toNat_le] at e
        exact ⟨e.1, e.2⟩
    by_cases avail : d2.match_available ≠ 0
    · have availB : (d2.match_available != 0) = true := by simpa using avail
      obtain ⟨st', h', run, rest⟩ := slow_pending safe head pending look out sel avail st hh
      refine ⟨st', h', ?_, rest⟩
      rw [bind_app, searchRun]
      simp only []
      rw [slow_decision_source, bind_app, ld2]
      simp only [selB, Bool.false_eq_true, ite_false, availB, ite_true]
      exact run
    · have idle : d2.match_available = 0 := by simpa using avail
      have availB : (d2.match_available != 0) = false := by simp [idle]
      obtain ⟨wrRun, invM, buffersM⟩ := slow_mark head look out sel idle
      have upd := out.update
      have headM : Head SlowKind (setD h2 ds (markState d2)) r ds z (markState d2) :=
        ⟨invM, buffersM, head.out, head.input, by show d2.level ≠ 0; rw [upd]; exact head.level,
          slow_kind_keep d (markState d2) (by show d2.strategy = _; rw [upd]) (by show d2.level = _; rw [upd]) head.kind⟩
      refine ⟨{ st with hash_head := hh, bflush := false }, setD h2 ds (markState d2), ?_, rfl,
        Or.inl ⟨rfl, z, markState d2, headM,
          Fr.priv head.inv.good head.buffers (out.priv.trans (priv_setD h2 r ds d _ out.good.live.hs))
            (by show Keys d (markState d2); rw [show markState d2 = { d2 with match_available := 1, strstart := d2.strstart + 1, lookahead := d2.lookahead - 1 } from rfl, upd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩),
          ?_, ?_⟩⟩
      · rw [bind_app, searchRun]
        simp only []
        rw [slow_decision_source, bind_app, ld2]
        simp only [selB, Bool.false_eq_true, ite_false, availB, bind_app, wrRun]
        rfl
      · show d2.pending = 0; rw [upd]; exact pending
      · show z.avail_in.toNat + (d2.lookahead - 1).toNat < _
        rw [out.lookahead, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))]
        have one1 : (1 : UInt32).toNat = 1 := rfl
        omega

/-- The states of the `deflate_slow` loop. -/
def SlowLoop (h0 : Heap) (d0 : DeflateState) (r : ZStreamRef) (ds : Nat) (z0 : ZStream) (flush : Int32)
    (st : LoopS) (h : Heap) : Prop :=
  ∃ z d, Head SlowKind h r ds z d ∧ Fr h0 r ds d0 z0 h z d ∧
    ((st.brk = false ∧ st.ret = none ∧ d.pending = 0) ∨
     (st.ret = some need_more ∧ (z.avail_out = 0 ∨ (z.avail_in = 0 ∧ flush = Z_NO_FLUSH))) ∨
     (st.brk = true ∧ st.ret = none ∧ d.pending = 0 ∧ d.lookahead = 0 ∧ z.avail_in = 0))

set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_slow`** from a loop head. -/
theorem slow_body_step (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} {h0 : Heap} {z0 : ZStream} {d0 : DeflateState} (head0 : Head SlowKind h0 r ds z0 d0)
    (head : Head SlowKind h r ds z d) (acc : Fr h0 r ds d0 z0 h z d) (pending : d.pending = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_slow_body (some (.tab ds)) flush st h = .ok (st', h') ∧ SlowLoop h0 d0 r ds z0 flush st' h' ∧
      loopMeasure r ds st' h' < loopMeasure r ds st h := by
  have measure0 := loop_measure_head head.inv.good.live.hz head.inv.good.live.hs brk ret
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head SlowKind h1 r ds z1 d1 → Fr h0 r ds d0 z0 h1 z1 d1 →
      d1.pending = 0 → 1 ≤ d1.lookahead.toNat → d1.strstart.toNat + 262 ≤ d1.window_size.toNat →
      z1.avail_in.toNat + d1.lookahead.toNat ≤ z.avail_in.toNat + d.lookahead.toNat →
      ∃ st' h', (do
          let hash_head ← slowSearch (some (.tab ds))
          slowDecision (some (.tab ds)) flush st hash_head) h1 = .ok (st', h') ∧ SlowLoop h0 d0 r ds z0 flush st' h' ∧
        loopMeasure r ds st' h' < loopMeasure r ds st h := by
    intro h1 z1 d1 head1 acc1 pending1 look1 room1 sum
    obtain ⟨st', h', iterRun, brk', choice⟩ := slow_iter safe head1 pending1 look1 room1 flush st
    refine ⟨st', h', iterRun, ?_, ?_⟩
    · rcases choice with ⟨retEq, z', d', head', acc', pending', _⟩ | ⟨retEq, z', d', head', acc', fullO⟩
      · exact ⟨z', d', head', Fr.trans head0.inv.good head0.buffers acc1 acc', Or.inl ⟨brk'.trans brk, retEq.trans ret, pending'⟩⟩
      · exact ⟨z', d', head', Fr.trans head0.inv.good head0.buffers acc1 acc', Or.inr (Or.inl ⟨retEq, Or.inl fullO⟩)⟩
    · rcases choice with ⟨retEq, z', d', head', _, pending', count⟩ | ⟨retEq, _⟩
      · rw [loop_measure_head head'.inv.good.live.hz head'.inv.good.live.hs (brk'.trans brk) (retEq.trans ret),
          measure0]
        omega
      · rw [loop_measure_exit (Or.inr (by rw [retEq]; rfl)), measure0]; omega
  rw [slow_body_source]
  by_cases small : d.lookahead < MIN_LOOKAHEAD_u
  · have short : d.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨sLevel, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, sPending, _⟩ := post.same
    have head1 : Head SlowKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold SlowKind; rw [sStrategy, sLevel]; exact k)
    have pending1 : d1.pending = 0 := sPending.trans pending
    have acc1 : Fr h0 r ds d0 z0 after1 z1 d1 :=
      Fr.trans head0.inv.good head0.buffers acc (Fr.fill head.inv.good head.buffers post)
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    have consumed := post.consumed
    have room1 := fill_room post
    have fillRun' : fill_window (some (.tab ds)) h = .ok ((), after1) := fillRun
    by_cases stop1 : (d1.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · refine ⟨{ st with ret := some need_more }, after1, ?_, ⟨z1, d1, head1, acc1, Or.inr (Or.inl ⟨rfl, Or.inr (stop_facts stop1 post.stopped)⟩)⟩, ?_⟩
      · simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1]
        rfl
      · rw [loop_measure_exit (Or.inr rfl), measure0]; omega
    · have stop1F : (d1.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false := by simpa using stop1
      by_cases empty1 : d1.lookahead = 0
      · have empty1B : (d1.lookahead == 0) = true := by simp [empty1]
        have availZero : z1.avail_in = 0 := by
          rcases post.stopped with big | zero
          · rw [empty1] at big; exact absurd big (by decide)
          · exact zero
        refine ⟨{ st with brk := true }, after1, ?_,
          ⟨z1, d1, head1, acc1, Or.inr (Or.inr ⟨rfl, ret, pending1, empty1, availZero⟩)⟩, ?_⟩
        · simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
            Bool.false_eq_true, ite_false, empty1B]
          rfl
        · rw [loop_measure_exit (Or.inl rfl), measure0]; omega
      · have empty1B : (d1.lookahead == 0) = false := by simpa using empty1
        have look1 : 1 ≤ d1.lookahead.toNat := by
          have : d1.lookahead.toNat ≠ 0 := fun e => empty1 (UInt32.toNat_inj.mp e)
          omega
        obtain ⟨st', h', iterRun, loop', less⟩ := finishIter head1 acc1 pending1 look1 room1 (by omega)
        refine ⟨st', h', ?_, loop', less⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        simp only [bind_app] at iterRun
        exact iterRun
  · have big : 262 ≤ d.lookahead.toNat := by
      have := small; rw [UInt32.lt_iff_toNat_lt] at this; change ¬ _ < 262 at this; omega
    have room := head.inv.shape.room
    obtain ⟨st', h', iterRun, loop', less⟩ := finishIter head acc pending (by omega) (by omega) (Nat.le_refl _)
    refine ⟨st', h', ?_, loop', less⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    simp only [bind_app] at iterRun
    exact iterRun

/-- The `deflate_slow` loop ends in a `need_more` return or a `break` at the end of the input. -/
theorem slow_loop (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head SlowKind h r ds z d) (pending : d.pending = 0) (flush : Int32) :
    ∃ st h', cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (st, h') ∧
      SlowLoop h d r ds z flush st h' ∧ (st.brk = true ∨ st.ret.isSome = true) := by
  have start : SlowLoop h d r ds z flush {} h :=
    ⟨z, d, head, Fr.refl head.inv.good head.buffers, Or.inl ⟨rfl, rfl, pending⟩⟩
  obtain ⟨st, h', run, loop, exit⟩ := cwhile_measure (cond := forever)
    (body := deflate_slow_body (some (.tab ds)) flush) (SlowLoop h d r ds z flush)
    (fun st h' => SlowLoop h d r ds z flush st h' ∧ (st.brk = true ∨ st.ret.isSome = true)) (loopMeasure r ds)
    (fun st h1 ⟨z1, d1, head1, acc1, cases⟩ => by
      rcases cases with ⟨brk, ret, pending⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending, _, _⟩
      · refine ⟨true, st, h1, (by simp [forever, brk, ret]), (fun _ => ?_), (fun e => by cases e)⟩
        exact slow_body_step safe head head1 acc1 pending flush st brk ret
      · refine ⟨false, st, h1, (by simp [forever, ret]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z1, d1, head1, acc1, Or.inr (Or.inl ⟨ret, why⟩)⟩, Or.inr (by rw [ret]; rfl)⟩
      · refine ⟨false, st, h1, (by simp [forever, brk]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z1, d1, head1, acc1, Or.inr (Or.inr ⟨brk, ret, pending, by assumption, by assumption⟩)⟩, Or.inl brk⟩)
    start (loop_measure_bound r ds {} h)
  exact ⟨st, h', run, loop, exit⟩

/-! ## The end of `deflate_slow` -/

set_option maxHeartbeats 1600000 in
/-- The end of a compression function from a state ready for a block flush that holds symbols:
the last block of a `Z_FINISH` call, or the current block. -/
theorem finish_tail_ready (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} (ready : BlockReady h r ds z d pb buf xs)
    (symbols : d.sym_next ≠ 0) (flush : Int32) (empty : z.avail_in = 0) (quiet : d.match_available = 0)
    (look0 : d.lookahead = 0) :
    ∃ bstate after z' d', finish_tail (some (.tab ds)) flush h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ Fr h r ds d z after z' d' ∧ StratMeaning flush bstate z' d' := by
  by_cases finish : flush = Z_FINISH
  · obtain ⟨opt, produced, after, z', result, run, invA, buffersA, account, keeps, _, idle, _, choiceT, bits,
      fullOut, totalOutF, bufferF, totalInF, shapeF, keysF⟩ := flush_block_macro safe ready true
    have run' : FLUSH_BLOCK (some (.tab ds)) 1 h = .ok (opt, after) := run
    have inA : z'.avail_in = 0 := keeps.availIn.trans empty
    rcases choiceT rfl with none' | started
    · subst none'
      refine ⟨finish_done, after, z', result, ?_, invA, buffersA, (Fr.flush account totalInF totalOutF bufferF shapeF keysF),
        ⟨fun _ => finish, fun _ => ⟨inA, (idle rfl).1, bits rfl rfl⟩, Or.inl inA,
          fun e => by rcases e with e | e <;> exact absurd e (by decide), fun _ => keeps.symNext,
          Or.inr (Or.inr (Or.inr rfl)), fun e => absurd e (by decide), fun e => absurd e (by decide),
          fun _ => keeps.lookahead.trans look0⟩⟩
      simp [finish_tail, finish, bind_app, run']
    · subst started
      refine ⟨finish_started, after, z', result, ?_, invA, buffersA, (Fr.flush account totalInF totalOutF bufferF shapeF keysF),
        ⟨fun _ => finish, fun e => absurd e (by decide), Or.inl inA,
          fun _ => Or.inl (fullOut (Option.some_ne_none _)), fun e => by rcases e with e | e <;> exact absurd e (by decide),
          Or.inr (Or.inr (Or.inl rfl)), fun _ => keeps.symNext, fun e => absurd e (by decide),
          fun _ => keeps.lookahead.trans look0⟩⟩
      simp [finish_tail, finish, bind_app, run']
  · have finishB : (flush == Z_FINISH) = false := by simpa using finish
    have rdSym : rd (some (.tab ds)) (·.sym_next) h = .ok (d.sym_next, h) := by
      simp [rdD_eq, ready.good.live.hs]
    obtain ⟨opt, produced, after, z', result, run, invA, buffersA, account, keeps, _, idleF, choiceF, _, _,
      fullOut, totalOutF, bufferF, totalInF, shapeF, keysF⟩ := flush_block_macro safe ready false
    have run' : FLUSH_BLOCK (some (.tab ds)) 0 h = .ok (opt, after) := run
    have inA : z'.avail_in = 0 := keeps.availIn.trans empty
    rcases choiceF rfl with none' | more
    · subst none'
      refine ⟨block_done, after, z', result, ?_, invA, buffersA, (Fr.flush account totalInF totalOutF bufferF shapeF keysF),
        ⟨fun e => by rcases e with e | e <;> exact absurd e (by decide), fun e => absurd e (by decide),
          Or.inl inA, fun e => by rcases e with e | e <;> exact absurd e (by decide), fun _ => keeps.symNext,
          Or.inr (Or.inl rfl), fun e => absurd e (by decide),
          fun _ => ⟨(idleF rfl).1, keeps.matchAvailable.trans quiet, finish⟩,
          fun e => by rcases e with e | e <;> exact absurd e (by decide)⟩⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols, run']
    · subst more
      refine ⟨need_more, after, z', result, ?_, invA, buffersA, (Fr.flush account totalInF totalOutF bufferF shapeF keysF),
        need_more_meaning (Or.inl (fullOut (Option.some_ne_none _)))⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols, run']

/-- The state after the last pending literal: no literal pending, and the insertion count of the
end of the input. -/
def endState (x : DeflateState) : DeflateState :=
  { x with match_available := 0, insert := if x.strstart < MIN_MATCH_u - 1 then x.strstart else MIN_MATCH_u - 1 }

set_option maxHeartbeats 8000000 in
/-- **The last pending literal of `deflate_slow`**: at the end of the input, the byte at
`strstart - 1` is tallied, `match_available` cleared and `insert` set. The state is ready for the
block flush of `finish_tail`, and holds a symbol. -/
theorem slow_end_literal {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head SlowKind h r ds z d) (pending : d.pending = 0) (empty : d.lookahead = 0)
    (avail : d.match_available ≠ 0) :
    ∃ c b buf xs h3, index8 d.window (d.strstart - 1).toNat h = .ok (c, h) ∧
      tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end, h3) ∧
      h3.dstates ds = some (literalState d c) ∧
      BlockReady (setD (setD h3 ds { literalState d c with match_available := 0 }) ds (endState (literalState d c)))
        r ds z (endState (literalState d c)) b buf xs ∧
      (endState (literalState d c)).sym_next ≠ 0 ∧ PrivStep h h3 r ds d := by
  have inv := head.inv
  have shape := inv.shape
  have level := head.level
  have kind := head.kind
  have room := shape.room
  have one : d.match_available = 1 := by
    rcases shape.matchAvailable with e | e
    · exact absurd e avail
    · exact e
  have s1 : 1 ≤ d.strstart.toNat := shape.available avail
  have laZero : d.lookahead.toNat = 0 := by rw [empty]; rfl
  obtain ⟨w, wa, win, getW, sizeW⟩ := window_block inv.good
  have back : (d.strstart - 1).toNat = d.strstart.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using s1))
  have readC : index8 d.window (d.strstart - 1).toNat h = .ok (bfn wa (d.strstart.toNat - 1), h) := by
    rw [win, back]; exact index8_bfn getW (by simp) (by omega)
  obtain ⟨c, cdef⟩ : ∃ x, x = bfn wa (d.strstart.toNat - 1) := ⟨_, rfl⟩
  rw [← cdef] at readC
  obtain ⟨⟨xs, ⟨b, buf, pbuf, getB, ledger⟩, dist⟩, clear, _⟩ := inv.symbols
  have trees : TreesInvAt h ds d b buf := trees_at_of_good inv.good pbuf getB
  have roomT := literal_room inv.good.inv shape.symRoom
  have tallyRun := tally_literal_run trees.base c roomT
  let X := literalState d c
  obtain ⟨h3, h3def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds X := ⟨_, rfl⟩
  rw [← h3def] at tallyRun
  have good3 : DGood h3 r ds z X := by rw [h3def]; exact literal_good_after inv.good trees c roomT
  have ledger3 := ledger_literal trees.base ledger roomT c
  have count3 := literal_count trees.base roomT c
  have buffers3 : StreamBuffers h3 r := by
    rw [h3def]; rw [h3def] at good3
    exact private_write_buffers inv.good head.buffers pbuf ⟨rfl, rfl, rfl, rfl⟩ good3
  have chains3 : HeapChains h3 X (chainTop d) := by
    rw [h3def]; exact pending_write_chains inv.good (inv.chains level) pbuf _ c
  let X1 : DeflateState := { X with match_available := 0 }
  let F := endState X
  obtain ⟨h5, h5def⟩ : ∃ x, x = setD (setD h3 ds X1) ds F := ⟨_, rfl⟩
  have good4 : DGood (setD h3 ds X1) r ds z X1 := engine_update_good good3 rfl
  have good5 : DGood h5 r ds z F := by rw [h5def]; exact engine_update_good good4 rfl
  have buffers4 : StreamBuffers (setD h3 ds X1) r := state_write_buffers good3 buffers3 ⟨rfl, rfl, rfl, rfl⟩ good4
  have buffers5 : StreamBuffers h5 r := by
    rw [h5def]; exact state_write_buffers good4 buffers4 ⟨rfl, rfl, rfl, rfl⟩ (by rw [← h5def]; exact good5)
  have getB5 : h5.bytes b = some (literalBytes buf d c) := by
    rw [h5def, h3def]; simp [Zlib.Trees.Proofs.Out.setB]
  have insN : F.insert.toNat = min d.strstart.toNat 2 := by
    show (if d.strstart < MIN_MATCH_u - 1 then d.strstart else MIN_MATCH_u - 1).toNat = _
    split
    · rename_i lt
      have := UInt32.lt_iff_toNat_lt.mp lt
      change d.strstart.toNat < 2 at this
      omega
    · rename_i nlt
      have : ¬ d.strstart.toNat < 2 := fun c => nlt (UInt32.lt_iff_toNat_lt.mpr c)
      change 2 = _
      omega
  have laF : F.lookahead.toNat = 0 := laZero
  have shapeF : Shape (flushedState F) := by
    refine flushed_shape (d := F) (by show d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat; exact room)
      (by rw [insN]; show _ ≤ d.strstart.toNat; omega) (fun large => by rw [laF] at large; omega)
      shape.prevLength shape.matchLength (Or.inl rfl) (fun zero => absurd zero level)
      (fun ne => absurd rfl ne) ?_ ?_ shape.highWater shape.windowInit shape.lastFlush shape.headerFlush
      shape.trailer shape.biValid shape.cursor (by show 0 < d.sym_end.toNat; have := shape.symRoom; omega)
      shape.slides shape.lazyPrev (fun ne => absurd rfl ne) rfl
    · intro large
      exact absurd (shape.pendingMatch large).2.2.1 (by change 3 ≤ d.match_length.toNat at large; omega)
    · intro _ hi
      exact absurd (show 4 ≤ d.level.toInt from kind.1) (by change d.level.toInt ≤ 3 at hi; omega)
  have hashingF : Hashing h5 F := by
    refine ⟨fun _ => ?_, fun one' => ?_, fun _ _ large => ?_⟩
    · obtain ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, H⟩ := chains3
      refine ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, by rw [h5def]; simpa using hw0, by rw [h5def]; simpa using hp0,
        by rw [h5def]; simpa using hq0, chains_mono H ?_ (Nat.le_refl _)⟩
      unfold chainTop
      change min (d.strstart.toNat - d.insert.toNat) (d.strstart.toNat + d.lookahead.toNat - 2) ≤
        min (d.strstart.toNat - F.insert.toNat) (d.strstart.toNat + d.lookahead.toNat - 2)
      rw [insN, laZero]; omega
    · change d.«matches» = 1 at one'
      rw [shape.slides.2 level] at one'; cases one'
    · rw [laF] at large; omega
  refine ⟨c, b, literalBytes buf d c, xs ++ [⟨0, c.toNat⟩], h3, readC, tallyRun, good3.live.hs,
    ?_, ?_, by rw [h3def]; exact priv_tally inv.good pbuf _ X⟩
  · rw [← h5def]
    refine ⟨good5, inv.alloc, by unfold LibraryGlobals; rw [h5def, h3def]; exact inv.globals,
      trees_at_of_good good5 pbuf getB5, ledger3.keep rfl rfl rfl rfl, ⟨clear.bl, clear.opt, clear.fixed⟩,
      shapeF, hashingF, pending, by show -(2 : Int) ^ 62 ≤ d.block_start.toInt; exact block_start_low inv level,
      by show d.block_start.toInt ≤ d.strstart.toNat; exact shape.blockStart, level, buffers5, head.out⟩
  · intro zero
    have := count3
    change F.sym_next.toNat = d.sym_next.toNat + 3 at this
    rw [zero] at this
    simp at this

/-- **`deflate_slow` keeps the invariant**, given the block flush, with the stream accounting. -/
theorem slow_spec_of (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StratIn h r z d) (flush : Int32)
    (slow : 4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_slow (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ Fr h r ds d z after z' d' ∧
      StratMeaning flush bstate z' d' := by
  have level : d.level ≠ 0 := by
    intro zero; have := slow.1; rw [zero] at this; exact absurd this (by decide)
  have head : Head SlowKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, slow⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, acc1, cases⟩, exit⟩ := slow_loop safe head entry.pending flush
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1, avail1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv, head1.buffers, acc1, need_more_meaning why⟩
    simp [C.run, deflate_slow, bind_app, loopRun, ret]
  · have ld1 : ldDeflateState (some (.tab ds)) h1 = .ok (d1, h1) := ldDeflateState_tab head1.inv.good.live.hs
    by_cases avail : d1.match_available ≠ 0
    · have availB : (d1.match_available != 0) = true := by simpa using avail
      obtain ⟨c, b, buf, xs, h3, readC, tallyRun, state3, ready, symbols, priv3⟩ :=
        slow_end_literal head1 pending1 empty1 avail
      obtain ⟨bstate, after, z', d', tailRun, invA, buffersA, accT, meanT⟩ :=
        finish_tail_ready safe ready symbols flush avail1 rfl empty1
      have pre : Fr h1 r ds d1 z1
          (setD (setD h3 ds { literalState d1 c with match_available := 0 }) ds (endState (literalState d1 c))) z1
          (endState (literalState d1 c)) :=
        Fr.priv head1.inv.good head1.buffers
          ((priv3.trans (priv_setD h3 r ds d1 _ state3)).trans (priv_setD _ r ds d1 _ (setD_dstates_same _ _ _)))
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨bstate, after, z', d', ?_, invA, buffersA,
        Fr.trans inv.good entry.buffers acc1 (Fr.trans head1.inv.good head1.buffers pre accT), meanT⟩
      have wr1 : wr (some (.tab ds)) (fun d => { d with match_available := 0 }) h3 =
          .ok ((), setD h3 ds { literalState d1 c with match_available := 0 }) := by rw [wrD_eq, state3]
      have wr2 : wr (some (.tab ds)) (fun d => { d with insert := if d.strstart < MIN_MATCH_u - 1 then d.strstart else MIN_MATCH_u - 1 })
          (setD h3 ds { literalState d1 c with match_available := 0 }) =
          .ok ((), setD (setD h3 ds { literalState d1 c with match_available := 0 }) ds (endState (literalState d1 c))) := by
        rw [wrD_eq]; simp; rfl
      simp only [C.run, deflate_slow, bind_app, loopRun, ret, ld1, availB, ite_true, readC, tallyRun, wr1, wr2]
      exact tailRun
    · have idle : d1.match_available = 0 := by simpa using avail
      have availB : (d1.match_available != 0) = false := by simp [idle]
      obtain ⟨wrRun, head2⟩ := set_insert_head head1 empty1 (fun _ k => k)
      obtain ⟨bstate, after, z', d', tailRun, invA, buffersA, accT, meanT⟩ := finish_tail_inv safe head2 pending1 flush avail1 idle empty1
      have ins : Fr h1 r ds d1 z1
          (setD h1 ds { d1 with insert := if d1.strstart < MIN_MATCH_u - 1 then d1.strstart else MIN_MATCH_u - 1 }) z1
          { d1 with insert := if d1.strstart < MIN_MATCH_u - 1 then d1.strstart else MIN_MATCH_u - 1 } :=
        Fr.priv head1.inv.good head1.buffers (priv_setD h1 r ds d1 _ head1.inv.good.live.hs) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨bstate, after, z', d', ?_, invA, buffersA,
        Fr.trans inv.good entry.buffers acc1 (Fr.trans head1.inv.good head1.buffers ins accT), meanT⟩
      simp only [C.run, deflate_slow, bind_app, loopRun, ret, ld1, availB, Bool.false_eq_true, ite_false, wrRun]
      exact tailRun

/-- **`slow_spec`**: `deflate_slow` (levels 4 to 9 with a hashing strategy) keeps the invariant for
every parameter tuple and flush value, with the stream accounting, given the pending-buffer
overlay that batch C proves for every memLevel. -/
theorem slow_spec (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (slow : 4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_slow (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ Fr h r ds d z after z' d' ∧
      StratMeaning flush bstate z' d' :=
  slow_spec_of (Block.flushSafe_of_tiny tiny) inv entry.toIn flush slow

end Zlib.Deflate.Universal
