import ZlibF.Proof.«deflate.c.universal-ops-params»
import ZlibF.Proof.«deflate.c.universal-ops-dispatch»
import ZlibF.Proof.«deflate.c.universal-ops-header»
import ZlibF.Proof.«deflate.c.universal-strategy-frame»
import ZlibF.Proof.«deflate.c.universal-strategies»
import ZlibF.Proof.«deflate.c.universal-stored-loop»

/-!
# deflate.c: `deflateParams` keeps the invariant, every case (inflate batch 1)

Batch B proved the refusals and the change without a flush (`step_params_refuse`,
`step_params_same`, `deflate.c.universal-ops-params`). This file proves the rest:

* a change of the strategy or of the compression function before the first `deflate` call
  (`last_flush = -2`): no flush, the level and strategy change at once;
* the same change after a `deflate` call: `deflate(Z_BLOCK)` first, `Z_BUF_ERROR` unless all
  input is consumed and the block is empty, then the change;
* the table repair of a level-0 stream: `slide_hash` for one pending slide, `CLEAR_HASH` for more.

The inner `deflate` call is the skeleton's `deflate_call`, a hypothesis here with the statement
`operation_step_of` uses. The state facts the change reads are `Shape`'s P2, P3 and P6
(`lazyPrev`, `symBlock`, `lazyStart`) and, before the first `deflate` call, `CallFacts`' P1 and
P1b (`fresh`, `freshStart`): `CallFacts d` is a hypothesis of the entry state, carried beside
`DInv` between calls. One fact is not in `DInv` yet; it is a premise named for what it awaits:

* `SlideRepair`: with one pending slide the slid chains hold at `chainTop`, the frontier of
  `Chains`. The current `SlidChains` uses the higher frontier `strstart - insert` (batch B's
  Finding 2), so it does not give `Chains` after `slide_hash`; at `chainTop` the repair is a
  congruence (`slide_repair`).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-! ## 1. The premise awaiting the deflate owner's `DInv` change -/

/-- `head` and `prev` after `slide_hash`: every entry of the old tables read through `slideVal`;
the window is unchanged. -/
def SlidTables (h h' : Heap) (d : DeflateState) : Prop :=
  ∃ w p q wa pa qa pa' qa',
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h'.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    h'.words p = some pa' ∧ h'.words q = some qa' ∧
    (∀ i, i < d.hash_size.toNat → wfn qa' i = slideVal d.w_size (wfn qa i)) ∧
    (∀ i, i < d.w_size.toNat → wfn pa' i = slideVal d.w_size (wfn pa i))

/-- `SlidChains` at the frontier of `Chains` (`chainTop`). The current `SlidChains` uses
`strstart - insert`, which is higher when `insert < 2` (reachable at level 0 with one pending
slide; batch B's Finding 2), so it does not give `Chains` after `slide_hash`. -/
def SlidChainsTop (h : Heap) (d : DeflateState) : Prop :=
  ∃ w p q wa pa qa,
    d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
    h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧
    HashChains (fun i => slideVal d.w_size (wfn qa i)) (fun i => slideVal d.w_size (wfn pa i))
      (bfn wa) d.hash_size d.hash_shift d.hash_mask d.w_size.toNat (chainTop d)
      (d.strstart.toNat + d.lookahead.toNat)

/-- **Awaiting the deflate owner's DInv change.** With one pending slide, the slid view of the
chains holds at `chainTop`. Checked on the real C after every call of 30000 random histories
(no failure, including the 7 states with `insert < 2`; side notes, batch1-deflate-dinv-checks). -/
def SlideRepair : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → d.«matches» = 1 → SlidChainsTop h d

/-! ## 2. The repair is a congruence -/

/-- Reachability reads `head` below `n` and `prev` below `ws` only. -/
theorem reach_bounded {h1 p1 h2 p2 : Nat → UInt16} {n : UInt32} {ws top k p : Nat} (pos : 0 < ws)
    (heads : ∀ i, i < n.toNat → h2 i = h1 i) (prevs : ∀ i, i < ws → p2 i = p1 i) (hk : k < n.toNat)
    (reach : Reach h2 p2 ws top k p) : Reach h1 p1 ws top k p := by
  induction reach with
  | head => rw [heads k hk]; exact Reach.head
  | @step q _ hq ht ih =>
    have lt : q &&& (ws - 1) < ws := Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
    rw [prevs _ lt]
    exact Reach.step ih hq ht

/-- The chain invariant reads `head` below `n` and `prev` below `ws` only. -/
theorem chains_bounded {h1 p1 h2 p2 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm : UInt32}
    {ws top lim : Nat} (pos : 0 < ws) (H : HashChains h1 p1 w n hsh hm ws top lim)
    (heads : ∀ i, i < n.toNat → h2 i = h1 i) (prevs : ∀ i, i < ws → p2 i = p1 i) :
    HashChains h2 p2 w n hsh hm ws top lim := by
  refine ⟨fun k p hk reach p0 tp => ?_⟩
  obtain ⟨a, b, c, e⟩ := H.node k p hk (reach_bounded pos heads prevs hk reach) p0 tp
  have lt : p &&& (ws - 1) < ws := Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
  exact ⟨a, b, c, by rw [prevs _ lt]; exact e⟩

/-- **The level-0 repair**: after `slide_hash` the slid view is the table, so the slid chains at
`chainTop` are the chains of a state with the same window, tables, positions and hash
parameters. -/
theorem slide_repair {h h' : Heap} {d d' : DeflateState} (tables : SlidTables h h' d)
    (wsPos : 0 < d.w_size.toNat)
    (win : d'.window = d.window) (prv : d'.prev = d.prev) (hd : d'.head = d.head)
    (ss : d'.strstart = d.strstart) (ins : d'.insert = d.insert) (la : d'.lookahead = d.lookahead)
    (n : d'.hash_size = d.hash_size) (hsh : d'.hash_shift = d.hash_shift) (hm : d'.hash_mask = d.hash_mask)
    (ws : d'.w_size = d.w_size) (slid : SlidChainsTop h d) : Chains h' d' := by
  obtain ⟨w, p, q, wa, pa, qa, pa', qa', ew, ep, eq, hw, hw', hp, hq, hp', hq', heads, prevs⟩ := tables
  obtain ⟨w1, p1, q1, wa1, pa1, qa1, ew1, ep1, eq1, hw1, hp1, hq1, H⟩ := slid
  rw [ew] at ew1; rw [ep] at ep1; rw [eq] at eq1
  cases ew1; cases ep1; cases eq1
  rw [hw] at hw1; rw [hp] at hp1; rw [hq] at hq1
  cases hw1; cases hp1; cases hq1
  refine ⟨w, p, q, wa, pa', qa', by rw [win, ew], by rw [prv, ep], by rw [hd, eq], hw', hp', hq', ?_⟩
  have top : chainTop d' = chainTop d := by unfold chainTop; rw [ss, ins, la]
  rw [top, n, hsh, hm, ws, ss, la]
  exact chains_bounded wsPos H heads prevs

/-! ## 3. The tail after the flush -/

/-- The state of `deflateParams` when it changes the strategy or the compression function: no
lookahead, no symbols, no lazy match, and the block starts at `strstart`. -/
structure Flushed (d : DeflateState) : Prop where
  lookahead : d.lookahead = 0
  symbols : d.sym_next = 0
  available : d.match_available = 0
  matchLength : d.match_length.toNat ≤ 2
  prevLength : d.prev_length.toNat ≤ 2
  block : d.block_start.toInt = d.strstart.toNat

/-- Before the first `deflate` call (P1, P1b). -/
theorem Flushed.of_reset {d : DeflateState} (calls : CallFacts d) (reset : d.last_flush = -2) :
    Flushed d := by
  obtain ⟨la, sym, ma, ml, pl, _⟩ := calls.fresh reset
  exact ⟨la, sym, ma, ml, pl, calls.freshStart reset⟩

/-- After the flush test of `deflateParams` (P2, P3, P6, `pendingMatch`). -/
theorem Flushed.of_empty {d : DeflateState} (shape : Shape d)
    (la : d.lookahead = 0) (block : d.block_start.toInt = d.strstart.toNat) : Flushed d := by
  have sym : d.sym_next = 0 := by
    refine Classical.byContradiction fun ne => ?_; have := shape.symBlock ne; omega
  have ma : d.match_available = 0 := by
    refine Classical.byContradiction fun ne => ?_; have := shape.lazyStart ne; omega
  have ml : d.match_length.toNat ≤ 2 := by
    refine Classical.byContradiction fun big => ?_
    have := (shape.pendingMatch (by omega)).2.2.1
    rw [la] at this; simp at this; omega
  have pl : d.prev_length.toNat ≤ 2 := by
    refine Classical.byContradiction fun big => ?_
    have := (shape.lazyPrev (by omega)).2.2.2
    omega
  exact ⟨la, sym, ma, ml, pl, block⟩

/-- The state after a level change: the repair cleared `matches` (and set `slid`), then the
tuning of the new level and the strategy. -/
def paramsFinal (d : DeflateState) (s : Int32) (level strategy : Int32) (c : Config) : DeflateState :=
  paramsState { d with «matches» := 0, slid := s } level strategy c

/-- The shape after a level change, from a flushed state. -/
theorem shape_final {d : DeflateState} (shape : Shape d) (flushed : Flushed d) (s : Int32)
    (lv strategy : Int32) (c : Config) : Shape (paramsFinal d s lv strategy c) := by
  have bs := flushed.block
  have ma := flushed.available
  have la := flushed.lookahead
  have sym := flushed.symbols
  refine ⟨shape.room, shape.insert, shape.insertDone, shape.prevLength, shape.matchLength,
    shape.matchAvailable, shape.blockStart, ?_, ?_, shape.available, shape.pendingMatch, ?_,
    shape.highWater, shape.windowInit, shape.lastFlush, shape.headerFlush, shape.trailer, shape.biValid,
    shape.cursor, shape.symRoom, ?_, fun large => absurd large (by show ¬ 3 ≤ d.prev_length.toNat; have := flushed.prevLength; omega),
    fun nz => absurd sym nz, fun nz => absurd ma nz, fun nz => absurd ma nz⟩
  · intro _
    change (d.strstart.toNat : Int) - d.block_start.toInt ≤ 258 * (d.sym_next.toNat / 3 : Nat) + d.match_available.toInt
    have m0 : d.match_available.toInt = 0 := by rw [ma]; rfl
    rw [bs, m0]; omega
  · intro _
    change 0 ≤ d.block_start.toInt ∧ d.lookahead = 0 ∧ d.sym_next = 0
    exact ⟨by rw [bs]; omega, la, sym⟩
  · intro _ _ _ _
    exact ⟨flushed.matchLength, flushed.prevLength⟩
  · exact ⟨show (0 : UInt32).toNat ≤ 2 by decide, fun _ => rfl⟩

/-- The shape after a strategy change at the same level, from a flushed state. -/
theorem shape_strategy {d : DeflateState} (shape : Shape d) (flushed : Flushed d) (strategy : Int32) :
    Shape { d with strategy } :=
  ⟨shape.room, shape.insert, shape.insertDone, shape.prevLength, shape.matchLength,
    shape.matchAvailable, shape.blockStart, shape.blockSpan, shape.levelZero, shape.available,
    shape.pendingMatch, fun _ _ _ _ => ⟨flushed.matchLength, flushed.prevLength⟩, shape.highWater,
    shape.windowInit, shape.lastFlush, shape.headerFlush, shape.trailer, shape.biValid, shape.cursor,
    shape.symRoom, shape.slides, fun large => absurd large (by show ¬ 3 ≤ d.prev_length.toNat; have := flushed.prevLength; omega),
    fun nz => absurd flushed.symbols nz, fun nz => absurd flushed.available nz, fun nz => absurd flushed.available nz⟩

/-- The symbol facts across a change of fields the symbols do not read, on a heap with the same
bytes. -/
theorem symbols_keep {h h' : Heap} {d d' : DeflateState} (symbols : Symbols h d) (bytes : h'.bytes = h.bytes)
    (pbuf : d'.pending_buf = d.pending_buf) (sym : d'.sym_next = d.sym_next) (lit : d'.lit_bufsize = d.lit_bufsize)
    (ws : d'.w_size = d.w_size)
    (lt : d'.dyn_ltree = d.dyn_ltree) (dt : d'.dyn_dtree = d.dyn_dtree) (bl : d'.bl_tree = d.bl_tree)
    (opt : d'.opt_len = d.opt_len) (st : d'.static_len = d.static_len)
    (po : d'.pending_out = d.pending_out) (pend : d'.pending = d.pending) : Symbols h' d' := by
  obtain ⟨⟨xs, ⟨b, a, pb, hb, ledger⟩, near⟩, clear, below⟩ := symbols
  refine ⟨⟨xs, ⟨b, a, by rw [pbuf]; exact pb, by rw [bytes]; exact hb, ledger.keep sym lit lt dt⟩,
    by rw [ws]; exact near⟩, ⟨by rw [bl]; exact clear.bl, by rw [opt]; exact clear.opt,
    by rw [st]; exact clear.fixed⟩, ?_⟩
  intro b' off e ne
  rw [po] at e; rw [sym] at ne
  rw [pend, lit]
  exact below b' off e ne

/-- What the tail of `deflateParams` gives: the run, the invariant, and its footprint (the state
record and the `head`/`prev` tables). -/
def TailOk (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) (run : M Int32) : Prop :=
  ∃ after dF, run h = .ok (Z_OK, after) ∧ DInv after r ds z dF ∧ Zlib.Deflate.Proofs.Shape h after ∧
    Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
    after.bytes = h.bytes ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
    (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) ∧
    (∀ b, DeflateOwned ds dF b ↔ DeflateOwned ds d b) ∧
    dF.status = d.status ∧ dF.sym_next = d.sym_next ∧ dF.gzhead = d.gzhead

/-- A state store over a heap with changed words keeps every byte view. -/
theorem views_setD {h hW : Heap} {ds : Nat} {d d' : DeflateState} (hs : h.dstates ds = some d)
    (depth : d'.depth = d.depth) (bytes : hW.bytes = h.bytes) (dst : hW.dstates = h.dstates)
    (borrow : hW.libcErrorBorrow = h.libcErrorBorrow) (static : hW.static = h.static) (ref : BRef) :
    (Space.get (setD hW ds d') ref : Option (Array UInt8)) = Space.get h ref := by
  cases ref with
  | blk b => change (setD hW ds d').bytes b = h.bytes b; rw [setD_bytes, bytes]
  | str i =>
    change staticStringBytes (setD hW ds d') i = staticStringBytes h i
    unfold staticStringBytes
    rw [show (setD hW ds d').libcErrorBorrow = h.libcErrorBorrow from borrow]
  | dstate_depth i =>
    change ((setD hW ds d').dstates i).map (·.depth) = (h.dstates i).map (·.depth)
    by_cases e : i = ds
    · subst e; rw [setD_dstates_same, hs]; simp [depth]
    · rw [setD_dstates_ne _ _ _ _ e, dst]
  | st_dist_code =>
    change some (setD hW ds d').static.dist_code = some h.static.dist_code
    rw [show (setD hW ds d').static = h.static from static]
  | st_length_code =>
    change some (setD hW ds d').static.length_code = some h.static.length_code
    rw [show (setD hW ds d').static = h.static from static]

theorem depth_setD {h : Heap} {ds : Nat} {d d' : DeflateState} (hs : h.dstates ds = some d)
    (depth : d'.depth = d.depth) (i : Nat) :
    ((setD h ds d').dstates i).map (·.depth) = (h.dstates i).map (·.depth) := by
  by_cases e : i = ds
  · subst e; rw [setD_dstates_same, hs]; simp [depth]
  · rw [setD_dstates_ne _ _ _ _ e]

theorem owned_frame_setD (h : Heap) (r : ZStreamRef) (ds : Nat) (d d' : DeflateState) :
    Frame h (setD h ds d') (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
  full_frame_weaken (state_store_full_frame h ds d') (fun _ e => Or.inr (Or.inl e))

/-- The run of the tail on a table heap `hW` (tables changed, state as before): the final state
record and its invariant. -/
theorem tail_final {h hW : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (flushed : Flushed d) (goodW : DGood hW r ds z d)
    (bytes : hW.bytes = h.bytes) (static : hW.static = h.static) (s : Int32) (lv strategy : Int32)
    (lo : 0 ≤ lv.toInt) (hi : lv.toInt ≤ 9) (slo : 0 ≤ strategy.toInt) (shi : strategy.toInt ≤ 4)
    (chains : Chains hW (paramsFinal d s lv strategy configuration_table[lv.toInt.toNat]!)) :
    DInv (setD hW ds (paramsFinal d s lv strategy configuration_table[lv.toInt.toNat]!)) r ds z
      (paramsFinal d s lv strategy configuration_table[lv.toInt.toNat]!) := by
  let dF := paramsFinal d s lv strategy configuration_table[lv.toInt.toNat]!
  have invF : DStInv hW ds dF :=
    { goodW.inv with blocks := goodW.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, level_lo := lo, level_hi := hi, strat_lo := slo, strat_hi := shi }
  have goodF : DGood (setD hW ds dF) r ds z dF := goodW.setD' rfl goodW.live.status invF (by trkeep)
  refine ⟨goodF, inv.alloc, ?_, shape_final inv.shape flushed s lv strategy _, ?_, ?_⟩
  · unfold LibraryGlobals at *; rw [show (setD hW ds dF).static = h.static from static]; exact inv.globals
  · refine ⟨fun _ => chains, fun one => absurd one (show ¬ (0 : UInt32) = 1 by decide), fun _ _ large => ?_⟩
    change 3 ≤ d.lookahead.toNat at large
    rw [flushed.lookahead] at large; exact absurd large (by decide)
  · exact symbols_keep inv.symbols bytes rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

set_option maxHeartbeats 8000000 in
/-- **The tail of `deflateParams`** from a flushed state: the level change with the table repair
of a level-0 stream (`slide_hash`, `CLEAR_HASH`), the tuning of the new level, and the strategy. -/
theorem params_tail {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (repair : SlideRepair) (inv : DInv h r ds z d) (flushed : Flushed d) (lv strategy : Int32)
    (lo : 0 ≤ lv.toInt) (hi : lv.toInt ≤ 9) (slo : 0 ≤ strategy.toInt) (shi : strategy.toInt ≤ 4) :
    TailOk h r ds z d (paramsTail (some (.tab ds)) lv strategy) := by
  have good := inv.good
  have shape := inv.shape
  have ldRun : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  have cfgL := config_at_run h lo hi
  have cfgAll : ∀ g, config_at lv g = .ok (configuration_table[lv.toInt.toNat]!, g) := fun g => config_at_run g lo hi
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, hw, _⟩ := blocks.wa
  obtain ⟨pa, hp, pSize⟩ := blocks.pa
  obtain ⟨qa, hq, qSize⟩ := blocks.qa
  have hashLo : 1 ≤ d.hash_size.toNat := by rw [good.inv.hsize]; exact Nat.one_le_two_pow
  have wsLo : 1 ≤ d.w_size.toNat := by rw [good.inv.wsize]; exact Nat.one_le_two_pow
  let c := configuration_table[lv.toInt.toNat]!
  by_cases sameLevel : d.level = lv
  · -- the strategy only
    have levelB : (d.level != lv) = false := by simp [sameLevel]
    let dA : DeflateState := { d with strategy }
    have tailRun : paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, setD h ds dA) := by
      unfold paramsTail
      simp only [bind_app, ldRun, levelB, Bool.false_eq_true, ite_false, wrD_eq, good.live.hs]
      rfl
    have invA : DStInv h ds dA :=
      { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, strat_lo := slo, strat_hi := shi }
    have goodA : DGood (setD h ds dA) r ds z dA := good.setD' rfl good.live.status invA (by trkeep)
    refine ⟨setD h ds dA, dA, tailRun, inv.of_fields goodA (fun _ => shape_strategy shape flushed strategy) ?_
      (fun sy => symbols_keep sy rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl),
      shape_setD good.live.hs _, owned_frame_setD h r ds d dA, rfl, rfl, rfl,
      views_setD good.live.hs rfl rfl rfl rfl rfl, fun _ => Iff.rfl, rfl, rfl, rfl⟩
    intro hashing
    refine ⟨hashing.chains, hashing.slid, fun _ _ large => ?_⟩
    change 3 ≤ d.lookahead.toNat at large
    rw [flushed.lookahead] at large; exact absurd large (by decide)
  have levelB : (d.level != lv) = true := by simpa using sameLevel
  by_cases repairNeeded : d.level = 0 ∧ d.«matches» ≠ 0
  · have zeroB : (d.level == 0 && d.«matches» != 0) = true := by simp [repairNeeded.1, repairNeeded.2]
    by_cases one : d.«matches» = 1
    · -- one pending slide: slide_hash
      have oneB : (d.«matches» == 1) = true := by simp [one]
      obtain ⟨qa', pa', slideRun, qs, ps, qv, pv⟩ := slide_hash_ok good.live.hs blocks.head blocks.prev hq hp
        blocks.pq.symm (by omega) (by omega) hashLo wsLo
      let hW : Heap := { h with words := upd (upd h.words q (some qa')) p (some pa') }
      have slideRun' : slide_hash (some (.tab ds)) h = .ok ((), setD hW ds { d with slid := 1 }) := by
        rw [slideRun]; rfl
      let dF := paramsFinal d 1 lv strategy c
      have tailRun : paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, setD hW ds dF) := by
        unfold paramsTail
        simp only [bind_app, ldRun, levelB, ite_true, zeroB, oneB, slideRun', wrD_eq, setD_dstates_same,
          setD_setD, cfgAll]
        rfl
      have good1 : DGood { h with words := upd h.words q (some qa') } r ds z d :=
        good.words_set q qa' qa hq qs
      have hp1 : ({ h with words := upd h.words q (some qa') } : Heap).words p = some pa := by
        simp [upd_ne _ _ _ _ blocks.pq, hp]
      have goodW : DGood hW r ds z d := good1.words_set p pa' pa hp1 ps
      have hpW : hW.words p = some pa' := by simp [hW]
      have hqW : hW.words q = some qa' := by simp [hW, upd_ne _ _ _ _ blocks.pq.symm]
      have tables : SlidTables h hW d :=
        ⟨w, p, q, wa, pa, qa, pa', qa', blocks.win, blocks.prev, blocks.head, hw, hw, hp, hq, hpW, hqW,
          fun i hi => by rw [qv i, if_pos hi], fun i hi => by rw [pv i, if_pos hi]⟩
      have chains : Chains hW dF := slide_repair tables (by omega) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (repair inv one)
      have shapeW : Zlib.Deflate.Proofs.Shape h hW :=
        (shape_setW hq qa').trans (shape_setW hp1 pa')
      have frameW : Frame h hW (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
        have f1 := full_frame_weaken (word_store_full_frame h q qa')
          (fun x e => show StreamRoot r x ∨ DeflateOwned ds d x from
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; exact blocks.head))))))
        have f2 := full_frame_weaken (word_store_full_frame (setW h q qa') p pa')
          (fun x e => show StreamRoot r x ∨ DeflateOwned ds d x from
            Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; exact blocks.prev)))))
        exact full_frame_trans_shape f1 f2 (shape_setW hq qa')
      refine ⟨setD hW ds dF, dF, tailRun,
        tail_final inv flushed goodW rfl rfl 1 lv strategy lo hi slo shi chains,
        shapeW.trans (shape_setD goodW.live.hs _),
        full_frame_trans_shape frameW (owned_frame_setD hW r ds d dF) shapeW, rfl, rfl, rfl,
        views_setD good.live.hs rfl rfl rfl rfl rfl, fun _ => Iff.rfl, rfl, rfl, rfl⟩
    · -- more pending slides: CLEAR_HASH
      have oneB : (d.«matches» == 1) = false := by simp [one]
      have clearRun := clearHash_run good.live.hs blocks.head hq hashLo (by omega)
      let hW : Heap := setW h q (clearHead qa d.hash_size.toNat)
      let dF := paramsFinal d 0 lv strategy c
      have tailRun : paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, setD hW ds dF) := by
        unfold paramsTail
        simp only [bind_app, ldRun, levelB, ite_true, zeroB, oneB, Bool.false_eq_true, ite_false, clearRun,
          wrD_eq, setD_dstates_same, setD_setD, cfgAll]
        rfl
      have goodW : DGood hW r ds z d := good.words_set q _ qa hq (size_clearHead _ _)
      have chains : Chains hW dF := by
        have hpW : hW.words p = some pa := by simp [hW, setW, upd_ne _ _ _ _ blocks.pq, hp]
        refine ⟨w, p, q, wa, pa, clearHead qa d.hash_size.toNat, blocks.win, blocks.prev, blocks.head, hw, hpW,
          by simp [hW], ?_⟩
        apply chains_empty
        intro k hk
        have zero := clear_head_zero qa d.hash_size.toNat (by omega) (by omega) k hk
        simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]
      have shapeW : Zlib.Deflate.Proofs.Shape h hW := shape_setW hq _
      have frameW : Frame h hW (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
        full_frame_weaken (word_store_full_frame h q _)
          (fun x e => show StreamRoot r x ∨ DeflateOwned ds d x from
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; exact blocks.head))))))
      refine ⟨setD hW ds dF, dF, tailRun,
        tail_final inv flushed goodW rfl rfl 0 lv strategy lo hi slo shi chains,
        shapeW.trans (shape_setD goodW.live.hs _),
        full_frame_trans_shape frameW (owned_frame_setD hW r ds d dF) shapeW, rfl, rfl, rfl,
        views_setD good.live.hs rfl rfl rfl rfl rfl, fun _ => Iff.rfl, rfl, rfl, rfl⟩
  · -- no repair: the pending slides are none
    have zeroB : (d.level == 0 && d.«matches» != 0) = false := by
      by_cases l0 : d.level = 0
      · have : d.«matches» = 0 := by
          refine Classical.byContradiction fun ne => ?_; exact repairNeeded ⟨l0, ne⟩
        simp [this]
      · simp [l0]
    have m0 : d.«matches» = 0 := by
      by_cases l0 : d.level = 0
      · refine Classical.byContradiction fun ne => ?_; exact repairNeeded ⟨l0, ne⟩
      · exact shape.slides.2 l0
    have same : ({ d with «matches» := 0, slid := d.slid } : DeflateState) = d := by
      cases d; simp only at m0; subst m0; rfl
    let dF := paramsFinal d d.slid lv strategy c
    have dFEq : dF = paramsState d lv strategy c := by
      show paramsState { d with «matches» := 0, slid := d.slid } lv strategy c = _
      rw [same]
    have tailRun : paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, setD h ds dF) := by
      rw [dFEq]
      unfold paramsTail
      simp only [bind_app, ldRun, levelB, ite_true, zeroB, Bool.false_eq_true, ite_false, cfgL, wrD_eq,
        good.live.hs, setD_dstates_same, setD_setD]
      rfl
    have chains : Chains h dF := by
      have := inv.hashing.chains m0
      rw [dFEq]; exact this
    refine ⟨setD h ds dF, dF, tailRun,
      tail_final inv flushed good rfl rfl d.slid lv strategy lo hi slo shi chains,
      shape_setD good.live.hs _, owned_frame_setD h r ds d dF, rfl, rfl, rfl,
      views_setD good.live.hs (by rw [dFEq]; rfl) rfl rfl rfl rfl, ?_, ?_, ?_, ?_⟩
    · intro b; rw [dFEq]; exact Iff.rfl
    · rw [dFEq]; rfl
    · rw [dFEq]; rfl
    · rw [dFEq]; rfl

/-! ## 4. Frames: the inner `deflate` call, then the tail -/

/-- Frames compose; liveness carries over because a kept slot keeps its contents. -/
theorem frame_trans_live {h m k : Heap} {changed : Nat → Prop} (one : Frame h m changed)
    (two : Frame m k changed) : Frame h k changed := by
  obtain ⟨s1, a1, g1, n1, c1, slots1⟩ := one
  obtain ⟨s2, a2, g2, n2, c2, slots2⟩ := two
  refine ⟨s1.trans s2, a1.trans a2, g1.trans g2, Nat.le_trans n1 n2, Nat.le_trans c1 c2, fun b live out => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := slots1 b live out
  have liveM : m.live b := by unfold Heap.live at *; rw [e1, e2, e3, e4, e5, e6, e7]; exact live
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := slots2 b liveM out
  exact ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5, f6.trans e6, f7.trans e7, f8.trans e8⟩

/-- Restoring the same view on two heaps keeps a frame between them, when the view's block is
live and kept. -/
theorem frame_put {m k : Heap} {changed : Nat → Prop} (frame : Frame m k changed) (ref : BRef)
    (a : Array UInt8) (outside : ∀ i, (ref = .blk i ∨ ref = .dstate_depth i) → ¬ changed i ∧ m.live i) :
    Frame (Space.put m ref a) (Space.put k ref a) changed := by
  obtain ⟨st, al, ga, ne, co, slots⟩ := frame
  cases ref with
  | blk i =>
    obtain ⟨outI, liveI⟩ := outside i (Or.inl rfl)
    obtain ⟨_, w1, s1, g1, d1, i1, z1, r1⟩ := slots i liveI outI
    refine ⟨st, al, ga, ne, co, fun x live out => ?_⟩
    change Heap.live { m with bytes := upd m.bytes i (some a) } x at live
    change ({ k with bytes := upd k.bytes i (some a) } : Heap).bytes x = ({ m with bytes := upd m.bytes i (some a) } : Heap).bytes x ∧ _
    by_cases e : x = i
    · subst e
      exact ⟨by simp only [upd_same], w1, s1, g1, d1, i1, z1, r1⟩
    · have liveX : m.live x := by simpa [Heap.live, upd_ne _ _ _ _ e] using live
      obtain ⟨b2, w2, s2, g2, d2, i2, z2, r2⟩ := slots x liveX out
      simp only [upd_ne _ _ _ _ e]
      exact ⟨b2, w2, s2, g2, d2, i2, z2, r2⟩
  | dstate_depth i =>
    obtain ⟨outI, liveI⟩ := outside i (Or.inr rfl)
    obtain ⟨b1, w1, s1, g1, d1, i1, z1, r1⟩ := slots i liveI outI
    change Frame (match m.dstates i with
        | some s => { m with dstates := upd m.dstates i (some { s with depth := a }) } | none => m)
      (match k.dstates i with
        | some s => { k with dstates := upd k.dstates i (some { s with depth := a }) } | none => k) changed
    rw [d1]
    cases e : m.dstates i with
    | none => exact ⟨st, al, ga, ne, co, slots⟩
    | some s =>
      refine ⟨st, al, ga, ne, co, fun x live out => ?_⟩
      by_cases ex : x = i
      · subst ex
        exact ⟨b1, w1, s1, g1, by simp only [upd_same], i1, z1, r1⟩
      · have liveX : m.live x := by simpa [Heap.live, upd_ne _ _ _ _ ex] using live
        obtain ⟨b2, w2, s2, g2, d2, i2, z2, r2⟩ := slots x liveX out
        simp only [upd_ne _ _ _ _ ex]
        exact ⟨b2, w2, s2, g2, d2, i2, z2, r2⟩
  | str i => exact ⟨st, al, ga, ne, co, slots⟩
  | st_dist_code => exact ⟨st, al, ga, ne, co, slots⟩
  | st_length_code => exact ⟨st, al, ga, ne, co, slots⟩

/-- **A caller-region frame followed by a private run.** The second run changes only blocks of the
changed set and leaves the region's view as it was. -/
theorem buffer_frame_then_frame {h m k : Heap} {changed : Nat → Prop} {p : BPtr} {n : Nat}
    (one : BufferFrame h m changed [⟨p, n⟩]) (two : Frame m k changed)
    (views : ∀ ref off, p = .ref ref off → (Space.get k ref : Option (Array UInt8)) = Space.get m ref)
    (outside : ∀ ref off, p = .ref ref off → ∀ i, (ref = .blk i ∨ ref = .dstate_depth i) →
      ¬ changed i ∧ m.live i) :
    BufferFrame h k changed [⟨p, n⟩] := by
  obtain ⟨frame1, cells1⟩ := one
  refine ⟨?_, ?_⟩
  · simp only [restoreRegions, List.foldl_cons, List.foldl_nil] at frame1 ⊢
    rcases ep : p with _ | ⟨ref, off⟩
    · rw [ep] at frame1; exact frame_trans_live frame1 two
    · rw [ep] at frame1
      simp only at frame1 ⊢
      cases g : (Space.get h ref : Option (Array UInt8)) with
      | none => rw [g] at frame1; exact frame_trans_live frame1 two
      | some a =>
        rw [g] at frame1
        exact frame_trans_live frame1 (frame_put two ref a (outside ref off ep))
  · intro region mem ref off a ptr get
    obtain ⟨a', get', size, keep⟩ := cells1 region mem ref off a ptr get
    rw [List.mem_singleton] at mem
    subst mem
    exact ⟨a', by rw [views ref off ptr]; exact get', size, keep⟩

/-! ## 5. `deflateParams` -/

/-- **Hypothesis: the skeleton's `deflate_call`**, with the statement `operation_step_of` uses
(the clauses of `Goal.deflate` and the five owned blocks kept). -/
def DeflateCallFact : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → StreamBuffers h r → ActiveHeader h r → ∀ flush : Int32,
    ∃ rc after z' d' used out,
      C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) ∧
      DInv after r ds z' d' ∧ DispatchCallClauses h r ds z d flush rc after z' d' used out ∧
      (∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b)

/-- The flush branch of `deflateParams`: `deflate(Z_BLOCK)`, the test that the input is consumed
and the block empty, and the tail. -/
def paramsFlush (strm : ZStreamPtr) (s : DeflateStatePtr) (level strategy : Int32) : M Int32 := do
  let err ← deflate strm Z_BLOCK
  if err == Z_STREAM_ERROR then return err
  let d ← ldDeflateState s
  let diff ← lsub d.strstart.toUInt64.toInt64 d.block_start
  let tot ← ladd diff d.lookahead.toUInt64.toInt64
  if (← zrd strm (·.avail_in)) != 0 || tot != 0 then return Z_BUF_ERROR
  paramsTail s level strategy

/-- `deflateParams` when the strategy or the compression function changes. -/
theorem params_differs {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (level strategy : Int32)
    (rangeB : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = false)
    (lo : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt)
    (hi : (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9)
    (differs : strategy ≠ d.strategy ∨ (configuration_table[d.level.toInt.toNat]!).func ≠
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func) :
    deflateParams (some r) level strategy h =
      (if d.last_flush != -2 then
        paramsFlush (some r) (some (.tab ds)) (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy
      else paramsTail (some (.tab ds)) (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy) h := by
  have check := stateCheck_live good.live
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  have ldRun : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  have cfgD := config_at_run h good.inv.level_lo good.inv.level_hi
  have cfgL := config_at_run h lo hi
  rw [params_source]
  by_cases sb : strategy = d.strategy
  · have stratB : (strategy != d.strategy) = false := by simp [sb]
    have funcB : ((configuration_table[d.level.toInt.toNat]!).func !=
        (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func) = true := by
      rcases differs with ne | ne
      · exact absurd sb ne
      · simpa using ne
    simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
      rangeB, ldRun, cfgD, stratB, cfgL, funcB, pure_app, Bool.true_and]
    rfl
  · have stratB : (strategy != d.strategy) = true := by simpa using sb
    simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
      rangeB, ldRun, cfgD, stratB, ite_true, pure_app, Bool.true_and]
    rfl

/-- The part of the flush branch after `deflate(Z_BLOCK)` returned `err`. -/
def paramsAfter (strm : ZStreamPtr) (s : DeflateStatePtr) (level strategy : Int32) (err : Int32) : M Int32 := do
  if err == Z_STREAM_ERROR then return err
  let d ← ldDeflateState s
  let diff ← lsub d.strstart.toUInt64.toInt64 d.block_start
  let tot ← ladd diff d.lookahead.toUInt64.toInt64
  if (← zrd strm (·.avail_in)) != 0 || tot != 0 then return Z_BUF_ERROR
  paramsTail s level strategy

theorem params_flush_split (strm : ZStreamPtr) (s : DeflateStatePtr) (level strategy : Int32) :
    paramsFlush strm s level strategy = (do
      let err ← deflate strm Z_BLOCK
      paramsAfter strm s level strategy err) := rfl

set_option maxHeartbeats 8000000 in
/-- **After `deflate(Z_BLOCK)`**: either `deflateParams` returns with the heap of the call
(`Z_STREAM_ERROR`, or `Z_BUF_ERROR` when input is left or the block is not empty), or the block is
empty, the state is flushed, and the tail runs. -/
theorem params_after_outcome (repair : SlideRepair)
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} (inv : DInv h r ds z d)
    (rc lv strategy : Int32) (lo : 0 ≤ lv.toInt) (hi : lv.toInt ≤ 9) (slo : 0 ≤ strategy.toInt)
    (shi : strategy.toInt ≤ 4) :
    (∃ v, paramsAfter (some r) (some (.tab ds)) lv strategy rc h = .ok (v, h)) ∨
      TailOk h r ds z d (paramsAfter (some r) (some (.tab ds)) lv strategy rc) := by
  have good := inv.good
  have shape := inv.shape
  have ld1 : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  have avail1 : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by rw [zrd_eq, good.live.hz]
  by_cases err : rc = Z_STREAM_ERROR
  · left
    refine ⟨rc, ?_⟩
    simp only [paramsAfter, err, beq_self_eq_true, ite_true, pure_app]
    all_goals (try rfl)
  have errB : (rc == Z_STREAM_ERROR) = false := by simpa using err
  -- the flush test in `long` arithmetic
  have shape := inv.shape
  have ssLt : d.strstart.toNat < 2 ^ 32 := d.strstart.toNat_lt
  have ssInt : d.strstart.toUInt64.toInt64.toInt = d.strstart.toNat := u32_toInt64_toInt _
  have laInt : d.lookahead.toUInt64.toInt64.toInt = d.lookahead.toNat := u32_toInt64_toInt _
  have laLt : d.lookahead.toNat < 2 ^ 32 := d.lookahead.toNat_lt
  have spanLo : 0 ≤ (d.strstart.toNat : Int) - d.block_start.toInt := by
    have := shape.blockStart; omega
  have spanHi : (d.strstart.toNat : Int) - d.block_start.toInt ≤ 2 ^ 41 := by
    by_cases l0 : d.level = 0
    · have := (shape.levelZero l0).1; omega
    · have span := shape.blockSpan l0
      have sym := d.sym_next.toNat_lt
      have avail : d.match_available.toInt ≤ 1 := by
        rcases shape.matchAvailable with e | e <;> rw [e] <;> decide
      omega
  have subRun := lsub_value d.strstart.toUInt64.toInt64 d.block_start h (by rw [ssInt]; omega)
    (by rw [ssInt]; omega)
  have diffInt : (Int64.ofInt (d.strstart.toUInt64.toInt64.toInt - d.block_start.toInt)).toInt =
      (d.strstart.toNat : Int) - d.block_start.toInt := by
    rw [ssInt]; exact int64_ofInt_toInt _ (by omega) (by omega)
  have addRun := ladd_value (Int64.ofInt (d.strstart.toUInt64.toInt64.toInt - d.block_start.toInt))
    d.lookahead.toUInt64.toInt64 h (by rw [diffInt, laInt]; omega) (by rw [diffInt, laInt]; omega)
  have totInt : (Int64.ofInt ((Int64.ofInt (d.strstart.toUInt64.toInt64.toInt - d.block_start.toInt)).toInt +
      d.lookahead.toUInt64.toInt64.toInt)).toInt = (d.strstart.toNat : Int) - d.block_start.toInt + d.lookahead.toNat := by
    rw [diffInt, laInt]; exact int64_ofInt_toInt _ (by omega) (by omega)
  by_cases busy : z.avail_in ≠ 0 ∨ (d.strstart.toNat : Int) - d.block_start.toInt + d.lookahead.toNat ≠ 0
  · left
    refine ⟨Z_BUF_ERROR, ?_⟩
    have testB : ((z.avail_in != 0) || (Int64.ofInt ((Int64.ofInt (d.strstart.toUInt64.toInt64.toInt -
        d.block_start.toInt)).toInt + d.lookahead.toUInt64.toInt64.toInt) != 0)) = true := by
      rcases busy with a | t
      · rw [show (z.avail_in != 0) = true from bne_iff_ne.mpr a, Bool.true_or]
      · have : Int64.ofInt ((Int64.ofInt (d.strstart.toUInt64.toInt64.toInt - d.block_start.toInt)).toInt +
            d.lookahead.toUInt64.toInt64.toInt) ≠ 0 := by
          intro e; apply t; rw [← totInt, e]; rfl
        rw [show (Int64.ofInt ((Int64.ofInt (d.strstart.toUInt64.toInt64.toInt - d.block_start.toInt)).toInt +
            d.lookahead.toUInt64.toInt64.toInt) != 0) = true from bne_iff_ne.mpr this, Bool.or_true]
    simp only [paramsAfter, bind_app, errB, Bool.false_eq_true, ite_false, ld1, subRun, addRun, avail1, testB,
      ite_true, pure_app]
    all_goals (try rfl)
  · -- all input consumed and the block empty: the tail
    have availZero : z.avail_in = 0 := by
      refine Classical.byContradiction fun ne => ?_; exact busy (Or.inl ne)
    have totZero : (d.strstart.toNat : Int) - d.block_start.toInt + d.lookahead.toNat = 0 := by
      refine Classical.byContradiction fun ne => ?_; exact busy (Or.inr ne)
    have la0 : d.lookahead = 0 := by
      have : d.lookahead.toNat = 0 := by omega
      exact UInt32.toNat_inj.mp this
    have block : d.block_start.toInt = d.strstart.toNat := by omega
    have testB : ((z.avail_in != 0) || (Int64.ofInt ((Int64.ofInt (d.strstart.toUInt64.toInt64.toInt -
        d.block_start.toInt)).toInt + d.lookahead.toUInt64.toInt64.toInt) != 0)) = false := by
      have : Int64.ofInt ((Int64.ofInt (d.strstart.toUInt64.toInt64.toInt - d.block_start.toInt)).toInt +
          d.lookahead.toUInt64.toInt64.toInt) = 0 := by
        apply Int64.toInt_inj.mp; rw [totInt, totZero]; rfl
      rw [availZero, this]; rfl
    right
    obtain ⟨after, dF, tailRun, rest⟩ :=
      params_tail repair inv (Flushed.of_empty shape la0 block) lv strategy lo hi slo shi
    refine ⟨after, dF, ?_, rest⟩
    simp only [paramsAfter, bind_app, errB, Bool.false_eq_true, ite_false, ld1, subRun, addRun, avail1, testB]
    exact tailRun

/-- The changed set of `StepOk` from the stream's owned blocks. -/
theorem changed_of_owned {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {call : Call}
    (inv : DInv h r ds z d) (b : Nat) (c : StreamRoot r b ∨ DeflateOwned ds d b) :
    StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b :=
  c.elim Or.inl (fun o => Or.inr (Or.inl ((inv.owned b).2 o)))

/-- `StepOk` of `deflateParams` from a run that writes only the stream's own blocks and keeps
every byte view. -/
theorem step_params_private {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    {level strategy : Int32} (inv : DInv h r ds z d) (value : Int32)
    (run : deflateParams (some r) level strategy h = .ok (value, after)) (inv' : DInv after r ds z' d')
    (shape : Zlib.Deflate.Proofs.Shape h after)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b))
    (views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref)
    (owned : ∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b) :
    StepOk h r (.deflateParams (some r) level strategy) := by
  refine ⟨value, after, heapCall_run run, ⟨ds, z', d', inv'⟩, ?_, live_same inv inv' (shape.live) (fun b => (owned b).symm)⟩
  exact buffer_frame_same_views (full_frame_weaken frame (fun b c => changed_of_owned inv b c))
    (fun _ _ ref _ _ => views ref)

set_option maxHeartbeats 8000000 in
/-- **`deflateParams` keeps the invariant**, for every level and strategy, in every state of the
invariant and its call facts. Hypothesis: the skeleton's `deflate_call` (`deflateCall`); premise
awaiting the deflate owner's `DInv` change: the level-0 repair (`repair`). -/
theorem step_params (deflateCall : DeflateCallFact) (repair : SlideRepair)
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (calls : CallFacts d) (level strategy : Int32) (buffers : StreamBuffers h r) (header : ActiveHeader h r) :
    StepOk h r (.deflateParams (some r) level strategy) := by
  have good := inv.good
  by_cases refuse : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = true
  · exact step_params_refuse inv level strategy refuse
  have rangeB : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = false := by simpa using refuse
  have ranges : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ∧
      (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9 ∧ 0 ≤ strategy.toInt ∧ strategy.toInt ≤ 4 := by
    have r2 := rangeB
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, GT.gt] at r2
    obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := r2
    have z0 : (0 : Int32).toInt = 0 := rfl
    have n9 : (9 : Int32).toInt = 9 := rfl
    have f4 : Z_FIXED.toInt = 4 := rfl
    omega
  obtain ⟨lo, hi, slo, shi⟩ := ranges
  by_cases same : strategy = d.strategy ∧ (configuration_table[d.level.toInt.toNat]!).func =
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func
  · exact step_params_same inv level strategy lo hi slo shi same.1 same.2
  have differs : strategy ≠ d.strategy ∨ (configuration_table[d.level.toInt.toNat]!).func ≠
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func := by
    by_cases s : strategy = d.strategy
    · exact Or.inr (fun f => same ⟨s, f⟩)
    · exact Or.inl s
  have source := params_differs good level strategy rangeB lo hi differs
  by_cases reset : d.last_flush = -2
  · -- no flush before the first `deflate` call
    have resetB : (d.last_flush != -2) = false := by simp [reset]
    obtain ⟨after, dF, tailRun, invF, shapeF, frameF, -, -, -, viewsF, ownedF, -, -, -⟩ :=
      params_tail repair inv (Flushed.of_reset calls reset) _ strategy lo hi slo shi
    refine step_params_private inv Z_OK ?_ invF shapeF frameF viewsF ownedF
    rw [source, resetB]
    exact tailRun
  · -- `deflate(Z_BLOCK)` first
    have resetB : (d.last_flush != -2) = true := by simpa using reset
    obtain ⟨rc, after1, z1, d1, used, out, run1, inv1, clauses1, owned1⟩ := deflateCall inv buffers header Z_BLOCK
    obtain ⟨account, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, frame1, live1, -⟩ := clauses1
    have regions : StreamWriteRegions h r (.deflateParams (some r) level strategy) =
        [⟨z.next_out, z.avail_out.toNat⟩] := by
      simp [StreamWriteRegions, inv.good.live.hz, inv.good.live.zst]
    have liveOne : ∀ b, after1.live b ↔ h.live b := fun b => by simpa [LiveChange] using live1 b
    have run1' : deflate (some r) Z_BLOCK h = .ok (rc, after1) := run1
    -- the result after the call alone (`Z_STREAM_ERROR`, `Z_BUF_ERROR`)
    have stopHere : ∀ value, deflateParams (some r) level strategy h = .ok (value, after1) →
        StepOk h r (.deflateParams (some r) level strategy) := by
      intro value run
      refine ⟨value, after1, heapCall_run run, ⟨ds, z1, d1, inv1⟩, ?_, live_same inv inv1 liveOne owned1⟩
      rw [regions]
      exact bufferFrame_widen frame1 account.2.1 (fun b c => changed_of_owned inv b c)
    have flushRun : ∀ v after, paramsAfter (some r) (some (.tab ds)) (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy rc after1 = .ok (v, after) →
        deflateParams (some r) level strategy h = .ok (v, after) := by
      intro v after e
      rw [source, if_pos resetB, params_flush_split]
      simp only [bind_app, run1']
      exact e
    rcases params_after_outcome repair inv1 rc _ strategy lo hi slo shi with
      ⟨v, stop⟩ | ⟨after, dF, tailRun, invF, shapeF, frameF, -, -, -, viewsF, ownedF, -, -, -⟩
    · exact stopHere v (flushRun v after1 stop)
    · have run : deflateParams (some r) level strategy h = .ok (Z_OK, after) := flushRun _ _ tailRun
      refine ⟨Z_OK, after, heapCall_run run, ⟨ds, z1, dF, invF⟩, ?_, ?_⟩
      · rw [regions]
        have same : (fun b => StreamRoot r b ∨ DeflateOwned ds d1 b) = (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
          funext b; rw [owned1 b]
        rw [same] at frameF
        refine bufferFrame_widen (buffer_frame_then_frame frame1 frameF (fun ref _ _ => viewsF ref) ?_) account.2.1
          (fun b c => changed_of_owned inv b c)
        intro ref off ptr i root
        rcases output_target good buffers with null | ⟨ob, oo, arr, eo, get, outside⟩ | ⟨owner, oo, foreign, eo, get, outside⟩
        · rw [null] at ptr; cases ptr
        · rw [eo] at ptr
          injection ptr with ptr1 _
          subst ptr1
          have ei : ob = i := by rcases root with e | e <;> cases e; rfl
          subst ei
          refine ⟨outside, ?_⟩
          obtain ⟨a', get', -, -⟩ := frame1.2 _ (List.mem_singleton.mpr rfl) (.blk ob) oo arr eo get
          refine Or.inl ?_
          rw [show after1.bytes ob = some a' from get']
          exact Option.some_ne_none _
        · rw [eo] at ptr
          injection ptr with ptr1 _
          subst ptr1
          have ei : owner = i := by rcases root with e | e <;> cases e; rfl
          subst ei
          refine ⟨outside, ?_⟩
          obtain ⟨a', get', -, -⟩ := frame1.2 _ (List.mem_singleton.mpr rfl) (.dstate_depth owner) oo foreign.depth
            eo (show (h.dstates owner).map (·.depth) = some foreign.depth by rw [get]; rfl)
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          intro none
          change (after1.dstates owner).map (·.depth) = some a' at get'
          rw [none] at get'
          cases get'
      · exact live_same inv invF (fun b => (shapeF.live b).trans (liveOne b)) (fun b => (owned1 b).trans (ownedF b).symm)

end Zlib.Deflate.Universal

/-! ## 6. The header facts (for batch C) -/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- **Hypothesis: the header phase of `deflate`**, as `SequenceFacts.deflateHeader` states it. -/
def DeflateHeaderFact : Prop :=
  ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream} {d d' : DeflateState} {flush rc : Int32},
    DInv h r ds z d → HeaderInv d → StreamBuffers h r → ActiveHeader h r →
    C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) → DInv after r ds' z' d' → HeaderInv d'

set_option maxHeartbeats 4000000 in
/-- `deflateParams` with the same strategy and compression function ends in a state with the
status, symbols and header record of the start. -/
theorem params_same_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (level strategy : Int32)
    (rangeB : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = false)
    (lo : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt)
    (hi : (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9)
    (sameStrategy : strategy = d.strategy)
    (sameFunc : (configuration_table[d.level.toInt.toNat]!).func =
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func) :
    ∃ dK, deflateParams (some r) level strategy h = .ok (Z_OK, setD h ds dK) ∧
      dK.status = d.status ∧ dK.sym_next = d.sym_next ∧ dK.gzhead = d.gzhead := by
  have check := stateCheck_live good.live
  have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
  have ldRun : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  have cfgD := config_at_run h good.inv.level_lo good.inv.level_hi
  have cfgL := config_at_run h lo hi
  have stratB : (strategy != d.strategy) = false := by simp [sameStrategy]
  have funcB : ((configuration_table[d.level.toInt.toNat]!).func !=
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func) = false := by
    rw [sameFunc]; exact bne_self_eq_false _
  have toTail : deflateParams (some r) level strategy h =
      paramsTail (some (.tab ds)) (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy h := by
    rw [params_source]
    simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
      rangeB, ldRun, cfgD, stratB, cfgL, funcB, pure_app, Bool.false_and]
  rw [toTail]
  have dlo := good.inv.level_lo
  have dhi := good.inv.level_hi
  have cls := func_class (a := d.level.toInt.toNat)
    (b := (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat) (by omega) (by omega) sameFunc
  by_cases sameLevel : d.level = (if level == Z_DEFAULT_COMPRESSION then 6 else level)
  · have levelB : (d.level != (if level == Z_DEFAULT_COMPRESSION then 6 else level)) = false := by simp [sameLevel]
    refine ⟨{ d with strategy }, ?_, rfl, rfl, rfl⟩
    unfold paramsTail
    simp only [bind_app, ldRun, levelB, Bool.false_eq_true, ite_false, wrD_eq, good.live.hs]
    all_goals (try rfl)
  · have levelB : (d.level != (if level == Z_DEFAULT_COMPRESSION then 6 else level)) = true := by simpa using sameLevel
    have dNonzero : d.level ≠ 0 := by
      intro zero
      apply sameLevel
      rw [zero]
      have : (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat = 0 := cls.1.mp (by rw [zero]; rfl)
      apply Int32.toInt_inj.mp
      change (0 : Int) = _
      omega
    have zeroB : (d.level == 0 && d.«matches» != 0) = false := by simp [dNonzero]
    refine ⟨paramsState d (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy
      configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!, ?_, rfl, rfl, rfl⟩
    unfold paramsTail
    simp only [bind_app, ldRun, levelB, ite_true, zeroB, Bool.false_eq_true, ite_false, cfgL, wrD_eq,
      good.live.hs, setD_dstates_same, setD_setD]
    all_goals (try rfl)

set_option maxHeartbeats 8000000 in
/-- **The header facts of `deflateParams`** (for batch C): the final state of every accepted or
refused call keeps `HeaderInv`. The statement is `SequenceFacts.paramsHeader`, with the entry state's
`CallFacts d` added (P1, P1b before the first `deflate` call). Hypotheses: the
skeleton's `deflate_call` and the header phase of `deflate`; premise awaiting the deflate
owner's `DInv` change: `repair`. -/
theorem params_header (deflateCall : DeflateCallFact) (deflateHeader : DeflateHeaderFact)
    (repair : SlideRepair)
    {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream} {d d' : DeflateState}
    {level strategy rc : Int32} (inv : DInv h r ds z d) (calls : CallFacts d) (header : HeaderInv d) (buffers : StreamBuffers h r)
    (act : ActiveHeader h r) (run : C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after))
    (invAfter : DInv after r ds' z' d') : HeaderInv d' := by
  have good := inv.good
  have run' : deflateParams (some r) level strategy h = .ok (rc, after) := run
  have final : ∀ {afterK : Heap} {zK : ZStream} {dK : DeflateState} {v : Int32},
      deflateParams (some r) level strategy h = .ok (v, afterK) → r.get afterK = some zK →
      zK.state = some (.deflate ds) → afterK.dstates ds = some dK → HeaderInv dK → HeaderInv d' := by
    intro afterK zK dK v runK getK stK stateK headerK
    have e := run'.symm.trans runK
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have := state_after getK stK invAfter
    rw [stateK] at this
    cases this
    exact headerK
  have finalInv : ∀ {afterK : Heap} {zK : ZStream} {dK : DeflateState} {v : Int32},
      deflateParams (some r) level strategy h = .ok (v, afterK) → DInv afterK r ds zK dK → HeaderInv dK →
      HeaderInv d' := fun runK invK headerK =>
    final runK invK.good.live.hz invK.good.live.zst invK.good.live.hs headerK
  have getSet : ∀ x, r.get (setD h ds x) = some z := fun x => by simpa using good.live.hz
  by_cases refuse : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = true
  · have check := stateCheck_live good.live
    have stateRun : zrd (some r) (·.state) h = .ok (z.state, h) := by rw [zrd_eq, good.live.hz]
    have runR : deflateParams (some r) level strategy h = .ok (Z_STREAM_ERROR, h) := by
      rw [params_source]
      simp only [bind_app, check, bne_self_eq_false, Bool.false_eq_true, ite_false, stateRun, good.live.zst, castD,
        refuse, ite_true, pure_app]
      all_goals (try rfl)
    exact finalInv runR inv header
  have rangeB : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
      decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
      decide (strategy < 0) || decide (strategy > Z_FIXED)) = false := by simpa using refuse
  have ranges : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ∧
      (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9 ∧ 0 ≤ strategy.toInt ∧ strategy.toInt ≤ 4 := by
    have r2 := rangeB
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, GT.gt] at r2
    obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := r2
    have z0 : (0 : Int32).toInt = 0 := rfl
    have n9 : (9 : Int32).toInt = 9 := rfl
    have f4 : Z_FIXED.toInt = 4 := rfl
    omega
  obtain ⟨lo, hi, slo, shi⟩ := ranges
  by_cases same : strategy = d.strategy ∧ (configuration_table[d.level.toInt.toNat]!).func =
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func
  · obtain ⟨dK, runK, st, sym, gz⟩ := params_same_run good level strategy rangeB lo hi same.1 same.2
    exact final runK (getSet dK) good.live.zst (setD_dstates_same _ _ _) (header.keep st sym gz)
  have differs : strategy ≠ d.strategy ∨ (configuration_table[d.level.toInt.toNat]!).func ≠
      (configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func := by
    by_cases s : strategy = d.strategy
    · exact Or.inr (fun f => same ⟨s, f⟩)
    · exact Or.inl s
  have source := params_differs good level strategy rangeB lo hi differs
  by_cases reset : d.last_flush = -2
  · have resetB : (d.last_flush != -2) = false := by simp [reset]
    obtain ⟨afterK, dF, tailRun, invF, -, -, -, -, -, -, -, st, sym, gz⟩ :=
      params_tail repair inv (Flushed.of_reset calls reset) _ strategy lo hi slo shi
    have runK : deflateParams (some r) level strategy h = .ok (Z_OK, afterK) := by
      rw [source, resetB]; exact tailRun
    exact finalInv runK invF (header.keep st sym gz)
  · have resetB : (d.last_flush != -2) = true := by simpa using reset
    obtain ⟨rc1, after1, z1, d1, -, -, run1, inv1, -, -⟩ := deflateCall inv buffers act Z_BLOCK
    have header1 : HeaderInv d1 := deflateHeader inv header buffers act run1 inv1
    have run1' : deflate (some r) Z_BLOCK h = .ok (rc1, after1) := run1
    have flushRun : ∀ v afterK, paramsAfter (some r) (some (.tab ds)) (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy rc1 after1 = .ok (v, afterK) →
        deflateParams (some r) level strategy h = .ok (v, afterK) := by
      intro v afterK e
      rw [source, if_pos resetB, params_flush_split]
      simp only [bind_app, run1']
      exact e
    rcases params_after_outcome repair inv1 rc1 _ strategy lo hi slo shi with
      ⟨v, stop⟩ | ⟨afterK, dF, tailRun, invF, -, -, -, -, -, -, -, st, sym, gz⟩
    · exact finalInv (flushRun v after1 stop) inv1 header1
    · exact finalInv (flushRun _ _ tailRun) invF (header1.keep st sym gz)

/-- **The companion for batch C**: the call's final state, with the invariant and the header
facts beside it. -/
theorem params_body (deflateCall : DeflateCallFact) (deflateHeader : DeflateHeaderFact)
    (repair : SlideRepair)
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (calls : CallFacts d) (level strategy : Int32) (buffers : StreamBuffers h r) (act : ActiveHeader h r) :
    ∃ rc after ds' zF dF, C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after) ∧
      DInv after r ds' zF dF ∧ (HeaderInv d → HeaderInv dF) := by
  obtain ⟨value, after, run, ⟨ds', zF, dF, invF⟩, -, -⟩ := step_params deflateCall repair inv calls level strategy
    buffers act
  have run' : C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (value, after) := heapCall_ok run
  exact ⟨value, after, ds', zF, dF, run', invF,
    fun header => params_header deflateCall deflateHeader repair inv calls header buffers act run' invF⟩

end Zlib.Deflate.Universal
