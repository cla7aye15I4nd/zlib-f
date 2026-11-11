import ZlibF.Proof.«deflate.c.universal-window»
import ZlibF.Proof.«trees.c.universal-flush»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-private-arrays»

/-!
# deflate.c, universal engine: the five compression functions

Batch B of the deflate skeleton (`docs/progress.md`, Core proof skeletons): `deflate_huff`,
`deflate_rle`, `deflate_fast`, `deflate_slow` and `deflate_stored` under the invariant `DInv` and
the strategy entry `StrategyEntry`, for every parameter tuple.

**Loop invariant.** At the head of every iteration of a strategy loop the state satisfies `DInv`
again, with an empty pending buffer and room in the caller's output buffer. Inside an iteration
the symbol buffer may be full; `FLUSH_BLOCK` empties it (batch C, `flush_block_only_safe`).

**Termination.** Every iteration either leaves the loop or consumes one byte of
`avail_in + lookahead` (`fill_window` moves input to lookahead without changing the sum).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-! ## A `while` rule with a measure -/

theorem cwhile_go_measure {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Heap → Prop) (Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, I s h → ∃ c s1 h1, cond s h = .ok ((c, s1), h1) ∧
      (c = true → ∃ s2 h2, body s1 h1 = .ok (s2, h2) ∧ I s2 h2 ∧ μ s2 h2 < μ s h) ∧
      (c = false → Q s1 h1)) :
    ∀ n s h, I s h → μ s h < n → ∃ s' h', cwhile.go cond body n s h = .ok (s', h') ∧ Q s' h' := by
  intro n
  induction n with
  | zero => intro s h _ bound; omega
  | succ n ih =>
    intro s h inv bound
    obtain ⟨c, s1, h1, run, more, stop⟩ := step s h inv
    cases c with
    | false =>
      exact ⟨s1, h1, by simp [cwhile.go, run], stop rfl⟩
    | true =>
      obtain ⟨s2, h2, body2, inv2, less⟩ := more rfl
      obtain ⟨s', h', go, q⟩ := ih s2 h2 inv2 (by omega)
      exact ⟨s', h', by simp [cwhile.go, run, body2, go], q⟩

/-- `while` rule for a loop whose iterations decrease a measure below the fuel. -/
theorem cwhile_measure {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Heap → Prop) (Q : σ → Heap → Prop) (μ : σ → Heap → Nat)
    (step : ∀ s h, I s h → ∃ c s1 h1, cond s h = .ok ((c, s1), h1) ∧
      (c = true → ∃ s2 h2, body s1 h1 = .ok (s2, h2) ∧ I s2 h2 ∧ μ s2 h2 < μ s h) ∧
      (c = false → Q s1 h1))
    {s : σ} {h : Heap} (inv : I s h) (bound : μ s h < fuel) :
    ∃ s' h', cwhile cond body s h = .ok (s', h') ∧ Q s' h' :=
  cwhile_go_measure I Q μ step fuel s h inv bound

/-! ## Scalar updates of the engine fields -/

/-- `d'` changes only the engine scalars of `d`: positions, match state and insertion state. -/
def EngineUpdate (d d' : DeflateState) : Prop :=
  d' = { d with
    strstart := d'.strstart
    lookahead := d'.lookahead
    match_length := d'.match_length
    match_start := d'.match_start
    match_available := d'.match_available
    prev_length := d'.prev_length
    prev_match := d'.prev_match
    insert := d'.insert
    ins_h := d'.ins_h }

/-- An update of the engine scalars keeps `DGood`. -/
theorem engine_update_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    (good : DGood h r ds z d) (update : EngineUpdate d d') : DGood (setD h ds d') r ds z d' := by
  rw [update]
  have inv : DStInv h ds { d with
      strstart := d'.strstart, lookahead := d'.lookahead, match_length := d'.match_length,
      match_start := d'.match_start, match_available := d'.match_available,
      prev_length := d'.prev_length, prev_match := d'.prev_match, insert := d'.insert,
      ins_h := d'.ins_h } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact good.setD' rfl good.live.status inv (by trkeep)

/-- An update of the engine scalars keeps `DInv` once the new shape and hash state are shown. -/
theorem engine_update_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    (inv : DInv h r ds z d) (update : EngineUpdate d d') (shape : Shape d')
    (hashing : Hashing (setD h ds d') d') : DInv (setD h ds d') r ds z d' := by
  refine ⟨engine_update_good inv.good update, inv.alloc, inv.globals, shape, hashing, ?_⟩
  obtain ⟨⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
  rw [update]
  exact ⟨⟨xs, ⟨b, a, pbuf, by simpa using get, ledger.keep rfl rfl rfl rfl⟩, dist⟩,
    ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩


/-! ## One literal

`deflate_huff` and the literal branch of `deflate_rle`:
`s->match_length = 0` (huff) is a separate statement; this is `_tr_tally_lit` of
`window[strstart]` followed by `s->lookahead--, s->strstart++`. -/

/-- The state after recording the literal `c` at `strstart` and advancing by one. -/
def literalStep (d : DeflateState) (c : UInt8) : DeflateState :=
  { literalState d c with lookahead := d.lookahead - 1, strstart := d.strstart + 1 }

theorem window_block {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) :
    ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧ wa.size = d.window_size.toNat := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, get, _⟩ := blocks.wa
  exact ⟨w, wa, blocks.win, get, (window_extent good blocks.win get).1⟩

/-- The recorded symbols of `DInv` live in the block that `TreesInvAt` names. -/
theorem recorded_trees {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) :
    ∃ b buf xs, TreesInvAt h ds d b buf ∧ SymbolLedger buf d xs ∧
      ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262 := by
  obtain ⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩ := inv.symbols.recorded
  obtain ⟨d0, b0, buf0, trees⟩ := inv.good.trees
  have de : d0 = d := Option.some.inj (trees.base.dstate.symm.trans inv.good.live.hs)
  subst d0
  have be : b0 = b := by
    simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using trees.base.pbuf.symm
  subst b0
  have ae : buf0 = a := Option.some.inj (trees.base.bytes.symm.trans get)
  subst buf0
  exact ⟨b, a, xs, trees, ledger, dist⟩


/-- The trees invariant of `DGood`, at the named pending block and its bytes. -/
theorem trees_at_of_good {h : Heap} {r : ZStreamRef} {ds b : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (pbuf : d.pending_buf = .ref (.blk b) 0)
    (get : h.bytes b = some buf) : TreesInvAt h ds d b buf := by
  obtain ⟨d0, b0, buf0, trees⟩ := good.trees
  have de : d0 = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst d0
  have be : b0 = b := by
    simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using trees.base.pbuf.symm
  subst b0
  have ae : buf0 = buf := Option.some.inj (trees.base.bytes.symm.trans get)
  subst buf0
  exact trees

set_option maxHeartbeats 1600000 in
/-- **One literal.** From `DInv` with lookahead, `_tr_tally_lit(s, window[strstart])` and the
advance run; the returned flag says whether the symbol buffer is now full. The result keeps
`DGood`, the trees invariant and the symbol ledger with the new literal; every field other than
the symbol count, the literal frequencies and the two positions is unchanged. -/
theorem literal_step_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level : d.level ≠ 0) (look : 1 ≤ d.lookahead.toNat) {α : Type}
    (k : Bool → M α) :
    ∃ b buf buf' xs c h3,
      (do
        let d ← ldDeflateState (some (.tab ds))
        let c ← index8 d.window d.strstart.toNat
        let bflush ← tally_lit (some (.tab ds)) c
        wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
        k bflush) h = k (d.sym_next + 3 == d.sym_end) h3 ∧
      h3 = setD (Zlib.Trees.Proofs.Out.setB h b buf') ds (literalStep d c) ∧
      TreesInvAt h ds d b buf ∧ SymbolLedger buf d xs ∧ (∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262) ∧
      buf' = literalBytes buf d c ∧
      DGood h3 r ds z (literalStep d c) ∧
      TreesInvAt h3 ds (literalStep d c) b buf' ∧
      SymbolLedger buf' (literalStep d c) (xs ++ [⟨0, c.toNat⟩]) ∧
      HeapChains h3 (literalStep d c) (d.strstart.toNat + 1 - d.insert.toNat) ∧
      (literalStep d c).sym_next.toNat = d.sym_next.toNat + 3 ∧
      (literalStep d c).strstart.toNat = d.strstart.toNat + 1 ∧
      (literalStep d c).lookahead.toNat = d.lookahead.toNat - 1 ∧
      ((d.sym_next + 3 == d.sym_end) = false →
        (literalStep d c).sym_next.toNat < (literalStep d c).sym_end.toNat) := by
  obtain ⟨b, buf, xs, trees, ledger, dist⟩ := recorded_trees inv
  obtain ⟨w, wa, win, get, size⟩ := window_block inv.good
  have room := inv.shape.room
  have strict := inv.shape.symRoom
  have roomT := literal_room inv.good.inv strict
  have readC : index8 d.window d.strstart.toNat h = .ok (bfn wa d.strstart.toNat, h) := by
    rw [win]; exact index8_bfn get (by simp) (by omega)
  obtain ⟨c, cdef⟩ : ∃ x, x = bfn wa d.strstart.toNat := ⟨_, rfl⟩
  rw [← cdef] at readC
  have tallyRun := tally_literal_run trees.base c roomT
  obtain ⟨h2, h2def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c) :=
    ⟨_, rfl⟩
  rw [← h2def] at tallyRun
  have chains2 : HeapChains h2 (literalState d c) (d.strstart.toNat - d.insert.toNat) := by
    rw [h2def]; exact pending_write_chains inv.good (inv.chains level) trees.base.pbuf _ c
  have good2 : DGood h2 r ds z (literalState d c) := by rw [h2def]; exact literal_good_after inv.good trees c roomT
  have ledger2 := ledger_literal trees.base ledger roomT c
  have count := literal_count trees.base roomT c
  have wsz := inv.good.inv.wsz
  have wsHi := (slide_window_sizes inv.good).2
  have ssEq : (d.strstart + 1).toNat = d.strstart.toNat + 1 := by
    rw [UInt32.toNat_add]; simp; omega
  have laEq : (d.lookahead - 1).toNat = d.lookahead.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))
  let d3 := literalStep d c
  obtain ⟨h3, h3def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds d3 := ⟨_, rfl⟩
  have h3eq : h3 = setD h2 ds d3 := by rw [h3def, h2def, setD_setD]
  have update : EngineUpdate (literalState d c) d3 := rfl
  have good3 : DGood h3 r ds z d3 := by rw [h3eq]; exact engine_update_good good2 update
  have state2 : h2.dstates ds = some (literalState d c) := by rw [h2def]; simp
  have write : wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 }) h2 =
      .ok ((), h3) := by
    rw [wrD_eq, state2, h3eq]
    rfl
  refine ⟨b, buf, literalBytes buf d c, xs, c, h3, ?_, h3def, trees, ledger, dist, rfl, good3, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp only [bind_app, ldDeflateState_tab inv.good.live.hs, readC, tallyRun, write]
  · exact trees_at_of_good good3 trees.base.pbuf (by rw [h3def]; simp)
  · exact ledger2.keep rfl rfl rfl rfl
  · have at2 : HeapChainsAt h2 (literalState d c) (d.strstart.toNat - d.insert.toNat)
        (d.strstart.toNat + d.lookahead.toNat) := chains2
    have at3 : HeapChainsAt h3 d3 (d.strstart.toNat - d.insert.toNat)
        (d.strstart.toNat + d.lookahead.toNat) :=
      at2.keep (by rw [h3eq]; rfl) (by rw [h3eq]; rfl) rfl rfl rfl rfl rfl rfl rfl
    have collapsed := at3.collapse (by change _ = (d.strstart + 1).toNat + (d.lookahead - 1).toNat; omega)
    exact heap_chains_raise collapsed (by omega)
  · exact count
  · exact ssEq
  · exact laEq
  · intro flag
    exact literal_not_full trees c roomT flag


/-- `s->match_length = 0` keeps the invariant. -/
theorem clear_match_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) :
    wr (some (.tab ds)) (fun d => { d with match_length := 0 }) h =
        .ok ((), setD h ds { d with match_length := 0 }) ∧
      DInv (setD h ds { d with match_length := 0 }) r ds z { d with match_length := 0 } := by
  refine ⟨by rw [wrD_eq, inv.good.live.hs], ?_⟩
  have shape := inv.shape
  refine engine_update_inv (d' := { d with match_length := 0 }) inv rfl ?_ ?_
  · exact ⟨shape.room, shape.insert, shape.insertDone, shape.prevLength,
      (by show (0 : UInt32).toNat ≤ 258; decide), shape.matchAvailable,
      shape.blockStart, shape.blockSpan, shape.levelZero, shape.available,
      fun large => absurd large (by show ¬ 3 ≤ (0 : UInt32).toNat; decide),
      fun a b c e => ⟨by show (0 : UInt32).toNat ≤ 2; decide, (shape.fastLazy a b c e).2⟩, shape.highWater, shape.lastFlush, shape.trailer,
      shape.biValid, shape.cursor, shape.symRoom, shape.slides⟩
  · obtain ⟨chains, slid, rolling⟩ := inv.hashing
    refine ⟨fun zero => ?_, fun one => ?_, fun a b large => ?_⟩
    · obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains zero
      exact ⟨w, p, q, wa, pa, qa, win, prev, head, by simpa using hw, by simpa using hp, by simpa using hq, H⟩
    · obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := slid one
      exact ⟨w, p, q, wa, pa, qa, win, prev, head, by simpa using hw, by simpa using hp, by simpa using hq, H⟩
    · obtain ⟨w, wa, win, hw, form⟩ := rolling a b large
      exact ⟨w, wa, win, by simpa using hw, form⟩

/-! ## A block flush inside a strategy

`FlushSafe` is the statement of batch C's `Block.flush_block_only_safe` for every memLevel,
with the lower bound on `block_start` that holds inside the strategies (`DInv.blockSpan`: a block
may span many slides) and the reset of `matches` by `init_block`. The strategy lemmas take it as a
hypothesis; the batch B theorems instantiate it with batch C's proof. It is not an assumed
contract: it is a statement about the translated `FLUSH_BLOCK_ONLY`. -/

def FlushSafe : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds pb ob w : Nat} {z : ZStream} {d : DeflateState}
    {buf window : Array UInt8} {xs : List Symbol},
    DGood h r ds z d → TreesInvAt h ds d pb buf → StreamBuffers h r → 0 < d.level.toInt →
    ((∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo)) →
    d.pending_out = d.pending_buf → d.pending = 0 → d.bi_valid.toInt ≤ 7 →
    SymbolLedger buf d xs → BlockInit.BlockClear d →
    d.window = .ref (.blk w) 0 → h.bytes w = some window →
    -(2 : Int) ^ 62 ≤ d.block_start.toInt → d.block_start.toInt ≤ d.strstart.toNat →
    d.strstart.toNat ≤ d.window_size.toNat → ∀ last : Bool,
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      BlockInit.BlockClear result ∧ (∃ b, SymbolLedger b result []) ∧ result.bi_valid.toInt < 8 ∧
      (last = true → result.bi_valid.toInt = 0) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      Block.FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      (result.pending = 0 ∨ z'.avail_out = 0) ∧ result.«matches» = 0

/-- The state a block flush leaves, as far as the shape is concerned. -/
def flushedState (d : DeflateState) : DeflateState :=
  { d with sym_next := 0, block_start := d.strstart.toUInt64.toInt64 }

/-- What a strategy has at a `FLUSH_BLOCK`: the invariant, except that the symbol buffer may be
full and the block not yet started at `strstart`; the shape is that of the flushed state. -/
structure BlockReady (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (pb : Nat) (buf : Array UInt8) (xs : List Symbol) : Prop where
  good : DGood h r ds z d
  alloc : DefAlloc z
  globals : LibraryGlobals h
  trees : TreesInvAt h ds d pb buf
  ledger : SymbolLedger buf d xs
  clear : BlockInit.BlockClear d
  shape : Shape (flushedState d)
  hashing : Hashing h d
  pending : d.pending = 0
  blockLow : -(2 : Int) ^ 62 ≤ d.block_start.toInt
  blockHigh : d.block_start.toInt ≤ d.strstart.toNat
  level : d.level ≠ 0
  buffers : StreamBuffers h r
  out : z.next_out ≠ .null

theorem output_reference {h : Heap} {r : ZStreamRef} {z : ZStream} (get : r.get h = some z)
    (buffers : StreamBuffers h r) (out : z.next_out ≠ .null) :
    ∃ ob, (∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo) := by
  obtain ⟨z0, get0, _, output, _⟩ := buffers
  have same : z0 = z := Option.some.inj (get0.symm.trans get)
  subst z0
  rcases output with null | ⟨_, writable, _⟩
  · exact absurd null out
  · cases pointer : z.next_out with
    | null => exact absurd pointer out
    | ref ref oo =>
      rw [pointer] at writable
      rcases writable_reference_cases (writable rfl) with ⟨b, e⟩ | ⟨o, e⟩
      · subst e; exact ⟨b, Or.inl ⟨oo, rfl⟩⟩
      · subst e; exact ⟨o, Or.inr ⟨oo, rfl⟩⟩

theorem ledger_empty_any {buf buf' : Array UInt8} {d : DeflateState}
    (ledger : SymbolLedger buf d []) : SymbolLedger buf' d [] :=
  ⟨ledger.count, ledger.valid, fun i s sel => by simp at sel, ledger.literal, ledger.distance⟩

set_option maxHeartbeats 4000000 in
/-- **A block flush inside a strategy restores the invariant.** From `BlockReady`, the macro
`FLUSH_BLOCK_ONLY` runs (by `FlushSafe`); afterwards `DInv` holds, the caller's buffers are valid,
the window side of the state is unchanged, and either the pending buffer is empty or the caller's
output buffer is full. -/
theorem flush_block_inv (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (ready : BlockReady h r ds z d pb buf xs) (last : Bool) :
    ∃ produced after z' result,
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DInv after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (result.pending = 0 ∨ z'.avail_out = 0) ∧ (last = true → result.bi_valid.toInt = 0) ∧
      result.strstart = d.strstart ∧ result.lookahead = d.lookahead ∧ result.insert = d.insert ∧
      result.ins_h = d.ins_h ∧ result.match_length = d.match_length ∧
      result.match_start = d.match_start ∧ result.match_available = d.match_available ∧
      result.prev_length = d.prev_length ∧ result.prev_match = d.prev_match ∧
      result.level = d.level ∧ result.strategy = d.strategy ∧ result.strm = d.strm ∧
      result.status = d.status ∧ result.wrap = d.wrap ∧ result.window_size = d.window_size ∧
      result.w_size = d.w_size ∧ result.sym_next = 0 := by
  have good := ready.good
  obtain ⟨ob, pointer⟩ := output_reference good.live.hz ready.buffers ready.out
  obtain ⟨w, wa, win, get, size⟩ := window_block good
  have levelPos : 0 < d.level.toInt := by
    have lo := good.inv.level_lo
    have ne : d.level.toInt ≠ 0 := by
      intro zero; exact ready.level (Int32.toInt_inj.mp (by rw [zero]; rfl))
    omega
  have shape := ready.shape
  have range : d.strstart.toNat ≤ d.window_size.toNat := by
    have := shape.room
    change d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat at this
    omega
  obtain ⟨produced, after, z', result, run, goodA, buffersA, account, sizes, storage, clearA, ⟨bA, ledgerA⟩,
      bitsA, lastA, cursorA, frame, drained, matchesA⟩ :=
    safe good ready.trees ready.buffers levelPos pointer (shape.cursor ready.pending) ready.pending
      shape.biValid ready.ledger ready.clear win get ready.blockLow ready.blockHigh range last
  have e := frame
  unfold Block.FlushFrame at e
  have fs : result.strstart = d.strstart := (congrArg DeflateState.strstart e).trans rfl
  have fl : result.lookahead = d.lookahead := (congrArg DeflateState.lookahead e).trans rfl
  have fi : result.insert = d.insert := (congrArg DeflateState.insert e).trans rfl
  have fh : result.ins_h = d.ins_h := (congrArg DeflateState.ins_h e).trans rfl
  have fml : result.match_length = d.match_length := (congrArg DeflateState.match_length e).trans rfl
  have fms : result.match_start = d.match_start := (congrArg DeflateState.match_start e).trans rfl
  have fma : result.match_available = d.match_available := (congrArg DeflateState.match_available e).trans rfl
  have fpl : result.prev_length = d.prev_length := (congrArg DeflateState.prev_length e).trans rfl
  have fpm : result.prev_match = d.prev_match := (congrArg DeflateState.prev_match e).trans rfl
  have flv : result.level = d.level := (congrArg DeflateState.level e).trans rfl
  have fst : result.strategy = d.strategy := (congrArg DeflateState.strategy e).trans rfl
  have fsm : result.strm = d.strm := (congrArg DeflateState.strm e).trans rfl
  have fstat : result.status = d.status := (congrArg DeflateState.status e).trans rfl
  have fwr : result.wrap = d.wrap := (congrArg DeflateState.wrap e).trans rfl
  have fws : result.window_size = d.window_size := (congrArg DeflateState.window_size e).trans rfl
  have fw : result.w_size = d.w_size := (congrArg DeflateState.w_size e).trans rfl
  have fbs : result.block_start = d.strstart.toUInt64.toInt64 := (congrArg DeflateState.block_start e).trans rfl
  have fse : result.sym_end = d.sym_end := (congrArg DeflateState.sym_end e).trans rfl
  have flit : result.lit_bufsize = d.lit_bufsize := (congrArg DeflateState.lit_bufsize e).trans rfl
  have fhw : result.high_water = d.high_water := (congrArg DeflateState.high_water e).trans rfl
  have flf : result.last_flush = d.last_flush := (congrArg DeflateState.last_flush e).trans rfl
  have fwin : result.window = d.window := (congrArg DeflateState.window e).trans rfl
  have fpb : result.pending_buf = d.pending_buf := (congrArg DeflateState.pending_buf e).trans rfl
  have fhs : result.hash_shift = d.hash_shift := (congrArg DeflateState.hash_shift e).trans rfl
  have fhm : result.hash_mask = d.hash_mask := (congrArg DeflateState.hash_mask e).trans rfl
  have symZero : result.sym_next = 0 := by
    have := ledgerA.count
    simp at this
    exact UInt32.toNat_inj.mp (by rw [this]; rfl)
  have shapeA : Shape result := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, cursorA, ?_, ?_⟩
    · rw [fs, fl, fws]; exact shape.room
    · rw [fi, fs]; exact shape.insert
    · rw [fl, fi]; exact shape.insertDone
    · rw [fpl]; exact shape.prevLength
    · rw [fml]; exact shape.matchLength
    · rw [fma]; exact shape.matchAvailable
    · rw [fbs, fs]; exact shape.blockStart
    · rw [flv, fs, fbs, symZero, fma]; exact shape.blockSpan
    · rw [flv, fbs, fl, symZero]; exact shape.levelZero
    · rw [fma, fs]; exact shape.available
    · rw [fml, fs, fms, fl, fw]; exact shape.pendingMatch
    · rw [flv, fst, fml, fpl]; exact shape.fastLazy
    · rw [fhw, fws]; exact shape.highWater
    · rw [flf]; exact shape.lastFlush
    · rw [fwr, fstat]; exact shape.trailer
    · rw [symZero, fse]; have := shape.symRoom; exact this
    · rw [matchesA, flv]; exact ⟨Nat.zero_le _, fun _ => rfl⟩
  have frameW := frame.work
  have pbuf := ready.trees.base.pbuf
  have zeroMatches : d.«matches» = 0 := by
    have := shape.slides.2 ready.level; exact this
  have chainsA : HeapChains after result (result.strstart.toNat - result.insert.toNat) := by
    rw [fs, fi]
    have chains : HeapChains h d (d.strstart.toNat - d.insert.toNat) := ready.hashing.chains zeroMatches
    rcases pointer with ⟨oo, p⟩ | ⟨oo, p⟩
    · exact flush_frames_chains storage good ready.buffers p pbuf frameW chains
    · exact foreign_flush_frames_chains storage good ready.buffers p pbuf frameW chains
  have windowA : after.bytes w = some wa := by
    obtain ⟨wp, pp, qp, b0, blocks⟩ := good.inv.blocks
    obtain ⟨pa, getP, _⟩ := blocks.pa
    obtain ⟨qa, getQ, _⟩ := blocks.qa
    have we : wp = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    subst wp
    rcases pointer with ⟨oo, p⟩ | ⟨oo, p⟩
    · exact (storage.private_arrays good ready.buffers p win get blocks.prev getP blocks.head getQ pbuf).1
    · exact (storage.foreign_private_arrays good ready.buffers p win get blocks.prev getP blocks.head getQ pbuf).1
  have staticA : after.static = h.static := storage.frame.1.symm
  obtain ⟨pbA, pbAget⟩ : ∃ a, after.bytes pb = some a := by
    have g : Space.get h (BRef.blk pb) = some buf := by simpa using ready.trees.base.bytes
    obtain ⟨next, getN, _⟩ := sizes.get (.blk pb) buf g
    exact ⟨next, by simpa using getN⟩
  refine ⟨produced, after, z', result, run, ⟨goodA, ?_, ?_, shapeA, ?_, ?_⟩, buffersA, account, drained,
    lastA, fs, fl, fi, fh, fml, fms, fma, fpl, fpm, flv, fst, fsm, fstat, fwr, fws, fw, symZero⟩
  · exact ⟨account.2.2.2.2.2.2.2.1.trans ready.alloc.1, account.2.2.2.2.2.2.2.2.1.trans ready.alloc.2⟩
  · unfold LibraryGlobals; rw [staticA]; exact ready.globals
  · refine ⟨fun _ => chainsA, (fun one => by rw [matchesA] at one; cases one), fun a b large => ?_⟩
    rw [fst] at a b
    rw [fl] at large
    obtain ⟨w0, wa0, win0, get0, form⟩ := ready.hashing.rolling a b large
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans get)
    subst wa0
    exact ⟨w, wa, by rw [fwin]; exact win, windowA, by rw [fhs, fhm, fs, fh]; exact form⟩
  · refine ⟨⟨[], ⟨pb, pbA, by rw [fpb]; exact pbuf, pbAget, ledger_empty_any ledgerA⟩, by simp⟩, clearA, ?_⟩
    intro b0 off _ nonzero
    exact absurd symZero nonzero


theorem u32_toInt64_toInt (x : UInt32) : x.toUInt64.toInt64.toInt = (x.toNat : Int) := by
  rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp
    have := x.toNat_lt
    omega

/-- The shape of the flushed state from the fields a flush does not reset. -/
theorem flushed_shape {d : DeflateState}
    (room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (insert : d.insert.toNat ≤ d.strstart.toNat)
    (insertDone : 3 ≤ d.lookahead.toNat → d.insert = 0)
    (prevLength : d.prev_length.toNat ≤ 258) (matchLength : d.match_length.toNat ≤ 258)
    (matchAvailable : d.match_available = 0 ∨ d.match_available = 1)
    (levelZero : d.level = 0 → d.lookahead = 0)
    (available : d.match_available ≠ 0 → 1 ≤ d.strstart.toNat)
    (pendingMatch : 3 ≤ d.match_length.toNat →
      1 ≤ (d.strstart - 1 - d.match_start).toNat ∧
      (d.strstart - 1 - d.match_start).toNat ≤ d.w_size.toNat - 262 ∧
      d.match_length.toNat ≤ d.lookahead.toNat + 1)
    (fastLazy : 1 ≤ d.level.toInt → d.level.toInt ≤ 3 → d.strategy.toInt ≠ 2 → d.strategy.toInt ≠ 3 →
      d.match_length.toNat ≤ 2 ∧ d.prev_length.toNat ≤ 2)
    (highWater : d.high_water.toNat ≤ d.window_size.toNat)
    (lastFlush : -2 ≤ d.last_flush.toInt ∧ d.last_flush.toInt ≤ 5)
    (trailer : d.wrap.toInt < 0 → d.status = FINISH_STATE)
    (biValid : d.bi_valid.toInt ≤ 7) (cursor : d.pending = 0 → d.pending_out = d.pending_buf)
    (symPos : 0 < d.sym_end.toNat)
    (slides : d.«matches».toNat ≤ 2 ∧ (d.level ≠ 0 → d.«matches» = 0)) : Shape (flushedState d) := by
  have cast := u32_toInt64_toInt d.strstart
  have avail : 0 ≤ d.match_available.toInt := by
    rcases matchAvailable with e | e <;> rw [e] <;> decide
  refine ⟨room, insert, insertDone, prevLength, matchLength, matchAvailable, ?_, ?_, ?_, available,
    pendingMatch, fastLazy, highWater, lastFlush, trailer, biValid, cursor, symPos, slides⟩
  · change d.strstart.toUInt64.toInt64.toInt ≤ _
    rw [cast]; exact Int.le_refl _
  · intro _
    change (d.strstart.toNat : Int) - d.strstart.toUInt64.toInt64.toInt ≤
      258 * ((0 : UInt32).toNat / 3 : Nat) + d.match_available.toInt
    rw [cast]
    have zero : (0 : UInt32).toNat / 3 = 0 := rfl
    rw [zero]
    omega
  · intro zero
    exact ⟨by change 0 ≤ d.strstart.toUInt64.toInt64.toInt; rw [cast]; omega, levelZero zero, rfl⟩

theorem DInv.flushedShape {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : Shape (flushedState d) :=
  have s := inv.shape
  flushed_shape s.room s.insert s.insertDone s.prevLength s.matchLength s.matchAvailable
    (fun zero => (s.levelZero zero).2.1) s.available s.pendingMatch s.fastLazy s.highWater s.lastFlush
    s.trailer s.biValid s.cursor (by have := s.symRoom; omega) s.slides

/-- A block flush can start from any invariant state with an empty pending buffer. -/
theorem DInv.ready {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (pending : d.pending = 0) (level : d.level ≠ 0)
    (buffers : StreamBuffers h r) (out : z.next_out ≠ .null) :
    ∃ pb buf xs, BlockReady h r ds z d pb buf xs := by
  obtain ⟨b, buf, xs, trees, ledger, _⟩ := recorded_trees inv
  exact ⟨b, buf, xs, ⟨inv.good, inv.alloc, inv.globals, trees, ledger, inv.symbols.clear, inv.flushedShape,
    inv.hashing, pending, block_start_low inv level, inv.shape.blockStart, level, buffers, out⟩⟩

/-- Writing the pending block and the state record keeps the caller's buffers. -/
theorem private_write_buffers {h : Heap} {r : ZStreamRef} {ds b : Nat} {z : ZStream} {d d' : DeflateState}
    {buf' : Array UInt8} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pbuf : d.pending_buf = .ref (.blk b) 0)
    (keys : d'.window = d.window ∧ d'.prev = d.prev ∧ d'.head = d.head ∧ d'.pending_buf = d.pending_buf)
    (good' : DGood (setD (Zlib.Trees.Proofs.Out.setB h b buf') ds d') r ds z d') :
    StreamBuffers (setD (Zlib.Trees.Proofs.Out.setB h b buf') ds d') r := by
  have frame : ByteFrame h (setD (Zlib.Trees.Proofs.Out.setB h b buf') ds d') (fun i => i = ds ∨ i = b) := by
    refine ⟨rfl, fun i outside => ?_, fun i outside => ?_, fun _ _ => rfl⟩
    · have ne : i ≠ b := fun e => outside (Or.inr e)
      simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ ne]
    · have ne : i ≠ ds := fun e => outside (Or.inl e)
      simp [setD_dstates_ne _ _ _ _ ne]
  have owned := stream_owned_keys good good' keys.1 keys.2.1 keys.2.2.1 keys.2.2.2
  exact stream_buffers_private_read good.live.hz good'.live.hz buffers frame
    (fun i mine => (stream_owned_deflate good i).mpr (by
      rcases mine with e | e
      · exact Or.inl e
      · subst e; exact Or.inr (Or.inr (Or.inr (Or.inr pbuf)))))
    owned (stream_accounting_self z) rfl

/-- The invariant after one literal of `deflate_huff` or `deflate_rle` (which do not roll the
hash), when the symbol buffer is not full. -/
theorem literal_step_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level : d.level ≠ 0) (look : 1 ≤ d.lookahead.toNat)
    (noRoll : d.strategy.toInt = 2 ∨ d.strategy.toInt = 3) (noMatch : d.match_length = 0)
    (pending : d.pending = 0) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    {α : Type} (k : Bool → M α) :
    ∃ b buf' c h3,
      (do
        let d ← ldDeflateState (some (.tab ds))
        let c ← index8 d.window d.strstart.toNat
        let bflush ← tally_lit (some (.tab ds)) c
        wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
        k bflush) h = k (d.sym_next + 3 == d.sym_end) h3 ∧
      h3 = setD (Zlib.Trees.Proofs.Out.setB h b buf') ds (literalStep d c) ∧
      d.pending_buf = .ref (.blk b) 0 ∧
      DGood h3 r ds z (literalStep d c) ∧
      (literalStep d c).lookahead.toNat = d.lookahead.toNat - 1 ∧
      (literalStep d c).strstart.toNat = d.strstart.toNat + 1 ∧ StreamBuffers h3 r ∧
      ((d.sym_next + 3 == d.sym_end) = true → ∃ xs', BlockReady h3 r ds z (literalStep d c) b buf' xs') ∧
      ((d.sym_next + 3 == d.sym_end) = false → DInv h3 r ds z (literalStep d c)) := by
  obtain ⟨b, buf, buf', xs, c, h3, run, h3def, trees, ledger, dist, bufEq, good3, trees3, ledger3, chains3,
    count, ssEq, laEq, notFull⟩ := literal_step_run inv level look k
  have buffers3 : StreamBuffers h3 r := by
    rw [h3def]; rw [h3def] at good3
    exact private_write_buffers inv.good buffers trees.base.pbuf ⟨rfl, rfl, rfl, rfl⟩ good3
  have staticEq : h3.static = h.static := by rw [h3def]; rfl
  have chainsA : Chains h3 (literalStep d c) := by
    unfold Chains
    change HeapChains h3 (literalStep d c) ((literalStep d c).strstart.toNat - d.insert.toNat)
    rw [ssEq]; exact chains3
  have hashingA : Hashing h3 (literalStep d c) := by
    refine ⟨fun _ => chainsA, fun one => ?_, fun a b _ => ?_⟩
    · have zero := inv.shape.slides.2 level
      change d.«matches» = 1 at one
      rw [zero] at one
      cases one
    · rcases noRoll with e | e
      · exact absurd e a
      · exact absurd e b
  refine ⟨b, buf', c, h3, run, h3def, trees.base.pbuf, good3, laEq, ssEq, buffers3, fun full => ?_,
    fun flag => ?_⟩
  · have shape := inv.shape
    have room := shape.room
    refine ⟨xs ++ [⟨0, c.toNat⟩], ⟨good3, inv.alloc, by unfold LibraryGlobals; rw [staticEq]; exact inv.globals,
      trees3, ledger3, ⟨inv.symbols.clear.bl, inv.symbols.clear.opt, inv.symbols.clear.fixed⟩, ?_, hashingA,
      pending, (block_start_low inv level : -(2 : Int) ^ 62 ≤ d.block_start.toInt), ?_, level, buffers3, out⟩⟩
    · refine flushed_shape ?_ ?_ ?_ shape.prevLength shape.matchLength shape.matchAvailable
        (fun zero => absurd zero level) ?_ ?_ shape.fastLazy shape.highWater shape.lastFlush shape.trailer
        shape.biValid shape.cursor (by have := shape.symRoom; change 0 < d.sym_end.toNat; omega) shape.slides
      · change (literalStep d c).strstart.toNat + (literalStep d c).lookahead.toNat ≤ d.window_size.toNat
        rw [ssEq, laEq]; omega
      · change d.insert.toNat ≤ (literalStep d c).strstart.toNat
        rw [ssEq]; have := shape.insert; omega
      · intro large
        change 3 ≤ (literalStep d c).lookahead.toNat at large
        rw [laEq] at large
        exact shape.insertDone (by omega)
      · intro avail
        change 1 ≤ (literalStep d c).strstart.toNat
        rw [ssEq]; omega
      · intro large
        change 3 ≤ d.match_length.toNat at large
        rw [noMatch] at large
        exact absurd large (by decide)
    · change d.block_start.toInt ≤ ((literalStep d c).strstart.toNat : Int)
      rw [ssEq]; have := shape.blockStart; omega
  have shape := inv.shape
  have strictA := notFull flag
  have room := shape.room
  have span := shape.blockSpan level
  have start := shape.blockStart
  have shapeA : Shape (literalStep d c) := by
    refine ⟨?_, ?_, ?_, shape.prevLength, shape.matchLength, shape.matchAvailable, ?_, ?_, ?_, ?_, ?_,
      shape.fastLazy, shape.highWater, shape.lastFlush, shape.trailer, shape.biValid, shape.cursor, strictA,
      shape.slides⟩
    · change (literalStep d c).strstart.toNat + (literalStep d c).lookahead.toNat ≤ d.window_size.toNat
      rw [ssEq, laEq]; omega
    · change d.insert.toNat ≤ (literalStep d c).strstart.toNat
      rw [ssEq]; have := shape.insert; omega
    · intro large
      change 3 ≤ (literalStep d c).lookahead.toNat at large
      rw [laEq] at large
      exact shape.insertDone (by omega)
    · change d.block_start.toInt ≤ ((literalStep d c).strstart.toNat : Int)
      rw [ssEq]; omega
    · intro _
      change ((literalStep d c).strstart.toNat : Int) - d.block_start.toInt ≤
        258 * ((literalStep d c).sym_next.toNat / 3 : Nat) + d.match_available.toInt
      rw [ssEq, count]
      have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
      rw [div]
      push_cast
      omega
    · intro zero; exact absurd zero level
    · intro avail
      change 1 ≤ (literalStep d c).strstart.toNat
      rw [ssEq]; omega
    · intro large
      change 3 ≤ d.match_length.toNat at large
      rw [noMatch] at large
      exact absurd large (by decide)
  refine ⟨good3, inv.alloc, by unfold LibraryGlobals; rw [staticEq]; exact inv.globals, shapeA, hashingA, ?_⟩
  · refine ⟨⟨xs ++ [⟨0, c.toNat⟩], ⟨b, buf', trees.base.pbuf, by rw [h3def]; simp, ledger3⟩, ?_⟩,
      ⟨inv.symbols.clear.bl, inv.symbols.clear.opt, inv.symbols.clear.fixed⟩, ?_⟩
    · intro s mem
      rcases List.mem_append.mp mem with old | new
      · exact dist s old
      · simp only [List.mem_singleton] at new
        subst new
        exact Nat.zero_le _
    · intro b0 off pout _
      change d.pending_out = _ at pout
      rw [shape.cursor pending, trees.base.pbuf] at pout
      simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
      change off + d.pending.toNat ≤ d.lit_bufsize.toNat
      rw [← pout.2, pending]
      exact Nat.zero_le _



theorem advance_ne_null {p : BPtr} (n : Nat) (ne : p ≠ .null) : advance p n ≠ .null := by
  cases p with
  | null => exact absurd rfl ne
  | ref r i => simp [advance]

/-- The window side and the stream entry facts that a flush keeps, for the loop invariants. -/
structure FlushKeeps (z z' : ZStream) (d result : DeflateState) : Prop where
  strstart : result.strstart = d.strstart
  lookahead : result.lookahead = d.lookahead
  insert : result.insert = d.insert
  matchLength : result.match_length = d.match_length
  matchAvailable : result.match_available = d.match_available
  prevLength : result.prev_length = d.prev_length
  level : result.level = d.level
  strategy : result.strategy = d.strategy
  status : result.status = d.status
  wrap : result.wrap = d.wrap
  windowSize : result.window_size = d.window_size
  symNext : result.sym_next = 0
  availIn : z'.avail_in = z.avail_in
  nextIn : z'.next_in = z.next_in

set_option maxHeartbeats 1600000 in
/-- **`FLUSH_BLOCK(s, last)`**: the block flush, then the early return when the caller's output
buffer is full. Without a return the pending buffer is empty and there is output room. -/
theorem flush_block_macro (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (ready : BlockReady h r ds z d pb buf xs) (last : Bool) :
    ∃ opt produced after z' result,
      FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (opt, after) ∧
      DInv after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      FlushKeeps z z' d result ∧ z'.next_out ≠ .null ∧
      (opt = none → result.pending = 0 ∧ (last = false → z'.avail_out ≠ 0)) ∧
      (last = false → opt = none ∨ opt = some need_more) ∧
      (last = true → opt = none ∨ opt = some finish_started) ∧
      (last = true → opt = none → result.bi_valid.toInt = 0) := by
  obtain ⟨produced, after, z', result, run, invA, buffersA, account, drained, lastBits, fs, fl, fi, _, fml, _,
    fma, fpl, _, flv, fst, fsm, fstat, fwr, fws, _, symZero⟩ := flush_block_inv safe ready last
  have back : result.strm = some r := fsm.trans ready.good.live.back
  have stateA : after.dstates ds = some result := invA.good.live.hs
  have getA : r.get after = some z' := invA.good.live.hz
  have outA : z'.next_out ≠ .null := by
    rw [account.2.2.2.2.2.1]; exact advance_ne_null _ ready.out
  have keeps : FlushKeeps z z' d result :=
    ⟨fs, fl, fi, fml, fma, fpl, flv, fst, fstat, fwr, fws, symZero,
      by have := account.2.2.1; exact UInt32.toNat_inj.mp (by omega),
      by rw [account.2.2.2.2.1, advance_zero]⟩
  by_cases full : z'.avail_out = 0
  · cases last with
    | false =>
      refine ⟨some need_more, produced, after, z', result, ?_, invA, buffersA, account, keeps, outA,
        (fun e => by cases e), (fun _ => Or.inr rfl), (fun e => by cases e), (fun e => by cases e)⟩
      unfold FLUSH_BLOCK
      simp only [bind_app, show ((if false then 1 else 0 : Int32)) = 0 from rfl] at run ⊢
      simp only [run, ldDeflateState_tab stateA, back, zrd_eq, getA, full]
      rfl
    | true =>
      by_cases busy : (result.pending != 0 || result.wrap != 0) = true
      · refine ⟨some finish_started, produced, after, z', result, ?_, invA, buffersA, account, keeps, outA,
          (fun e => by cases e), (fun e => by cases e), (fun _ => Or.inr rfl), (fun _ e => by cases e)⟩
        unfold FLUSH_BLOCK
        simp only [bind_app, show ((if true then 1 else 0 : Int32)) = 1 from rfl] at run ⊢
        simp only [run, ldDeflateState_tab stateA, back, zrd_eq, getA, full]
        simp only [busy]
        rfl
      · have idle : result.pending = 0 := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at busy
          exact busy.1
        have busyF : (result.pending != 0 || result.wrap != 0) = false := by simpa using busy
        refine ⟨none, produced, after, z', result, ?_, invA, buffersA, account, keeps, outA,
          (fun _ => ⟨idle, fun e => by cases e⟩), (fun e => by cases e), (fun _ => Or.inl rfl),
          (fun _ _ => lastBits rfl)⟩
        unfold FLUSH_BLOCK
        simp only [bind_app, show ((if true then 1 else 0 : Int32)) = 1 from rfl] at run ⊢
        simp only [run, ldDeflateState_tab stateA, back, zrd_eq, getA, full]
        simp only [busyF]
        rfl
  · have idle : result.pending = 0 := by
      rcases drained with e | e
      · exact e
      · exact absurd e full
    refine ⟨none, produced, after, z', result, ?_, invA, buffersA, account, keeps, outA,
      (fun _ => ⟨idle, fun _ => full⟩), (fun _ => Or.inl rfl), (fun _ => Or.inl rfl), (fun t _ => lastBits t)⟩
    have nf : (z'.avail_out == 0) = false := by simpa using full
    unfold FLUSH_BLOCK
    simp only [bind_app] at run ⊢
    simp only [run, ldDeflateState_tab stateA, back, zrd_eq, getA, nf]
    rfl


/-! ## Loop states of the strategies -/

/-- The head of a strategy loop iteration (and the state a strategy returns from): the
invariant, the caller's buffers, the pointer facts `deflate` checked, and the strategy kind. -/
structure Head (kind : DeflateState → Prop) (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream)
    (d : DeflateState) : Prop where
  inv : DInv h r ds z d
  buffers : StreamBuffers h r
  out : z.next_out ≠ .null
  input : z.avail_in ≠ 0 → z.next_in ≠ .null
  level : d.level ≠ 0
  kind : kind d

/-- The measure of a strategy loop: one step per byte of input or lookahead, plus one for the
step that leaves the loop. -/
def loopMeasure (r : ZStreamRef) (ds : Nat) (st : LoopS) (h : Heap) : Nat :=
  if st.brk || st.ret.isSome then 0 else
    match r.get h, h.dstates ds with
    | some z, some d => 1 + 2 * (z.avail_in.toNat + d.lookahead.toNat)
    | _, _ => 0

theorem loop_measure_head {r : ZStreamRef} {ds : Nat} {st : LoopS} {h : Heap} {z : ZStream}
    {d : DeflateState} (get : r.get h = some z) (state : h.dstates ds = some d)
    (brk : st.brk = false) (ret : st.ret = none) :
    loopMeasure r ds st h = 1 + 2 * (z.avail_in.toNat + d.lookahead.toNat) := by
  simp [loopMeasure, brk, ret, get, state]

theorem loop_measure_exit {r : ZStreamRef} {ds : Nat} {st : LoopS} {h : Heap}
    (exit : st.brk = true ∨ st.ret.isSome = true) : loopMeasure r ds st h = 0 := by
  rcases exit with e | e <;> simp [loopMeasure, e]

theorem loop_measure_bound (r : ZStreamRef) (ds : Nat) (st : LoopS) (h : Heap) :
    loopMeasure r ds st h < fuel := by
  unfold loopMeasure fuel
  split
  · decide
  · split
    · rename_i z d _ _
      have a := z.avail_in.toNat_lt
      have b := d.lookahead.toNat_lt
      omega
    · decide

/-- A write of the state record alone keeps the caller's buffers. -/
theorem state_write_buffers {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d' : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (keys : d'.window = d.window ∧ d'.prev = d.prev ∧ d'.head = d.head ∧ d'.pending_buf = d.pending_buf)
    (good' : DGood (setD h ds d') r ds z d') : StreamBuffers (setD h ds d') r := by
  have frame : ByteFrame h (setD h ds d') (fun i => i = ds) := by
    refine ⟨rfl, fun _ _ => rfl, fun i outside => ?_, fun _ _ => rfl⟩
    simp [setD_dstates_ne _ _ _ _ outside]
  have owned := stream_owned_keys good good' keys.1 keys.2.1 keys.2.2.1 keys.2.2.2
  exact stream_buffers_private_read good.live.hz good'.live.hz buffers frame
    (fun i mine => (stream_owned_deflate good i).mpr (Or.inl mine)) owned (stream_accounting_self z) rfl

/-! ## `deflate_huff` -/

/-- The tail of an iteration of `deflate_huff` after the literal. -/
def huffTail (s : DeflateStatePtr) (st : LoopS) (bflush : Bool) : M LoopS := do
  if bflush then
    if let some r := (← FLUSH_BLOCK s 0) then return { st with bflush, ret := some r }
  return { st with bflush }

theorem huff_body_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    deflate_huff_body s flush st = (do
      if (← rd s (·.lookahead)) == 0 then
        fill_window s
        if (← rd s (·.lookahead)) == 0 then
          if flush == Z_NO_FLUSH then return { st with ret := some need_more }
          return { st with brk := true }
      wr s (fun d => { d with match_length := 0 })
      let d ← ldDeflateState s
      let c ← index8 d.window d.strstart.toNat
      let bflush ← tally_lit s c
      wr s (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
      huffTail s st bflush) := by
  unfold deflate_huff_body huffTail
  rfl


/-- The kind of a `deflate_huff` state. -/
def HuffKind (d : DeflateState) : Prop := d.strategy.toInt = 2

set_option maxHeartbeats 1600000 in
/-- **One literal iteration of `deflate_huff`** from a loop head with lookahead: the literal, and
the block flush when the symbol buffer is full. Either the loop continues from a new head with
one byte less of lookahead, or it returns `need_more` because the output buffer is full. -/
theorem huff_literal_iter (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head HuffKind h r ds z d) (look : 1 ≤ d.lookahead.toNat)
    (pending : d.pending = 0) (st : LoopS) :
    ∃ st' h',
      (do
        wr (some (.tab ds)) (fun d => { d with match_length := 0 })
        let d ← ldDeflateState (some (.tab ds))
        let c ← index8 d.window d.strstart.toNat
        let bflush ← tally_lit (some (.tab ds)) c
        wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
        huffTail (some (.tab ds)) st bflush) h = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head HuffKind h' r ds z' d' ∧ d'.pending = 0 ∧
          z'.avail_in.toNat + d'.lookahead.toNat + 1 = z.avail_in.toNat + d.lookahead.toNat) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head HuffKind h' r ds z' d')) := by
  obtain ⟨wrRun, inv1⟩ := clear_match_inv head.inv
  have buffers1 := state_write_buffers (d' := { d with match_length := 0 }) head.inv.good head.buffers
    ⟨rfl, rfl, rfl, rfl⟩ inv1.good
  obtain ⟨b, buf', c, h3, run, h3def, pbuf, good3, laEq, ssEq, buffers3, fullCase, notFullCase⟩ :=
    literal_step_inv inv1 head.level look (Or.inl head.kind) rfl pending buffers1 head.out
      (huffTail (some (.tab ds)) st)
  have start : (do
        wr (some (.tab ds)) (fun d => { d with match_length := 0 })
        let d ← ldDeflateState (some (.tab ds))
        let c ← index8 d.window d.strstart.toNat
        let bflush ← tally_lit (some (.tab ds)) c
        wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
        huffTail (some (.tab ds)) st bflush) h =
      huffTail (some (.tab ds)) st ({ d with match_length := 0 }.sym_next + 3 ==
        { d with match_length := 0 }.sym_end) h3 := by
    rw [bind_app, wrRun]
    exact run
  by_cases flag : ({ d with match_length := 0 }.sym_next + 3 == { d with match_length := 0 }.sym_end) = true
  · obtain ⟨xs', ready⟩ := fullCase flag
    obtain ⟨opt, produced, after, z', result, flushRun, invA, buffersA, account, keeps, outA, idle, choice, _, _⟩ :=
      flush_block_macro safe ready false
    have flushRun' : FLUSH_BLOCK (some (.tab ds)) 0 h3 = .ok (opt, after) := flushRun
    have inputA : z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
      rw [keeps.availIn, keeps.nextIn]; exact head.input
    have headA : Head HuffKind after r ds z' result :=
      ⟨invA, buffersA, outA, inputA, by rw [keeps.level]; exact head.level,
        by unfold HuffKind; rw [keeps.strategy]; exact head.kind⟩
    rcases choice rfl with none' | more
    · subst none'
      refine ⟨{ st with bflush := true }, after, ?_, rfl, Or.inl ⟨rfl, z', result, headA, (idle rfl).1, ?_⟩⟩
      · rw [start, flag]
        simp [huffTail, bind_app, flushRun']
      · rw [keeps.availIn, keeps.lookahead]
        change z.avail_in.toNat + (literalStep { d with match_length := 0 } c).lookahead.toNat + 1 = _
        rw [laEq]
        change _ + ({ d with match_length := 0 }.lookahead.toNat - 1) + 1 = _
        change _ + (d.lookahead.toNat - 1) + 1 = _
        omega
    · subst more
      refine ⟨{ st with bflush := true, ret := some need_more }, after, ?_, rfl, Or.inr ⟨rfl, z', result, headA⟩⟩
      rw [start, flag]
      simp [huffTail, bind_app, flushRun']
  · have notFull : ({ d with match_length := 0 }.sym_next + 3 == { d with match_length := 0 }.sym_end) = false := by
      simpa using flag
    have inv3 := notFullCase notFull
    refine ⟨{ st with bflush := false }, h3, ?_, rfl, Or.inl ⟨rfl, z, literalStep { d with match_length := 0 } c,
      ⟨inv3, buffers3, head.out, head.input, head.level, head.kind⟩, pending, ?_⟩⟩
    · rw [start, notFull]
      simp [huffTail]
    · rw [laEq]
      change _ + (d.lookahead.toNat - 1) + 1 = _
      omega


/-- The states of the `deflate_huff` loop: a head, a `need_more` return, or the `break` at the
end of the input with no lookahead. -/
def HuffLoop (r : ZStreamRef) (ds : Nat) (st : LoopS) (h : Heap) : Prop :=
  ∃ z d, Head HuffKind h r ds z d ∧
    ((st.brk = false ∧ st.ret = none ∧ d.pending = 0) ∨ st.ret = some need_more ∨
     (st.brk = true ∧ st.ret = none ∧ d.pending = 0 ∧ d.lookahead = 0 ∧ z.avail_in = 0))

theorem head_after_fill {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    {kind : DeflateState → Prop} (head : Head kind h r ds z d) (inv' : DInv after r ds z' d')
    (buffers' : StreamBuffers after r) (post : FillPost (d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) h after r ds z z' d d')
    (kindKeep : kind d → kind d') : Head kind after r ds z' d' := by
  obtain ⟨used, account, _⟩ := post.account
  obtain ⟨sLevel, _⟩ := post.same
  refine ⟨inv', buffers', ?_, ?_, by rw [sLevel]; exact head.level, kindKeep head.kind⟩
  · rw [account.2.2.2.2.2.1]; exact advance_ne_null _ head.out
  · intro nonempty
    rw [account.2.2.2.2.1]
    have count := account.2.2.1
    have before : z.avail_in ≠ 0 := by
      intro zero
      rw [zero] at count
      have z0 : (0 : UInt32).toNat = 0 := rfl
      rw [z0] at count
      exact nonempty (UInt32.toNat_inj.mp (by rw [z0]; omega))
    exact advance_ne_null _ (head.input before)

set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_huff`** from a loop head. -/
theorem huff_body_step (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head HuffKind h r ds z d) (pending : d.pending = 0) (flush : Int32)
    (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_huff_body (some (.tab ds)) flush st h = .ok (st', h') ∧ HuffLoop r ds st' h' ∧
      loopMeasure r ds st' h' < loopMeasure r ds st h := by
  have measure0 := loop_measure_head head.inv.good.live.hz head.inv.good.live.hs brk ret
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  rw [huff_body_source]
  by_cases empty : d.lookahead = 0
  · have emptyB : (d.lookahead == 0) = true := by simp [empty]
    have short : d.lookahead.toNat < 262 := by rw [empty]; decide
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨sLevel, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, sPending, _⟩ := post.same
    have head1 : Head HuffKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold HuffKind; rw [sStrategy]; exact k)
    have pending1 : d1.pending = 0 := sPending.trans pending
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    have consumed := post.consumed
    have fillRun' : fill_window (some (.tab ds)) after1 = fill_window (some (.tab ds)) after1 := rfl
    by_cases empty1 : d1.lookahead = 0
    · have empty1B : (d1.lookahead == 0) = true := by simp [empty1]
      have availZero : z1.avail_in = 0 := by
        rcases post.stopped with big | zero
        · rw [empty1] at big; exact absurd big (by decide)
        · exact zero
      by_cases noFlush : flush = Z_NO_FLUSH
      · refine ⟨{ st with ret := some need_more }, after1, ?_, ⟨z1, d1, head1, Or.inr (Or.inl rfl)⟩, ?_⟩
        · simp only [bind_app, rdLook, emptyB, ite_true]
          rw [show fill_window (some (.tab ds)) h = .ok ((), after1) from fillRun]
          simp only [bind_app, rdLook1, empty1B, ite_true, noFlush, beq_self_eq_true]
          rfl
        · rw [loop_measure_exit (Or.inr rfl), measure0]; omega
      · have noFlushB : (flush == Z_NO_FLUSH) = false := by simpa using noFlush
        refine ⟨{ st with brk := true }, after1, ?_,
          ⟨z1, d1, head1, Or.inr (Or.inr ⟨rfl, ret, pending1, empty1, availZero⟩)⟩, ?_⟩
        · simp only [bind_app, rdLook, emptyB, ite_true]
          rw [show fill_window (some (.tab ds)) h = .ok ((), after1) from fillRun]
          simp only [bind_app, rdLook1, empty1B, ite_true, noFlushB, Bool.false_eq_true, ite_false]
          rfl
        · rw [loop_measure_exit (Or.inl rfl), measure0]; omega
    · have empty1B : (d1.lookahead == 0) = false := by simpa using empty1
      have look1 : 1 ≤ d1.lookahead.toNat := by
        have : d1.lookahead.toNat ≠ 0 := fun e => empty1 (UInt32.toNat_inj.mp e)
        omega
      obtain ⟨st', h', iterRun, brk', choice⟩ := huff_literal_iter safe head1 look1 pending1 st
      refine ⟨st', h', ?_, ?_, ?_⟩
      · simp only [bind_app, rdLook, emptyB, ite_true]
        rw [show fill_window (some (.tab ds)) h = .ok ((), after1) from fillRun]
        simp only [bind_app, rdLook1, empty1B, Bool.false_eq_true, ite_false]
        exact iterRun
      · rcases choice with ⟨retEq, z', d', head', pending', _⟩ | ⟨retEq, z', d', head'⟩
        · exact ⟨z', d', head', Or.inl ⟨brk'.trans brk, retEq.trans ret, pending'⟩⟩
        · exact ⟨z', d', head', Or.inr (Or.inl retEq)⟩
      · rcases choice with ⟨retEq, z', d', head', pending', count⟩ | ⟨retEq, _⟩
        · rw [loop_measure_head head'.inv.good.live.hz head'.inv.good.live.hs (brk'.trans brk) (retEq.trans ret),
            measure0]
          omega
        · rw [loop_measure_exit (Or.inr (by rw [retEq]; rfl)), measure0]; omega
  · have emptyB : (d.lookahead == 0) = false := by simpa using empty
    have look : 1 ≤ d.lookahead.toNat := by
      have : d.lookahead.toNat ≠ 0 := fun e => empty (UInt32.toNat_inj.mp e)
      omega
    obtain ⟨st', h', iterRun, brk', choice⟩ := huff_literal_iter safe head look pending st
    refine ⟨st', h', ?_, ?_, ?_⟩
    · simp only [bind_app, rdLook, emptyB, Bool.false_eq_true, ite_false]
      exact iterRun
    · rcases choice with ⟨retEq, z', d', head', pending', _⟩ | ⟨retEq, z', d', head'⟩
      · exact ⟨z', d', head', Or.inl ⟨brk'.trans brk, retEq.trans ret, pending'⟩⟩
      · exact ⟨z', d', head', Or.inr (Or.inl retEq)⟩
    · rcases choice with ⟨retEq, z', d', head', pending', count⟩ | ⟨retEq, _⟩
      · rw [loop_measure_head head'.inv.good.live.hz head'.inv.good.live.hs (brk'.trans brk) (retEq.trans ret),
          measure0]
        omega
      · rw [loop_measure_exit (Or.inr (by rw [retEq]; rfl)), measure0]; omega


/-- The `deflate_huff` loop ends in a `need_more` return or a `break` at the end of the input. -/
theorem huff_loop (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head HuffKind h r ds z d) (pending : d.pending = 0) (flush : Int32) :
    ∃ st h', cwhile forever (deflate_huff_body (some (.tab ds)) flush) {} h = .ok (st, h') ∧
      HuffLoop r ds st h' ∧ (st.brk = true ∨ st.ret.isSome = true) := by
  have start : HuffLoop r ds {} h := ⟨z, d, head, Or.inl ⟨rfl, rfl, pending⟩⟩
  obtain ⟨st, h', run, loop, exit⟩ := cwhile_measure (cond := forever)
    (body := deflate_huff_body (some (.tab ds)) flush) (HuffLoop r ds)
    (fun st h => HuffLoop r ds st h ∧ (st.brk = true ∨ st.ret.isSome = true)) (loopMeasure r ds)
    (fun st h ⟨z, d, head, cases⟩ => by
      rcases cases with ⟨brk, ret, pending⟩ | ret | ⟨brk, ret, pending, _, _⟩
      · refine ⟨true, st, h, (by simp [forever, brk, ret]), (fun _ => ?_), (fun e => by cases e)⟩
        exact huff_body_step safe head pending flush st brk ret
      · refine ⟨false, st, h, (by simp [forever, ret]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z, d, head, Or.inr (Or.inl ret)⟩, Or.inr (by rw [ret]; rfl)⟩
      · refine ⟨false, st, h, (by simp [forever, brk]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z, d, head, Or.inr (Or.inr ⟨brk, ret, pending, by assumption, by assumption⟩)⟩, Or.inl brk⟩)
    start (loop_measure_bound r ds {} h)
  exact ⟨st, h', run, loop, exit⟩

/-- `s->insert = 0` (the end of `deflate_huff` and `deflate_rle`) keeps the loop head. -/
theorem clear_insert_head {kind : DeflateState → Prop} {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (head : Head kind h r ds z d)
    (kindKeep : kind d → kind { d with insert := 0 }) :
    wr (some (.tab ds)) (fun d => { d with insert := 0 }) h = .ok ((), setD h ds { d with insert := 0 }) ∧
      Head kind (setD h ds { d with insert := 0 }) r ds z { d with insert := 0 } := by
  refine ⟨by rw [wrD_eq, head.inv.good.live.hs], ?_⟩
  have inv := head.inv
  have shape := inv.shape
  have invA : DInv (setD h ds { d with insert := 0 }) r ds z { d with insert := 0 } := by
    refine engine_update_inv (d' := { d with insert := 0 }) inv rfl ?_ ?_
    · exact ⟨shape.room, Nat.zero_le _, fun _ => rfl, shape.prevLength, shape.matchLength,
        shape.matchAvailable, shape.blockStart, shape.blockSpan, shape.levelZero, shape.available,
        shape.pendingMatch, shape.fastLazy, shape.highWater, shape.lastFlush, shape.trailer, shape.biValid,
        shape.cursor, shape.symRoom, shape.slides⟩
    · obtain ⟨chains, slid, rolling⟩ := inv.hashing
      refine ⟨fun zero => ?_, fun one => ?_, fun a b large => ?_⟩
      · obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains zero
        exact ⟨w, p, q, wa, pa, qa, win, prev, head, by simpa using hw, by simpa using hp, by simpa using hq,
          chains_mono H (by
            change d.strstart.toNat - d.insert.toNat ≤ d.strstart.toNat - (0 : UInt32).toNat
            have z0 : (0 : UInt32).toNat = 0 := rfl
            rw [z0]; omega)
            (Nat.le_refl _)⟩
      · have zero := shape.slides.2 head.level
        change d.«matches» = 1 at one
        rw [zero] at one; cases one
      · obtain ⟨w, wa, win, hw, form⟩ := rolling a b large
        exact ⟨w, wa, win, by simpa using hw, form⟩
  exact ⟨invA, state_write_buffers (d' := { d with insert := 0 }) inv.good head.buffers ⟨rfl, rfl, rfl, rfl⟩
    invA.good, head.out, head.input, head.level, kindKeep head.kind⟩

set_option maxHeartbeats 1600000 in
/-- The end of the compression functions: the last block of a `Z_FINISH` call, or the current
block when it has symbols. -/
theorem finish_tail_inv (safe : FlushSafe) {kind : DeflateState → Prop} {h : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} (head : Head kind h r ds z d) (pending : d.pending = 0)
    (flush : Int32) :
    ∃ bstate after z' d', finish_tail (some (.tab ds)) flush h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r := by
  obtain ⟨pb, buf, xs, ready⟩ := head.inv.ready pending head.level head.buffers head.out
  by_cases finish : flush = Z_FINISH
  · obtain ⟨opt, _, after, z', result, run, invA, buffersA, _⟩ := flush_block_macro safe ready true
    have run' : FLUSH_BLOCK (some (.tab ds)) 1 h = .ok (opt, after) := run
    cases opt with
    | none =>
      refine ⟨finish_done, after, z', result, ?_, invA, buffersA⟩
      simp [finish_tail, finish, bind_app, run']
    | some b =>
      refine ⟨b, after, z', result, ?_, invA, buffersA⟩
      simp [finish_tail, finish, bind_app, run']
  · have finishB : (flush == Z_FINISH) = false := by simpa using finish
    have rdSym : rd (some (.tab ds)) (·.sym_next) h = .ok (d.sym_next, h) := by
      simp [rdD_eq, head.inv.good.live.hs]
    by_cases symbols : d.sym_next = 0
    · refine ⟨block_done, h, z, d, ?_, head.inv, head.buffers⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols]
    · have symbolsB : (d.sym_next != 0) = true := by simpa using symbols
      obtain ⟨opt, _, after, z', result, run, invA, buffersA, _⟩ := flush_block_macro safe ready false
      have run' : FLUSH_BLOCK (some (.tab ds)) 0 h = .ok (opt, after) := run
      cases opt with
      | none =>
        refine ⟨block_done, after, z', result, ?_, invA, buffersA⟩
        simp [finish_tail, finishB, bind_app, rdSym, symbolsB, symbols, run']
      | some b =>
        refine ⟨b, after, z', result, ?_, invA, buffersA⟩
        simp [finish_tail, finishB, bind_app, rdSym, symbolsB, symbols, run']

/-- **`deflate_huff` keeps the invariant** (`Z_HUFFMAN_ONLY` at a nonzero level), given the block
flush of batch C. -/
theorem huff_spec_of (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (level : d.level ≠ 0) (huff : d.strategy.toInt = 2) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_huff (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r := by
  have head : Head HuffKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, huff⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, cases⟩, exit⟩ := huff_loop safe head entry.pending flush
  rcases cases with ⟨brk, ret0, _⟩ | ret | ⟨brk, ret, pending1, _, _⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv, head1.buffers⟩
    simp [C.run, deflate_huff, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := clear_insert_head head1 id
    obtain ⟨bstate, after, z', d', tailRun, invA, buffersA⟩ := finish_tail_inv safe head2 pending1 flush
    refine ⟨bstate, after, z', d', ?_, invA, buffersA⟩
    simp only [C.run, deflate_huff, bind_app, loopRun, ret, wrRun]
    exact tailRun


/-! ## `deflate_rle`: the run scan -/

/-- The condition of the run scan of `deflate_rle` (eight comparisons with `prev`, then
`scan < strend`), as written in the translation. -/
def rleCond (prev : UInt32) (strend : BPtr) : BPtr → M (Bool × BPtr) := fun scan => do
  let mut scan := scan
  for _ in [0:8] do
    scan ← padd scan 1
    if prev != (← load8 scan).toUInt32 then return (false, scan)
  return (← Ptr.lt scan strend, scan)

/-- The same condition with an explicit count of comparisons. -/
def rleCondR (prev : UInt32) (strend : BPtr) : Nat → BPtr → M (Bool × BPtr)
  | 0, scan => do return (← Ptr.lt scan strend, scan)
  | n + 1, scan => do
    let scan ← padd scan 1
    if prev != (← load8 scan).toUInt32 then return (false, scan)
    rleCondR prev strend n scan

theorem rle_cond_eq (prev : UInt32) (strend scan : BPtr) :
    rleCond prev strend scan = rleCondR prev strend 8 scan := by
  unfold rleCond
  simp [List.range', List.forIn'_cons, List.forIn'_nil, rleCondR, Zlib.Deflate.Engine.Proofs.M_bind_assoc,
    Zlib.Deflate.Engine.Proofs.M_pure_bind, Zlib.Deflate.Engine.Proofs.M_ite_bind]

/-- The first of `n` positions after `t` whose byte differs from `prev`. -/
def runSteps (w : Nat → UInt8) (S : Nat) (prev : UInt32) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, t => if (w (S + t + 1)).toUInt32 ≠ prev then some (t + 1) else runSteps w S prev n (t + 1)

theorem runSteps_some {w : Nat → UInt8} {S : Nat} {prev : UInt32} :
    ∀ n t k, runSteps w S prev n t = some k → t + 1 ≤ k ∧ k ≤ t + n ∧ (w (S + k)).toUInt32 ≠ prev ∧
      ∀ j, t + 1 ≤ j → j < k → (w (S + j)).toUInt32 = prev := by
  intro n
  induction n with
  | zero => intro t k h; simp [runSteps] at h
  | succ n ih =>
    intro t k h
    unfold runSteps at h
    split at h
    · rename_i hne
      cases h
      exact ⟨by omega, by omega, by rwa [show S + (t + 1) = S + t + 1 by omega], fun j h1 h2 => by omega⟩
    · rename_i heq
      obtain ⟨a, b, c, d⟩ := ih (t + 1) k h
      refine ⟨by omega, by omega, c, fun j h1 h2 => ?_⟩
      by_cases hj : j = t + 1
      · subst hj
        have e : (w (S + t + 1)).toUInt32 = prev := by simpa using heq
        rwa [show S + (t + 1) = S + t + 1 by omega]
      · exact d j (by omega) h2

theorem runSteps_none {w : Nat → UInt8} {S : Nat} {prev : UInt32} :
    ∀ n t, runSteps w S prev n t = none → ∀ j, t + 1 ≤ j → j ≤ t + n → (w (S + j)).toUInt32 = prev := by
  intro n
  induction n with
  | zero => intro t _ j h1 h2; omega
  | succ n ih =>
    intro t h j h1 h2
    unfold runSteps at h
    split at h
    · simp at h
    · rename_i heq
      by_cases hj : j = t + 1
      · subst hj
        have e : (w (S + t + 1)).toUInt32 = prev := by simpa using heq
        rwa [show S + (t + 1) = S + t + 1 by omega]
      · exact ih (t + 1) h j (by omega) (by omega)

theorem rleCondR_ok {h : Heap} {wb : Nat} {wa : Array UInt8} (hw : h.bytes wb = some wa) (S : Nat)
    (prev : UInt32) (hS : S + 258 < wa.size) :
    ∀ n t, t + n ≤ 258 →
      rleCondR prev (.ref (.blk wb) (S + 258)) n (.ref (.blk wb) (S + t)) h =
        .ok ((match runSteps (bfn wa) S prev n t with
          | some k => (false, Ptr.ref (BRef.blk wb) (S + k))
          | none => (decide (S + (t + n) < S + 258), Ptr.ref (BRef.blk wb) (S + (t + n)))), h) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have : OkOn h (Ptr.lt (Ptr.ref (BRef.blk wb) (S + t)) (Ptr.ref (BRef.blk wb) (S + 258))) (decide (S + t < S + 258)) :=
      Ptr.lt_ok (r := BRef.blk wb) (by simpa using hw) (by omega) (by omega)
    simp only [rleCondR, runSteps, bind_app, Nat.add_zero]
    unfold OkOn at this
    rw [this]; rfl
  | succ n ih =>
    intro t ht
    have g : Space.get h (BRef.blk wb) = some wa := by simpa using hw
    have hs1 : S + t + 1 < wa.size := by omega
    have p1 : padd (Ptr.ref (BRef.blk wb) (S + t)) 1 h = .ok (Ptr.ref (BRef.blk wb) (S + t + 1), h) :=
      padd_ok' g (by omega)
    have l1 : load8 (Ptr.ref (BRef.blk wb) (S + t + 1)) h = .ok (wa[S + t + 1], h) := Ptr.load_ok g hs1
    have b1 : bfn wa (S + t + 1) = wa[S + t + 1] := by simp [bfn, Array.getD_eq_getD_getElem?, hs1]
    simp only [rleCondR, bind_app, p1, l1]
    by_cases hne : prev = (wa[S + t + 1]).toUInt32
    · have hne' : ¬ ((bfn wa (S + t + 1)).toUInt32 ≠ prev) := by rw [b1]; simp [hne]
      have hih := ih (t + 1) (by omega)
      rw [show S + (t + 1) = S + t + 1 by omega, show t + 1 + n = t + (n + 1) by omega] at hih
      have hb : (prev != (wa[S + t + 1]).toUInt32) = false := by simp [hne]
      simp only [runSteps, hne', ite_false, hb, Bool.false_eq_true, hih]
    · have hne' : (bfn wa (S + t + 1)).toUInt32 ≠ prev := by rw [b1]; exact fun e => hne e.symm
      have hb : (prev != (wa[S + t + 1]).toUInt32) = true := by simpa using hne
      simp only [runSteps, ite_eq_left hne', hb]
      rfl

/-- **The run scan of `deflate_rle`.** From `scan = strstart + 2` (the three bytes after the
previous one equal it), with 258 bytes of room, the loop does not fault, leaves the heap, and
stops at `strstart + j` with `3 ≤ j ≤ 258`: the bytes before agree with `prev`, and the byte at
`j` does not unless `j = 258`. -/
theorem rle_scan_loop {h : Heap} {wb : Nat} {wa : Array UInt8} (hw : h.bytes wb = some wa) (S : Nat)
    (prev : UInt32) (hS : S + 258 < wa.size) :
    ∃ j, cdoWhile (fun x => (pure x : M BPtr)) (rleCond prev (Ptr.ref (BRef.blk wb) (S + 258)))
        (Ptr.ref (BRef.blk wb) (S + 2)) h = .ok (Ptr.ref (BRef.blk wb) (S + j), h) ∧
      3 ≤ j ∧ j ≤ 258 ∧ (∀ k, 3 ≤ k → k < j → (bfn wa (S + k)).toUInt32 = prev) ∧
      (j < 258 → (bfn wa (S + j)).toUInt32 ≠ prev) := by
  let Inv : BPtr → Heap → Prop := fun s h' =>
    h' = h ∧ ∃ j, j % 8 = 2 ∧ 2 ≤ j ∧ j ≤ 250 ∧ s = Ptr.ref (BRef.blk wb) (S + j) ∧
      ∀ k, 3 ≤ k → k ≤ j → (bfn wa (S + k)).toUInt32 = prev
  let Q : BPtr → Heap → Prop := fun s h' =>
    h' = h ∧ ∃ j, s = Ptr.ref (BRef.blk wb) (S + j) ∧ 3 ≤ j ∧ j ≤ 258 ∧
      (∀ k, 3 ≤ k → k < j → (bfn wa (S + k)).toUInt32 = prev) ∧
      (j < 258 → (bfn wa (S + j)).toUInt32 ≠ prev)
  let μ : BPtr → Nat := fun s => match s with | .null => 0 | .ref _ o => 258 - (o - S)
  have key := cdoWhile_measure (σ := BPtr)
    (body := fun x => (pure x : M BPtr))
    (cond := rleCond prev (Ptr.ref (BRef.blk wb) (S + 258)))
    Inv μ Q ?_ (s := Ptr.ref (BRef.blk wb) (S + 2)) (h := h)
    ⟨rfl, 2, by omega, by omega, by omega, rfl, fun k hk1 hk2 => by omega⟩ (by unfold fuel; simp only [μ]; omega)
  · obtain ⟨s', h', hrun, hq, j, hs, rest⟩ := key
    subst hq hs
    exact ⟨j, hrun, rest⟩
  · intro s h' hI
    obtain ⟨hh', j, hj8, hj2, hj250, hs, hag⟩ := hI
    have hh2 := hh'.symm
    subst hh2
    subst hs
    have hrun := rleCondR_ok hw S prev hS 8 j (by omega)
    cases hcs : runSteps (bfn wa) S prev 8 j with
    | some k =>
      obtain ⟨hk1, hk2, hk3, hk4⟩ := runSteps_some 8 j k hcs
      refine ⟨_, h, false, Ptr.ref (BRef.blk wb) (S + k), h, rfl, ?_, ?_, ?_⟩
      · simp only [bind_app, rle_cond_eq, hrun, hcs]
        try rfl
      · intro _
        refine ⟨rfl, k, rfl, by omega, by omega, fun q hq1 hq2 => ?_, fun _ => hk3⟩
        by_cases hqj : q ≤ j
        · exact hag q hq1 hqj
        · exact hk4 q (by omega) hq2
      · intro hc; simp at hc
    | none =>
      have hn := runSteps_none 8 j hcs
      by_cases hlt : S + (j + 8) < S + 258
      · refine ⟨_, h, true, Ptr.ref (BRef.blk wb) (S + (j + 8)), h, rfl, ?_, ?_, ?_⟩
        · simp [bind_app, rle_cond_eq, hrun, hcs, hlt]
        · intro hc; simp at hc
        · intro _
          refine ⟨⟨rfl, j + 8, by omega, by omega, by omega, rfl, ?_⟩, ?_⟩
          · intro k hk1 hk2
            by_cases hkj : k ≤ j
            · exact hag k hk1 hkj
            · exact hn k (by omega) (by omega)
          · simp only [μ]; omega
      · refine ⟨_, h, false, Ptr.ref (BRef.blk wb) (S + (j + 8)), h, rfl, ?_, ?_, ?_⟩
        · simp [bind_app, rle_cond_eq, hrun, hcs, hlt]
        · intro _
          refine ⟨rfl, j + 8, rfl, by omega, by omega, fun q hq1 hq2 => ?_, fun big => by omega⟩
          by_cases hqj : q ≤ j
          · exact hag q hq1 hqj
          · exact hn q (by omega) (by omega)
        · intro hc; simp at hc

end Zlib.Deflate.Universal
