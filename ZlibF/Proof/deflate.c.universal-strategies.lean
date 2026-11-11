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

/-- The invariant after one literal of `deflate_huff` or `deflate_rle` (which do not roll the
hash), when the symbol buffer is not full. -/
theorem literal_step_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level : d.level ≠ 0) (look : 1 ≤ d.lookahead.toNat)
    (noRoll : d.strategy.toInt = 2 ∨ d.strategy.toInt = 3) (noMatch : d.match_length = 0)
    (pending : d.pending = 0) {α : Type} (k : Bool → M α) :
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
      ((d.sym_next + 3 == d.sym_end) = false → DInv h3 r ds z (literalStep d c)) := by
  obtain ⟨b, buf, buf', xs, c, h3, run, h3def, trees, ledger, dist, bufEq, good3, trees3, ledger3, chains3,
    count, ssEq, laEq, notFull⟩ := literal_step_run inv level look k
  refine ⟨b, buf', c, h3, run, h3def, trees.base.pbuf, good3, laEq, fun flag => ?_⟩
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
  have staticEq : h3.static = h.static := by rw [h3def]; rfl
  refine ⟨good3, inv.alloc, by unfold LibraryGlobals; rw [staticEq]; exact inv.globals, shapeA, ?_, ?_⟩
  · refine ⟨fun _ => ?_, fun one => ?_, fun a b _ => ?_⟩
    · unfold Chains
      change HeapChains h3 (literalStep d c) ((literalStep d c).strstart.toNat - d.insert.toNat)
      rw [ssEq]; exact chains3
    · have zero := shape.slides.2 level
      change d.«matches» = 1 at one
      rw [zero] at one
      cases one
    · rcases noRoll with e | e
      · exact absurd e a
      · exact absurd e b
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

end Zlib.Deflate.Universal
