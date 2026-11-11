import ZlibF.Proof.«deflate.c.universal-window»
import ZlibF.Proof.«trees.c.universal-flush»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-private-arrays»
import ZlibF.Proof.«deflate.c.engine.match-insert-loop»
import ZlibF.Proof.«deflate.c.engine.match-consume»

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



theorem recorded_trees_of {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d)
    (recorded : ∃ xs, Recorded h d xs ∧ ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262) :
    ∃ b buf xs, TreesInvAt h ds d b buf ∧ SymbolLedger buf d xs ∧
      ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262 := by
  obtain ⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩ := recorded
  exact ⟨b, a, xs, trees_at_of_good good pbuf get, ledger, dist⟩

set_option maxHeartbeats 1600000 in
/-- **One literal, general form**: the same run from explicit premises instead of `DInv`
(inside `deflate_fast` and `deflate_slow` the state after `INSERT_STRING` is not `DInv`). -/
theorem literal_step_core {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {top : Nat} (good : DGood h r ds z d)
    (recorded : ∃ xs, Recorded h d xs ∧ ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262)
    (room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (chains : HeapChains h d top)
    (look : 1 ≤ d.lookahead.toNat) {α : Type} (k : Bool → M α) :
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
      HeapChains h3 (literalStep d c) top ∧
      (literalStep d c).sym_next.toNat = d.sym_next.toNat + 3 ∧
      (literalStep d c).strstart.toNat = d.strstart.toNat + 1 ∧
      (literalStep d c).lookahead.toNat = d.lookahead.toNat - 1 ∧
      ((d.sym_next + 3 == d.sym_end) = false →
        (literalStep d c).sym_next.toNat < (literalStep d c).sym_end.toNat) := by
  obtain ⟨b, buf, xs, trees, ledger, dist⟩ := recorded_trees_of good recorded
  obtain ⟨w, wa, win, get, size⟩ := window_block good
  have roomT := literal_room good.inv strict
  have readC : index8 d.window d.strstart.toNat h = .ok (bfn wa d.strstart.toNat, h) := by
    rw [win]; exact index8_bfn get (by simp) (by omega)
  obtain ⟨c, cdef⟩ : ∃ x, x = bfn wa d.strstart.toNat := ⟨_, rfl⟩
  rw [← cdef] at readC
  have tallyRun := tally_literal_run trees.base c roomT
  obtain ⟨h2, h2def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c) :=
    ⟨_, rfl⟩
  rw [← h2def] at tallyRun
  have chains2 : HeapChains h2 (literalState d c) top := by
    rw [h2def]; exact pending_write_chains good chains trees.base.pbuf _ c
  have good2 : DGood h2 r ds z (literalState d c) := by rw [h2def]; exact literal_good_after good trees c roomT
  have ledger2 := ledger_literal trees.base ledger roomT c
  have count := literal_count trees.base roomT c
  have wsz := good.inv.wsz
  have wsHi := (slide_window_sizes good).2
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
  · simp only [bind_app, ldDeflateState_tab good.live.hs, readC, tallyRun, write]
  · exact trees_at_of_good good3 trees.base.pbuf (by rw [h3def]; simp)
  · exact ledger2.keep rfl rfl rfl rfl
  · have at2 : HeapChainsAt h2 (literalState d c) top
        (d.strstart.toNat + d.lookahead.toNat) := chains2
    have at3 : HeapChainsAt h3 d3 top
        (d.strstart.toNat + d.lookahead.toNat) :=
      at2.keep (by rw [h3eq]; rfl) (by rw [h3eq]; rfl) rfl rfl rfl rfl rfl rfl rfl
    exact at3.collapse (by change _ = (d.strstart + 1).toNat + (d.lookahead - 1).toNat; omega)
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


/-! ## `deflate_rle`: a run -/

/-- The state after the run of length `ml` at distance 1 is recorded and passed. -/
def runStep (d : DeflateState) (ml : UInt32) : DeflateState :=
  { matchSymbolState { d with match_length := ml } 1 (ml - MIN_MATCH_u) with
    lookahead := d.lookahead - ml, strstart := d.strstart + ml, match_length := 0 }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **One run of `deflate_rle`.** From `DInv` (after `s->match_length = 0`) and the run length
`ml` the scan wrote (`3 ≤ ml ≤ 258`, within the lookahead), `_tr_tally_dist(s, 1, ml - 3)` and the
advance run; afterwards `DInv` holds when the symbol buffer is not full, and the flush can start
when it is. -/
theorem run_step_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (level : d.level ≠ 0) (noRoll : d.strategy.toInt = 2 ∨ d.strategy.toInt = 3)
    (noMatch : d.match_length = 0) (pending : d.pending = 0) (buffers : StreamBuffers h r)
    (out : z.next_out ≠ .null) (ml : UInt32) (lo : 3 ≤ ml.toNat) (hi : ml.toNat ≤ 258)
    (within : ml.toNat ≤ d.lookahead.toNat) {α : Type} (k : Bool → M α) :
    ∃ b buf' h3,
      (do
        let bflush ← tally_dist (some (.tab ds)) 1 (ml - MIN_MATCH_u)
        wr (some (.tab ds)) (fun d =>
          { d with lookahead := d.lookahead - d.match_length, strstart := d.strstart + d.match_length, match_length := 0 })
        k bflush) (setD h ds { d with match_length := ml }) = k (d.sym_next + 3 == d.sym_end) h3 ∧
      DGood h3 r ds z (runStep d ml) ∧
      (runStep d ml).lookahead.toNat = d.lookahead.toNat - ml.toNat ∧
      (runStep d ml).strstart.toNat = d.strstart.toNat + ml.toNat ∧ StreamBuffers h3 r ∧
      ((d.sym_next + 3 == d.sym_end) = true → ∃ xs', BlockReady h3 r ds z (runStep d ml) b buf' xs') ∧
      ((d.sym_next + 3 == d.sym_end) = false → DInv h3 r ds z (runStep d ml)) := by
  obtain ⟨b, buf, xs, trees, ledger, dist⟩ := recorded_trees inv
  let ds0 : DeflateState := { d with match_length := ml }
  have update0 : EngineUpdate d ds0 := rfl
  have good0 : DGood (setD h ds ds0) r ds z ds0 := engine_update_good inv.good update0
  have trees0 : TreesInvAt (setD h ds ds0) ds ds0 b buf :=
    trees_at_of_good good0 trees.base.pbuf (by simpa using trees.base.bytes)
  have ledger0 : SymbolLedger buf ds0 xs := ledger.keep rfl rfl rfl rfl
  have chains0 : HeapChains (setD h ds ds0) ds0 (d.strstart.toNat - d.insert.toNat) := by
    obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := inv.chains level
    exact ⟨w, p, q, wa, pa, qa, win, prev, head, by simpa using hw, by simpa using hp, by simpa using hq, H⟩
  have strict := inv.shape.symRoom
  have roomT : ds0.sym_next.toNat + 3 ≤ ds0.sym_end.toNat := literal_room good0.inv strict
  have len3 : (ml - MIN_MATCH_u).toNat = ml.toNat - 3 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by change 3 ≤ ml.toNat; exact lo))
  have tallyRun := tally_match_run trees0.base 1 (ml - MIN_MATCH_u) (by decide) (by decide) roomT
  have ledger2 := ledger_match trees0.base ledger0 roomT 1 (ml - MIN_MATCH_u) (by decide) (by decide)
    (by rw [len3]; omega)
  let buf' := matchBytes buf ds0 (1 : UInt32).toUInt16 (ml - MIN_MATCH_u).toUInt8
  let d2 := matchSymbolState ds0 1 (ml - MIN_MATCH_u)
  obtain ⟨h2, h2def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB (setD h ds ds0) b buf') ds d2 := ⟨_, rfl⟩
  have tallyRun : tally_dist (some (.tab ds)) 1 (ml - MIN_MATCH_u) (setD h ds ds0) =
      .ok (ds0.sym_next + 3 == ds0.sym_end, h2) := by rw [h2def]; exact tallyRun
  have good2 : DGood h2 r ds z d2 := by
    rw [h2def]; exact match_good_after good0 trees0 1 (ml - MIN_MATCH_u) roomT
  have trees2 : TreesInvAt h2 ds d2 b buf' := by
    rw [h2def]; exact tally_match_trees trees0 1 (ml - MIN_MATCH_u) roomT
  have chains2 : HeapChains h2 d2 (d.strstart.toNat - d.insert.toNat) := by
    rw [h2def]
    obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ :=
      pending_write_chains good0 chains0 trees0.base.pbuf buf' 0
    exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩
  have count : d2.sym_next.toNat = d.sym_next.toNat + 3 := literal_count trees0.base roomT 0
  have notFull : (d.sym_next + 3 == d.sym_end) = false → d2.sym_next.toNat < d2.sym_end.toNat :=
    fun flag => literal_not_full trees0 0 roomT flag
  have wsHi := (slide_window_sizes inv.good).2
  have wsz := inv.good.inv.wsz
  have room := inv.shape.room
  have ssEq : (d.strstart + ml).toNat = d.strstart.toNat + ml.toNat := by
    rw [UInt32.toNat_add]; omega
  have laEq : (d.lookahead - ml).toNat = d.lookahead.toNat - ml.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr within)
  let d3 := runStep d ml
  obtain ⟨h3, h3def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB (setD h ds ds0) b buf') ds d3 := ⟨_, rfl⟩
  have h3eq : h3 = setD h2 ds d3 := by rw [h3def, h2def, setD_setD]
  have update : EngineUpdate d2 d3 := rfl
  have good3 : DGood h3 r ds z d3 := by rw [h3eq]; exact engine_update_good good2 update
  have state2 : h2.dstates ds = some d2 := by rw [h2def]; simp
  have write : wr (some (.tab ds)) (fun d =>
      { d with lookahead := d.lookahead - d.match_length, strstart := d.strstart + d.match_length, match_length := 0 })
      h2 = .ok ((), h3) := by
    rw [wrD_eq, state2, h3eq]
    rfl
  have trees3 : TreesInvAt h3 ds d3 b buf' := trees_at_of_good good3 trees.base.pbuf (by rw [h3def]; simp)
  have ledger3 : SymbolLedger buf' d3 (xs ++ [⟨(1 : UInt32).toNat, (ml - MIN_MATCH_u).toNat⟩]) :=
    ledger2.keep rfl rfl rfl rfl
  have ssEq3 : d3.strstart.toNat = d.strstart.toNat + ml.toNat := ssEq
  have laEq3 : d3.lookahead.toNat = d.lookahead.toNat - ml.toNat := laEq
  have chains3 : Chains h3 d3 := by
    have at2 : HeapChainsAt h2 d2 (d.strstart.toNat - d.insert.toNat) (d.strstart.toNat + d.lookahead.toNat) := chains2
    have at3 : HeapChainsAt h3 d3 (d.strstart.toNat - d.insert.toNat) (d.strstart.toNat + d.lookahead.toNat) :=
      at2.keep (by rw [h3eq]; rfl) (by rw [h3eq]; rfl) rfl rfl rfl rfl rfl rfl rfl
    have collapsed := at3.collapse (by rw [ssEq3, laEq3]; omega)
    unfold Chains
    change HeapChains h3 d3 (d3.strstart.toNat - d.insert.toNat)
    rw [ssEq3]
    exact heap_chains_raise collapsed (by omega)
  have staticEq : h3.static = h.static := by rw [h3def]; rfl
  have hashingA : Hashing h3 d3 := by
    refine ⟨fun _ => chains3, fun one => ?_, fun a b _ => ?_⟩
    · have zero := inv.shape.slides.2 level
      change d.«matches» = 1 at one
      rw [zero] at one; cases one
    · rcases noRoll with e | e
      · exact absurd e a
      · exact absurd e b
  have buffers3 : StreamBuffers h3 r := by
    have mid := state_write_buffers (d' := ds0) inv.good buffers ⟨rfl, rfl, rfl, rfl⟩ good0
    rw [h3def]; rw [h3def] at good3
    exact private_write_buffers good0 mid trees0.base.pbuf ⟨rfl, rfl, rfl, rfl⟩ good3
  have distOk : ∀ s ∈ xs ++ [⟨(1 : UInt32).toNat, (ml - MIN_MATCH_u).toNat⟩], s.distance ≤ d3.w_size.toNat - 262 := by
    intro s mem
    rcases List.mem_append.mp mem with old | new
    · exact dist s old
    · simp only [List.mem_singleton] at new
      subst new
      have := (slide_window_sizes inv.good).1
      change 1 ≤ d.w_size.toNat - 262
      omega
  have shape := inv.shape
  have span := shape.blockSpan level
  refine ⟨b, buf', h3, ?_, good3, laEq3, ssEq3, buffers3, fun full => ?_, fun flag => ?_⟩
  · have e0 : setD h ds { d with match_length := ml } = setD h ds ds0 := rfl
    rw [e0, bind_app, tallyRun]
    simp only [bind_app, write]
    rfl
  · refine ⟨xs ++ [⟨(1 : UInt32).toNat, (ml - MIN_MATCH_u).toNat⟩], ⟨good3, inv.alloc,
      by unfold LibraryGlobals; rw [staticEq]; exact inv.globals, trees3, ledger3,
      ⟨inv.symbols.clear.bl, inv.symbols.clear.opt, inv.symbols.clear.fixed⟩, ?_, hashingA, pending,
      (block_start_low inv level : -(2 : Int) ^ 62 ≤ d.block_start.toInt), ?_, level, buffers3, out⟩⟩
    · refine flushed_shape ?_ ?_ ?_ shape.prevLength (by show (0 : UInt32).toNat ≤ 258; decide)
        shape.matchAvailable (fun zero => absurd zero level) ?_
        (fun large => absurd large (by show ¬ 3 ≤ (0 : UInt32).toNat; decide))
        (fun a b c e => ⟨by show (0 : UInt32).toNat ≤ 2; decide, (shape.fastLazy a b c e).2⟩)
        shape.highWater shape.lastFlush shape.trailer shape.biValid shape.cursor
        (by have := shape.symRoom; change 0 < d.sym_end.toNat; omega) shape.slides
      · change d3.strstart.toNat + d3.lookahead.toNat ≤ d.window_size.toNat
        rw [ssEq3, laEq3]; omega
      · change d.insert.toNat ≤ d3.strstart.toNat
        rw [ssEq3]; have := shape.insert; omega
      · intro large
        change 3 ≤ d3.lookahead.toNat at large
        rw [laEq3] at large
        exact shape.insertDone (by omega)
      · intro avail
        change 1 ≤ d3.strstart.toNat
        rw [ssEq3]; omega
    · change d.block_start.toInt ≤ (d3.strstart.toNat : Int)
      rw [ssEq3]; have := shape.blockStart; omega
  · have strictA := notFull flag
    have shapeA : Shape d3 := by
      refine ⟨?_, ?_, ?_, shape.prevLength, (by show (0 : UInt32).toNat ≤ 258; decide), shape.matchAvailable,
        ?_, ?_, ?_, ?_, (fun large => absurd large (by show ¬ 3 ≤ (0 : UInt32).toNat; decide)),
        (fun a b c e => ⟨by show (0 : UInt32).toNat ≤ 2; decide, (shape.fastLazy a b c e).2⟩),
        shape.highWater, shape.lastFlush, shape.trailer, shape.biValid, shape.cursor, strictA, shape.slides⟩
      · change d3.strstart.toNat + d3.lookahead.toNat ≤ d.window_size.toNat
        rw [ssEq3, laEq3]; omega
      · change d.insert.toNat ≤ d3.strstart.toNat
        rw [ssEq3]; have := shape.insert; omega
      · intro large
        change 3 ≤ d3.lookahead.toNat at large
        rw [laEq3] at large
        exact shape.insertDone (by omega)
      · change d.block_start.toInt ≤ (d3.strstart.toNat : Int)
        rw [ssEq3]; have := shape.blockStart; omega
      · intro _
        change (d3.strstart.toNat : Int) - d.block_start.toInt ≤
          258 * (d3.sym_next.toNat / 3 : Nat) + d.match_available.toInt
        have count3 : d3.sym_next.toNat = d.sym_next.toNat + 3 := count
        rw [ssEq3, count3]
        have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
        rw [div]
        push_cast
        omega
      · intro zero; exact absurd zero level
      · intro avail
        change 1 ≤ d3.strstart.toNat
        rw [ssEq3]; omega
    refine ⟨good3, inv.alloc, by unfold LibraryGlobals; rw [staticEq]; exact inv.globals, shapeA, hashingA,
      ⟨⟨_, ⟨b, buf', trees.base.pbuf, by rw [h3def]; simp, ledger3⟩, distOk⟩,
        ⟨inv.symbols.clear.bl, inv.symbols.clear.opt, inv.symbols.clear.fixed⟩, ?_⟩⟩
    intro b0 off pout _
    change d.pending_out = _ at pout
    rw [shape.cursor pending, trees.base.pbuf] at pout
    simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
    change off + d.pending.toNat ≤ d.lit_bufsize.toNat
    rw [← pout.2, pending]
    exact Nat.zero_le _


/-! ## `deflate_rle`: the body -/

/-- The run detection of `deflate_rle` (after `s->match_length = 0`). -/
def rleScan (s : DeflateStatePtr) : M Unit := do
  let d ← ldDeflateState s
  if d.lookahead ≥ MIN_MATCH_u && d.strstart > 0 then
    let mut scan ← psub (← padd d.window d.strstart.toNat) 1
    let prev : UInt32 := (← load8 scan).toUInt32
    scan ← padd scan 1
    let mut ok := prev == (← load8 scan).toUInt32
    if ok then
      scan ← padd scan 1
      ok := prev == (← load8 scan).toUInt32
    if ok then
      scan ← padd scan 1
      ok := prev == (← load8 scan).toUInt32
    if ok then
      let strend ← padd (← padd d.window d.strstart.toNat) MAX_MATCH_u.toNat
      let scan2 ← cdoWhile (fun x => pure x)
        (fun scan => do
          let mut scan := scan
          for _ in [0:8] do
            scan ← padd scan 1
            if prev != (← load8 scan).toUInt32 then return (false, scan)
          return (← Ptr.lt scan strend, scan))
        scan
      let diff ← Ptr.diff strend scan2
      let ml : UInt32 := MAX_MATCH_u - diff.toUInt64.toUInt32
      wr s (fun d => { d with match_length := ml })
      wr s (fun d => { d with match_length := if d.match_length > d.lookahead then d.lookahead else d.match_length })

/-- The emission of `deflate_rle`: a run or a literal, then the tail with the block flush. -/
def rleEmit (s : DeflateStatePtr) (st : LoopS) : M LoopS := do
  let d ← ldDeflateState s
  if d.match_length ≥ MIN_MATCH_u then
    let bflush ← tally_dist s 1 (d.match_length - MIN_MATCH_u)
    wr s (fun d =>
      { d with lookahead := d.lookahead - d.match_length, strstart := d.strstart + d.match_length, match_length := 0 })
    huffTail s st bflush
  else
    let c ← index8 d.window d.strstart.toNat
    let bflush ← tally_lit s c
    wr s (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
    huffTail s st bflush

theorem rle_body_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    deflate_rle_body s flush st = (do
      if (← rd s (·.lookahead)) ≤ MAX_MATCH_u then
        fill_window s
        let la ← rd s (·.lookahead)
        if la ≤ MAX_MATCH_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }
        if la == 0 then return { st with brk := true }
      wr s (fun d => { d with match_length := 0 })
      rleScan s
      rleEmit s st) := by
  unfold deflate_rle_body rleScan rleEmit huffTail
  simp only [Zlib.Deflate.Engine.Proofs.M_bind_assoc, Zlib.Deflate.Engine.Proofs.M_pure_bind, fill_ite_bind]
  rfl



theorem rle_length_eq (j : Nat) (hj : j ≤ 258) :
    (MAX_MATCH_u - (Int64.ofInt ((((258 : Nat) : Int) - ((j : Nat) : Int)))).toUInt64.toUInt32) = UInt32.ofNat j := by
  show (258 : UInt32) - _ = _
  have v : (((258 : Nat) : Int) - ((j : Nat) : Int)) = ((258 - j : Nat) : Int) := by omega
  rw [v, Int64.ofInt_eq_ofNat]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub_of_le]
  · simp
    omega
  · rw [UInt32.le_iff_toNat_le]
    simp
    omega

set_option maxHeartbeats 4000000 in
/-- **The run detection of `deflate_rle`.** With room for a run of 258 bytes after `strstart`, the
scan does not fault and only writes `match_length`: 0 when there is no run of 3, otherwise the run
length capped by the lookahead, between 3 and 258. -/
theorem rle_scan_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (noMatch : d.match_length = 0)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 258 < d.window_size.toNat) :
    ∃ ml : UInt32, rleScan (some (.tab ds)) h = .ok ((), setD h ds { d with match_length := ml }) ∧
      (ml = 0 ∨ (3 ≤ ml.toNat ∧ ml.toNat ≤ 258 ∧ ml.toNat ≤ d.lookahead.toNat)) := by
  obtain ⟨w, wa, win, get, size⟩ := window_block good
  have g : Space.get h (BRef.blk w) = some wa := by simpa using get
  have self : setD h ds { d with match_length := 0 } = h := by
    rw [← noMatch]; exact setD_self good.live.hs
  have ld : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
  by_cases go : (d.lookahead ≥ MIN_MATCH_u && d.strstart > 0) = true
  · have go' := go
    simp only [Bool.and_eq_true, decide_eq_true_eq] at go'
    obtain ⟨la3, ss0⟩ := go'
    have la3' : 3 ≤ d.lookahead.toNat := by
      have := UInt32.le_iff_toNat_le.mp la3
      have m3 : MIN_MATCH_u.toNat = 3 := rfl
      omega
    have ss1 : 1 ≤ d.strstart.toNat := by
      have := UInt32.lt_iff_toNat_lt.mp ss0
      have z0 : (0 : UInt32).toNat = 0 := rfl
      omega
    have pw : padd d.window d.strstart.toNat h = .ok (.ref (.blk w) d.strstart.toNat, h) := by
      rw [win]; simpa using padd_ok' (off := 0) (n := d.strstart.toNat) g (by omega)
    have ps : psub (.ref (.blk w) d.strstart.toNat : BPtr) 1 h = .ok (.ref (.blk w) (d.strstart.toNat - 1), h) :=
      psub_ok' g (by omega) (by omega)
    have l0 := load8_bfn get (i := d.strstart.toNat - 1) (by omega)
    have p1 : padd (.ref (.blk w) (d.strstart.toNat - 1) : BPtr) 1 h = .ok (.ref (.blk w) d.strstart.toNat, h) := by
      have := padd_ok' (off := d.strstart.toNat - 1) (n := 1) g (by omega)
      rw [show d.strstart.toNat - 1 + 1 = d.strstart.toNat by omega] at this; exact this
    have l1 := load8_bfn get (i := d.strstart.toNat) (by omega)
    have p2 : padd (.ref (.blk w) d.strstart.toNat : BPtr) 1 h = .ok (.ref (.blk w) (d.strstart.toNat + 1), h) :=
      padd_ok' g (by omega)
    have l2 := load8_bfn get (i := d.strstart.toNat + 1) (by omega)
    have p3 : padd (.ref (.blk w) (d.strstart.toNat + 1) : BPtr) 1 h = .ok (.ref (.blk w) (d.strstart.toNat + 2), h) :=
      padd_ok' g (by omega)
    have l3 := load8_bfn get (i := d.strstart.toNat + 2) (by omega)
    have pe : padd (.ref (.blk w) d.strstart.toNat : BPtr) MAX_MATCH_u.toNat h =
        .ok (.ref (.blk w) (d.strstart.toNat + 258), h) := padd_ok' g (by change _ + 258 ≤ _; omega)
    have beq : ∀ a b : UInt8, ((a.toUInt32 == b.toUInt32) = true ↔ a.toUInt32 = b.toUInt32) := by
      intro a b; simp
    by_cases e1 : (bfn wa (d.strstart.toNat - 1)).toUInt32 = (bfn wa d.strstart.toNat).toUInt32
    · have b1 : ((bfn wa (d.strstart.toNat - 1)).toUInt32 == (bfn wa d.strstart.toNat).toUInt32) = true :=
        (beq _ _).mpr e1
      by_cases e2 : (bfn wa (d.strstart.toNat - 1)).toUInt32 = (bfn wa (d.strstart.toNat + 1)).toUInt32
      · have b2 : ((bfn wa (d.strstart.toNat - 1)).toUInt32 == (bfn wa (d.strstart.toNat + 1)).toUInt32) = true :=
          (beq _ _).mpr e2
        by_cases e3 : (bfn wa (d.strstart.toNat - 1)).toUInt32 = (bfn wa (d.strstart.toNat + 2)).toUInt32
        · have b3 : ((bfn wa (d.strstart.toNat - 1)).toUInt32 == (bfn wa (d.strstart.toNat + 2)).toUInt32) = true :=
            (beq _ _).mpr e3
          obtain ⟨j, loopRun, j3, j258, _, _⟩ :=
            rle_scan_loop get d.strstart.toNat (bfn wa (d.strstart.toNat - 1)).toUInt32 (by omega)
          unfold rleCond at loopRun
          have df : Ptr.diff (.ref (.blk w) (d.strstart.toNat + 258) : BPtr) (.ref (.blk w) (d.strstart.toNat + j)) h =
              .ok (Int64.ofInt (((d.strstart.toNat + 258 : Nat) : Int) - ((d.strstart.toNat + j : Nat) : Int)), h) :=
            Ptr.diff_ok g (by omega) (by omega) (by omega)
          have mlEq : (MAX_MATCH_u - (Int64.ofInt (((d.strstart.toNat + 258 : Nat) : Int) -
              ((d.strstart.toNat + j : Nat) : Int))).toUInt64.toUInt32) = UInt32.ofNat j := by
            have v : (((d.strstart.toNat + 258 : Nat) : Int) - ((d.strstart.toNat + j : Nat) : Int)) =
                (((258 : Nat) : Int) - ((j : Nat) : Int)) := by omega
            rw [v]; exact rle_length_eq j j258
          let mlc : UInt32 := if UInt32.ofNat j > d.lookahead then d.lookahead else UInt32.ofNat j
          have jNat : (UInt32.ofNat j).toNat = j := by simp; omega
          refine ⟨mlc, ?_, Or.inr ?_⟩
          · unfold rleScan
            simp only [bind_app, ld, go, ite_true, M_ite_app, pw, ps, l0, p1, l1, b1, p2, l2, b2, p3, l3, b3, pe]
            rw [loopRun]
            simp only [bind_app, df, mlEq, wrD_eq, good.live.hs, setD_dstates_same, setD_setD]
            rfl
          · simp only [mlc]
            split
            · rename_i big
              rw [GT.gt, UInt32.lt_iff_toNat_lt, jNat] at big
              exact ⟨la3', by omega, Nat.le_refl _⟩
            · rename_i small
              rw [GT.gt, UInt32.lt_iff_toNat_lt, jNat] at small
              exact ⟨by rw [jNat]; omega, by rw [jNat]; omega, by rw [jNat]; omega⟩
        · have b3 : ((bfn wa (d.strstart.toNat - 1)).toUInt32 == (bfn wa (d.strstart.toNat + 2)).toUInt32) = false := by
            simpa using e3
          refine ⟨0, ?_, Or.inl rfl⟩
          rw [self]
          unfold rleScan
          simp only [bind_app, ld, go, ite_true, M_ite_app, pw, ps, l0, p1, l1, b1, p2, l2, b2, p3, l3, b3,
            Bool.false_eq_true, ite_false, pure_app]
      · have b2 : ((bfn wa (d.strstart.toNat - 1)).toUInt32 == (bfn wa (d.strstart.toNat + 1)).toUInt32) = false := by
          simpa using e2
        refine ⟨0, ?_, Or.inl rfl⟩
        rw [self]
        unfold rleScan
        simp only [bind_app, ld, go, ite_true, M_ite_app, pw, ps, l0, p1, l1, b1, p2, l2, b2,
          Bool.false_eq_true, ite_false, pure_app]
    · have b1 : ((bfn wa (d.strstart.toNat - 1)).toUInt32 == (bfn wa d.strstart.toNat).toUInt32) = false := by
        simpa using e1
      refine ⟨0, ?_, Or.inl rfl⟩
      rw [self]
      unfold rleScan
      simp only [bind_app, ld, go, ite_true, M_ite_app, pw, ps, l0, p1, l1, b1,
        Bool.false_eq_true, ite_false, pure_app]
  · refine ⟨0, ?_, Or.inl rfl⟩
    rw [self]
    have goF : (d.lookahead ≥ MIN_MATCH_u && d.strstart > 0) = false := by simpa using go
    unfold rleScan
    simp only [bind_app, ld, goF, Bool.false_eq_true, ite_false, M_ite_app]
    rfl


/-- The kind of a `deflate_rle` state. -/
def RleKind (d : DeflateState) : Prop := d.strategy.toInt = 3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **One emission of `deflate_rle`** from a loop head with lookahead and room for a run: the run
detection, then a run or a literal with the block flush on a full symbol buffer. -/
theorem rle_emit_iter (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head RleKind h r ds z d) (look : 1 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + 258 < d.window_size.toNat) (pending : d.pending = 0) (st : LoopS) :
    ∃ st' h',
      (do
        wr (some (.tab ds)) (fun d => { d with match_length := 0 })
        rleScan (some (.tab ds))
        rleEmit (some (.tab ds)) st) h = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head RleKind h' r ds z' d' ∧ d'.pending = 0 ∧
          z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head RleKind h' r ds z' d')) := by
  obtain ⟨wrRun, inv1⟩ := clear_match_inv head.inv
  have buffers1 := state_write_buffers (d' := { d with match_length := 0 }) head.inv.good head.buffers
    ⟨rfl, rfl, rfl, rfl⟩ inv1.good
  let d1 : DeflateState := { d with match_length := 0 }
  have kind1 : RleKind d1 := head.kind
  obtain ⟨ml, scanRun, mlCases⟩ := rle_scan_run (d := d1) inv1.good rfl inv1.shape.room room
  have state2 : (setD (setD h ds d1) ds { d1 with match_length := ml }).dstates ds = some { d1 with match_length := ml } := by
    simp
  have heap2 : setD (setD h ds d1) ds { d1 with match_length := ml } = setD h ds { d1 with match_length := ml } := by
    rw [setD_setD]
  -- the tail after the emission, for both flag values
  have tail : ∀ (h3 : Heap) (z3 : ZStream) (d3 : DeflateState) (bflush : Bool)
      (count : z.avail_in.toNat + d3.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat)
      (good3 : DGood h3 r ds z d3) (buffers3 : StreamBuffers h3 r) (z3eq : z3 = z)
      (kind3 : RleKind d3) (level3 : d3.level ≠ 0) (pending3 : d3.pending = 0)
      (full : bflush = true → ∃ pb buf xs, BlockReady h3 r ds z d3 pb buf xs)
      (notFull : bflush = false → DInv h3 r ds z d3),
      ∃ st' h', huffTail (some (.tab ds)) st bflush h3 = .ok (st', h') ∧ st'.brk = st.brk ∧
        ((st'.ret = st.ret ∧ ∃ z' d', Head RleKind h' r ds z' d' ∧ d'.pending = 0 ∧
            z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
         (st'.ret = some need_more ∧ ∃ z' d', Head RleKind h' r ds z' d')) := by
    intro h3 z3 d3 bflush count good3 buffers3 _ kind3 level3 pending3 full notFull
    cases bflush with
    | false =>
      refine ⟨{ st with bflush := false }, h3, by simp [huffTail], rfl,
        Or.inl ⟨rfl, z, d3, ⟨notFull rfl, buffers3, head.out, head.input, level3, kind3⟩, pending3, count⟩⟩
    | true =>
      obtain ⟨pb, buf, xs, ready⟩ := full rfl
      obtain ⟨opt, produced, after, z', result, flushRun, invA, buffersA, account, keeps, outA, idle, choice, _, _⟩ :=
        flush_block_macro safe ready false
      have flushRun' : FLUSH_BLOCK (some (.tab ds)) 0 h3 = .ok (opt, after) := flushRun
      have inputA : z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
        rw [keeps.availIn, keeps.nextIn]; exact head.input
      have headA : Head RleKind after r ds z' result :=
        ⟨invA, buffersA, outA, inputA, by rw [keeps.level]; exact level3,
          by unfold RleKind; rw [keeps.strategy]; exact kind3⟩
      rcases choice rfl with none' | more
      · subst none'
        refine ⟨{ st with bflush := true }, after, by simp [huffTail, bind_app, flushRun'], rfl,
          Or.inl ⟨rfl, z', result, headA, (idle rfl).1, ?_⟩⟩
        rw [keeps.availIn, keeps.lookahead]; exact count
      · subst more
        exact ⟨{ st with bflush := true, ret := some need_more }, after, by simp [huffTail, bind_app, flushRun'], rfl,
          Or.inr ⟨rfl, z', result, headA⟩⟩
  rcases mlCases with zero | ⟨lo, hi, within⟩
  · -- a literal
    subst zero
    have self2 : setD h ds { d1 with match_length := 0 } = setD h ds d1 := rfl
    obtain ⟨b, buf', c, h3, run, h3def, pbuf, good3, laEq, ssEq, buffers3, fullCase, notFullCase⟩ :=
      literal_step_inv inv1 head.level look (Or.inr head.kind) rfl pending buffers1 head.out
        (huffTail (some (.tab ds)) st)
    have ld1 : ldDeflateState (some (.tab ds)) (setD h ds d1) = .ok (d1, setD h ds d1) :=
      ldDeflateState_tab (setD_dstates_same h ds d1)
    have notBig : ¬ (d1.match_length ≥ MIN_MATCH_u) := by
      change ¬ ((0 : UInt32) ≥ 3); decide
    obtain ⟨st', h', tailRun, brk', cases⟩ := tail h3 z (literalStep d1 c) _
      (by rw [laEq]; change _ + (d.lookahead.toNat - 1) < _; omega) good3 buffers3 rfl head.kind head.level pending
      (fun flag => let ⟨xs, ready⟩ := fullCase flag; ⟨b, buf', xs, ready⟩) notFullCase
    have heapL : setD (setD h ds d1) ds { d1 with match_length := 0 } = setD h ds d1 := by
      rw [setD_setD]
    have emit : rleEmit (some (.tab ds)) st (setD h ds d1) =
        (do
          let d ← ldDeflateState (some (.tab ds))
          let c ← index8 d.window d.strstart.toNat
          let bflush ← tally_lit (some (.tab ds)) c
          wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
          huffTail (some (.tab ds)) st bflush) (setD h ds d1) := by
      unfold rleEmit
      simp only [bind_app, ld1, if_neg notBig]
    refine ⟨st', h', ?_, brk', cases⟩
    rw [bind_app, wrRun]
    simp only [bind_app, scanRun]
    have all := emit.trans (run.trans tailRun)
    rw [← heapL] at all
    exact all
  · -- a run
    have noRoll : d1.strategy.toInt = 2 ∨ d1.strategy.toInt = 3 := Or.inr head.kind
    obtain ⟨b, buf', h3, run, good3, laEq, ssEq, buffers3, fullCase, notFullCase⟩ :=
      run_step_inv inv1 head.level noRoll rfl pending buffers1 head.out ml lo hi within
        (huffTail (some (.tab ds)) st)
    obtain ⟨st', h', tailRun, brk', cases⟩ := tail h3 z (runStep d1 ml) _
      (by rw [laEq]; change _ + (d.lookahead.toNat - ml.toNat) < _; omega) good3 buffers3 rfl head.kind
      head.level pending (fun flag => let ⟨xs, ready⟩ := fullCase flag; ⟨b, buf', xs, ready⟩) notFullCase
    refine ⟨st', h', ?_, brk', cases⟩
    rw [bind_app, wrRun]
    simp only [bind_app, scanRun]
    have ld2 : ldDeflateState (some (.tab ds)) (setD (setD h ds d1) ds { d1 with match_length := ml }) =
        .ok ({ d1 with match_length := ml }, setD (setD h ds d1) ds { d1 with match_length := ml }) :=
      ldDeflateState_tab (setD_dstates_same _ ds _)
    have big : ({ d1 with match_length := ml } : DeflateState).match_length ≥ MIN_MATCH_u := by
      change MIN_MATCH_u ≤ ml
      rw [UInt32.le_iff_toNat_le]; exact lo
    have emit : rleEmit (some (.tab ds)) st (setD (setD h ds d1) ds { d1 with match_length := ml }) =
        (do
          let bflush ← tally_dist (some (.tab ds)) 1 (ml - MIN_MATCH_u)
          wr (some (.tab ds)) (fun d =>
            { d with lookahead := d.lookahead - d.match_length, strstart := d.strstart + d.match_length, match_length := 0 })
          huffTail (some (.tab ds)) st bflush) (setD (setD h ds d1) ds { d1 with match_length := ml }) := by
      unfold rleEmit
      simp only [bind_app, ld2, if_pos big]
    exact emit.trans (run.trans tailRun)


/-- The states of the `deflate_rle` loop. -/
def RleLoop (r : ZStreamRef) (ds : Nat) (st : LoopS) (h : Heap) : Prop :=
  ∃ z d, Head RleKind h r ds z d ∧
    ((st.brk = false ∧ st.ret = none ∧ d.pending = 0) ∨ st.ret = some need_more ∨
     (st.brk = true ∧ st.ret = none ∧ d.pending = 0 ∧ d.lookahead = 0 ∧ z.avail_in = 0))

/-- `fill_window` leaves room for a run of 258 bytes. -/
theorem fill_room {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    {roll : Prop} (post : FillPost roll h after r ds z z' d d') :
    d'.strstart.toNat + 262 ≤ d'.window_size.toNat := by
  have noSlide := post.noSlide
  have threshold := slide_threshold post.good
  rw [GE.ge, UInt32.le_iff_toNat_le, threshold] at noSlide
  have wsz := post.good.inv.wsz
  omega

set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_rle`** from a loop head. -/
theorem rle_body_step (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head RleKind h r ds z d) (pending : d.pending = 0) (flush : Int32)
    (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_rle_body (some (.tab ds)) flush st h = .ok (st', h') ∧ RleLoop r ds st' h' ∧
      loopMeasure r ds st' h' < loopMeasure r ds st h := by
  have measure0 := loop_measure_head head.inv.good.live.hz head.inv.good.live.hs brk ret
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head RleKind h1 r ds z1 d1 →
      d1.pending = 0 → 1 ≤ d1.lookahead.toNat → d1.strstart.toNat + 258 < d1.window_size.toNat →
      z1.avail_in.toNat + d1.lookahead.toNat ≤ z.avail_in.toNat + d.lookahead.toNat →
      ∃ st' h', (do
          wr (some (.tab ds)) (fun d => { d with match_length := 0 })
          rleScan (some (.tab ds))
          rleEmit (some (.tab ds)) st) h1 = .ok (st', h') ∧ RleLoop r ds st' h' ∧
        loopMeasure r ds st' h' < loopMeasure r ds st h := by
    intro h1 z1 d1 head1 pending1 look1 room1 sum
    obtain ⟨st', h', iterRun, brk', choice⟩ := rle_emit_iter safe head1 look1 room1 pending1 st
    refine ⟨st', h', iterRun, ?_, ?_⟩
    · rcases choice with ⟨retEq, z', d', head', pending', _⟩ | ⟨retEq, z', d', head'⟩
      · exact ⟨z', d', head', Or.inl ⟨brk'.trans brk, retEq.trans ret, pending'⟩⟩
      · exact ⟨z', d', head', Or.inr (Or.inl retEq)⟩
    · rcases choice with ⟨retEq, z', d', head', pending', count⟩ | ⟨retEq, _⟩
      · rw [loop_measure_head head'.inv.good.live.hz head'.inv.good.live.hs (brk'.trans brk) (retEq.trans ret),
          measure0]
        omega
      · rw [loop_measure_exit (Or.inr (by rw [retEq]; rfl)), measure0]; omega
  rw [rle_body_source]
  by_cases small : d.lookahead ≤ MAX_MATCH_u
  · have short : d.lookahead.toNat < 262 := by
      have := UInt32.le_iff_toNat_le.mp small; change _ ≤ 258 at this; omega
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨sLevel, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, sPending, _⟩ := post.same
    have head1 : Head RleKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold RleKind; rw [sStrategy]; exact k)
    have pending1 : d1.pending = 0 := sPending.trans pending
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    have consumed := post.consumed
    have room1 := fill_room post
    have fillRun' : fill_window (some (.tab ds)) h = .ok ((), after1) := fillRun
    by_cases stop1 : (d1.lookahead ≤ MAX_MATCH_u && flush == Z_NO_FLUSH) = true
    · refine ⟨{ st with ret := some need_more }, after1, ?_, ⟨z1, d1, head1, Or.inr (Or.inl rfl)⟩, ?_⟩
      · simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1]
        rfl
      · rw [loop_measure_exit (Or.inr rfl), measure0]; omega
    · have stop1F : (d1.lookahead ≤ MAX_MATCH_u && flush == Z_NO_FLUSH) = false := by simpa using stop1
      by_cases empty1 : d1.lookahead = 0
      · have empty1B : (d1.lookahead == 0) = true := by simp [empty1]
        have availZero : z1.avail_in = 0 := by
          rcases post.stopped with big | zero
          · rw [empty1] at big; exact absurd big (by decide)
          · exact zero
        refine ⟨{ st with brk := true }, after1, ?_,
          ⟨z1, d1, head1, Or.inr (Or.inr ⟨rfl, ret, pending1, empty1, availZero⟩)⟩, ?_⟩
        · simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
            Bool.false_eq_true, ite_false, empty1B]
          rfl
        · rw [loop_measure_exit (Or.inl rfl), measure0]; omega
      · have empty1B : (d1.lookahead == 0) = false := by simpa using empty1
        have look1 : 1 ≤ d1.lookahead.toNat := by
          have : d1.lookahead.toNat ≠ 0 := fun e => empty1 (UInt32.toNat_inj.mp e)
          omega
        obtain ⟨st', h', iterRun, loop', less⟩ := finishIter head1 pending1 look1 (by omega) (by omega)
        refine ⟨st', h', ?_, loop', less⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        exact iterRun
  · have smallF : (d.lookahead ≤ MAX_MATCH_u) = False := by simp [small]
    have big : 258 < d.lookahead.toNat := by
      have := small; rw [UInt32.le_iff_toNat_le] at this; change ¬ _ ≤ 258 at this; omega
    have room := head.inv.shape.room
    obtain ⟨st', h', iterRun, loop', less⟩ := finishIter head pending (by omega) (by omega) (Nat.le_refl _)
    refine ⟨st', h', ?_, loop', less⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    exact iterRun

/-- The `deflate_rle` loop ends in a `need_more` return or a `break` at the end of the input. -/
theorem rle_loop (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head RleKind h r ds z d) (pending : d.pending = 0) (flush : Int32) :
    ∃ st h', cwhile forever (deflate_rle_body (some (.tab ds)) flush) {} h = .ok (st, h') ∧
      RleLoop r ds st h' ∧ (st.brk = true ∨ st.ret.isSome = true) := by
  have start : RleLoop r ds {} h := ⟨z, d, head, Or.inl ⟨rfl, rfl, pending⟩⟩
  obtain ⟨st, h', run, loop, exit⟩ := cwhile_measure (cond := forever)
    (body := deflate_rle_body (some (.tab ds)) flush) (RleLoop r ds)
    (fun st h => RleLoop r ds st h ∧ (st.brk = true ∨ st.ret.isSome = true)) (loopMeasure r ds)
    (fun st h ⟨z, d, head, cases⟩ => by
      rcases cases with ⟨brk, ret, pending⟩ | ret | ⟨brk, ret, pending, _, _⟩
      · refine ⟨true, st, h, (by simp [forever, brk, ret]), (fun _ => ?_), (fun e => by cases e)⟩
        exact rle_body_step safe head pending flush st brk ret
      · refine ⟨false, st, h, (by simp [forever, ret]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z, d, head, Or.inr (Or.inl ret)⟩, Or.inr (by rw [ret]; rfl)⟩
      · refine ⟨false, st, h, (by simp [forever, brk]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z, d, head, Or.inr (Or.inr ⟨brk, ret, pending, by assumption, by assumption⟩)⟩, Or.inl brk⟩)
    start (loop_measure_bound r ds {} h)
  exact ⟨st, h', run, loop, exit⟩

/-- **`deflate_rle` keeps the invariant** (`Z_RLE` at a nonzero level), given the block flush of
batch C. -/
theorem rle_spec_of (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (flush : Int32)
    (level : d.level ≠ 0) (rle : d.strategy.toInt = 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r := by
  have head : Head RleKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, rle⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, cases⟩, exit⟩ := rle_loop safe head entry.pending flush
  rcases cases with ⟨brk, ret0, _⟩ | ret | ⟨brk, ret, pending1, _, _⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv, head1.buffers⟩
    simp [C.run, deflate_rle, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := clear_insert_head head1 id
    obtain ⟨bstate, after, z', d', tailRun, invA, buffersA⟩ := finish_tail_inv safe head2 pending1 flush
    refine ⟨bstate, after, z', d', ?_, invA, buffersA⟩
    simp only [C.run, deflate_rle, bind_app, loopRun, ret, wrRun]
    exact tailRun


/-! ## `deflate_fast`: the insertion loop after a short match -/

/-- The body of the insertion loop of `deflate_fast`. -/
def fastMatchBody (s : DeflateStatePtr) : UInt32 → M UInt32 := fun (_ : UInt32) => do
  wr s (fun d => { d with strstart := d.strstart + 1 })
  INSERT_STRING s (← rd s (·.strstart))

/-- The condition of the insertion loop of `deflate_fast`. -/
def fastMatchCond (s : DeflateStatePtr) : UInt32 → M (Bool × UInt32) := fun hh => do
  wr s (fun d => { d with match_length := d.match_length - 1 })
  pure ((← rd s (·.match_length)) != 0, hh)

def fastCountDown (d : DeflateState) : DeflateState := { d with match_length := d.match_length - 1 }

theorem fast_count_down_good {h : Heap} {r : ZStreamRef} {ds top : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top) :
    DGood (setD h ds (fastCountDown d)) r ds z (fastCountDown d) ∧
      HeapChains (setD h ds (fastCountDown d)) (fastCountDown d) top := by
  have inv : DStInv h ds (fastCountDown d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨good.setD' (d' := fastCountDown d) rfl good.live.status inv (by trkeep), ?_⟩
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩

set_option maxHeartbeats 1000000 in
/-- One step of the insertion loop: advance, insert, count down. -/
theorem fast_match_insert_step {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.match_length.toNat) (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + d.match_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ key candidate mid after,
      let result := fastCountDown { bumpStart d with ins_h := key }
      fastMatchBody (some (.tab ds)) hash_head h = .ok (candidate, mid) ∧
      fastMatchCond (some (.tab ds)) candidate mid = .ok ((result.match_length != 0, candidate), after) ∧
      DGood after r ds z result ∧ HeapChains after result (result.strstart.toNat + 1) ∧
      after.bytes w = some wa ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.match_length.toNat = d.match_length.toNat - 1 ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      after.libcErrorBorrow = h.libcErrorBorrow := by
  have bumped := bump_start_good good chains win get (by omega)
  let hb := setD h ds (bumpStart d)
  have getB : hb.bytes w = some wa := get
  have primed : InsHForm (bumpStart d).hash_shift (bumpStart d).hash_mask (bfn wa)
      (bumpStart d).strstart.toNat (bumpStart d).ins_h := by
    change InsHForm d.hash_shift d.hash_mask (bfn wa) (bumpStart d).strstart.toNat d.ins_h
    rw [bumped.1]
    exact form
  obtain ⟨key, candidate, mid, insert, goodI, chainsI, bytesI, formI, storageI⟩ := current_insert_storage
    bumped.2.1 bumped.2.2.1 win getB (by rw [bumped.1]; omega) bumped.2.2.2 lookahead primed
  let di := { bumpStart d with ins_h := key }
  let after := setD mid ds (fastCountDown di)
  have kept := fast_count_down_good goodI chainsI
  have ss : (fastCountDown di).strstart.toNat = d.strstart.toNat + 1 := bumped.1
  have count : (fastCountDown di).match_length.toNat = d.match_length.toNat - 1 := u32_sub_one positive
  have write : wr (some (.tab ds)) bumpStart h = .ok ((), hb) := by simp [wrD_eq, good.live.hs, hb]
  have body : fastMatchBody (some (.tab ds)) hash_head h = .ok (candidate, mid) := by
    unfold fastMatchBody
    change (do
      wr (some (.tab ds)) bumpStart
      INSERT_STRING (some (.tab ds)) (← rd (some (.tab ds)) (·.strstart))) h = _
    rw [bind_app, write]
    have stateB : hb.dstates ds = some (bumpStart d) := bumped.2.1.live.hs
    simp only [bind_app, rdD_eq, stateB]
    exact insert
  have condition : fastMatchCond (some (.tab ds)) candidate mid =
      .ok (((fastCountDown di).match_length != 0, candidate), after) := by
    unfold fastMatchCond
    change (do
      wr (some (.tab ds)) fastCountDown
      pure ((← rd (some (.tab ds)) (·.match_length)) != 0, candidate)) mid = _
    have put : wr (some (.tab ds)) fastCountDown mid = .ok ((), after) := by
      simp [wrD_eq, goodI.live.hs, after, di]
    rw [bind_app, put]
    have stateA : after.dstates ds = some (fastCountDown di) := kept.1.live.hs
    simp only [bind_app, rdD_eq, stateA]
    rfl
  have borrowI : mid.libcErrorBorrow = hb.libcErrorBorrow :=
    Zlib.Deflate.BorrowProofs.stable_INSERT_STRING _ _ _ _ _ insert
  refine ⟨key, candidate, mid, after, body, condition, kept.1, kept.2, ?_, ss, count, ?_, ?_,
    ((byte_frame_setD h ds (bumpStart d)).trans storageI).trans (byte_frame_setD mid ds (fastCountDown di)), ?_⟩
  · change mid.bytes w = some wa
    rw [bytesI]
    exact getB
  · exact formI
  · exact bytesI
  · exact borrowI

/-- Only the insertion key, current position and loop counter change. -/
def FastInsertFrame (before after : DeflateState) : Prop :=
  after = { before with strstart := after.strstart, ins_h := after.ins_h, match_length := after.match_length }

set_option maxHeartbeats 1000000 in
/-- **The insertion loop of `deflate_fast`** inserts each position of the match after the first:
it ends with a zero counter, `strstart` advanced by the counter, the chains through the current
position and the rolling hash ready for the next byte. -/
theorem fast_match_insert_loop {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.match_length.toNat) (countBound : d.match_length.toNat ≤ 258)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + d.match_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ candidate after result,
      cdoWhile (fastMatchBody (some (.tab ds))) (fastMatchCond (some (.tab ds))) hash_head h =
        .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result (result.strstart.toNat + 1) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.match_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat ∧ result.lookahead = d.lookahead ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h ∧
      FastInsertFrame d result ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      after.libcErrorBorrow = h.libcErrorBorrow := by
  let total := d.strstart.toNat + d.match_length.toNat
  let Inv : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state (state.strstart.toNat + 1) ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧
    1 ≤ state.match_length.toNat ∧ state.match_length.toNat ≤ 258 ∧
    3 ≤ state.lookahead.toNat ∧ state.lookahead = d.lookahead ∧
    state.strstart.toNat + state.match_length.toNat = total ∧
    state.strstart.toNat + state.match_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h ∧
    FastInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧
    heap.libcErrorBorrow = h.libcErrorBorrow
  let Q : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state (state.strstart.toNat + 1) ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧ state.match_length = 0 ∧
    state.strstart.toNat = total ∧ state.lookahead = d.lookahead ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h ∧
    FastInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧
    heap.libcErrorBorrow = h.libcErrorBorrow
  let rank : UInt32 → Heap → Nat := fun _ heap =>
    ((heap.dstates ds).map (fun state => state.match_length.toNat)).getD 0
  have step : ∀ hh heap, Inv hh heap → ∃ hh1 h1 c hh2 h2,
      fastMatchBody (some (.tab ds)) hh heap = .ok (hh1, h1) ∧
      fastMatchCond (some (.tab ds)) hh1 h1 = .ok ((c, hh2), h2) ∧
      (c = false → Q hh2 h2) ∧ (c = true → Inv hh2 h2 ∧ rank hh2 h2 < rank hh heap) := by
    intro hh heap inv
    obtain ⟨state, goodS, chainsS, winS, bytesS, posS, boundS, lookS, lookEq, sumS, roomS, formS, frameS,
      byteFrame, storageS, borrowS⟩ := inv
    obtain ⟨key, candidate, mid, after, bodyRun, condRun, goodA, chainsA, bytesA, startA, countA, formA,
      bytesEq, storageA, borrowA⟩ := fast_match_insert_step goodS chainsS winS bytesS posS lookS roomS formS hh
    let result := fastCountDown { bumpStart state with ins_h := key }
    have sumA : result.strstart.toNat + result.match_length.toNat = total := by rw [startA, countA]; omega
    have frameA : FastInsertFrame d result := by
      unfold FastInsertFrame at *
      change fastCountDown { bumpStart state with ins_h := key } = _
      rw [frameS]
      rfl
    refine ⟨candidate, mid, result.match_length != 0, candidate, after, bodyRun, condRun, ?_, ?_⟩
    · intro stop
      have zero : result.match_length = 0 := by simpa only [bne_eq_false_iff_eq] using stop
      refine ⟨result, goodA, chainsA, winS, bytesA, zero, ?_, lookEq, formA, frameA, bytesEq.trans byteFrame,
        storageS.trans storageA, borrowA.trans borrowS⟩
      have value : result.match_length.toNat = 0 := by rw [zero]; rfl
      omega
    · intro more
      have nonzero : result.match_length ≠ 0 := by simpa only [bne_iff_ne] using more
      have positiveA : 1 ≤ result.match_length.toNat := by
        have ne : result.match_length.toNat ≠ 0 := by intro eq; exact nonzero (UInt32.toNat_inj.mp eq)
        omega
      have roomA : result.strstart.toNat + result.match_length.toNat + 1 + result.lookahead.toNat ≤
          result.window_size.toNat := by
        change result.strstart.toNat + result.match_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat
        rw [startA, countA]
        omega
      refine ⟨⟨result, goodA, chainsA, winS, bytesA, positiveA, ?_, lookS, lookEq, sumA, roomA, formA, frameA,
        bytesEq.trans byteFrame, storageS.trans storageA, borrowA.trans borrowS⟩, ?_⟩
      · rw [countA]; omega
      · have stateA : after.dstates ds = some result := goodA.live.hs
        simp only [rank, goodS.live.hs, stateA, Option.map_some, Option.getD_some]
        rw [countA]
        omega
  have initial : Inv hash_head h :=
    ⟨d, good, chains, win, get, positive, countBound, lookahead, rfl, rfl, room, form, rfl, rfl,
      ByteFrame.refl h _, rfl⟩
  have fuelBound : rank hash_head h < fuel := by
    simp only [rank, good.live.hs, Option.map_some, Option.getD_some]
    change d.match_length.toNat < 18446744073709551616
    omega
  obtain ⟨candidate, after, run, result, post⟩ := do_heap_rank Inv rank Q step initial fuelBound
  exact ⟨candidate, after, result, run, post⟩


/-! ## `deflate_fast`: the body -/

/-- The search of `deflate_fast`: insert the string at `strstart` and look for a match. -/
def fastSearch (s : DeflateStatePtr) : M UInt32 := do
  let mut hash_head : UInt32 := 0
  if (← rd s (·.lookahead)) ≥ MIN_MATCH_u then
    hash_head ← INSERT_STRING s (← rd s (·.strstart))
  let d ← ldDeflateState s
  if hash_head != 0 && d.strstart - hash_head ≤ d.w_size - MIN_LOOKAHEAD_u then
    let ml ← longest_match s hash_head
    wr s (fun d => { d with match_length := ml })
  pure hash_head

/-- The tail of an iteration of `deflate_fast` and `deflate_slow`. -/
def lazyTail (s : DeflateStatePtr) (st : LoopS) (hash_head : UInt32) (bflush : Bool) : M LoopS := do
  if bflush then
    if let some r := (← FLUSH_BLOCK s 0) then return { st with hash_head, bflush, ret := some r }
  return { st with hash_head, bflush }

/-- The emission of `deflate_fast`: a match (with the insertions it allows) or a literal. -/
def fastEmit (s : DeflateStatePtr) (st : LoopS) (hash_head : UInt32) : M LoopS := do
  let d ← ldDeflateState s
  if d.match_length ≥ MIN_MATCH_u then
    let bflush ← tally_dist s (d.strstart - d.match_start) (d.match_length - MIN_MATCH_u)
    wr s (fun d => { d with lookahead := d.lookahead - d.match_length })
    let d ← ldDeflateState s
    if d.match_length ≤ d.max_lazy_match && d.lookahead ≥ MIN_MATCH_u then
      wr s (fun d => { d with match_length := d.match_length - 1 })
      let hh ← cdoWhile (fastMatchBody s) (fastMatchCond s) hash_head
      wr s (fun d => { d with strstart := d.strstart + 1 })
      lazyTail s st hh bflush
    else
      wr s (fun d => { d with strstart := d.strstart + d.match_length, match_length := 0 })
      let d ← ldDeflateState s
      let c ← index8 d.window d.strstart.toNat
      wr s (fun d => { d with ins_h := c.toUInt32 })
      UPDATE_HASH s (← index8 d.window (d.strstart + 1).toNat)
      lazyTail s st hash_head bflush
  else
    let c ← index8 d.window d.strstart.toNat
    let bflush ← tally_lit s c
    wr s (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
    lazyTail s st hash_head bflush

theorem fast_body_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    deflate_fast_body s flush st = (do
      if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then
        fill_window s
        let la ← rd s (·.lookahead)
        if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }
        if la == 0 then return { st with brk := true }
      let hash_head ← fastSearch s
      fastEmit s st hash_head) := by
  unfold deflate_fast_body fastSearch fastEmit lazyTail fastMatchBody fastMatchCond
  simp only [Zlib.Deflate.Engine.Proofs.M_bind_assoc, Zlib.Deflate.Engine.Proofs.M_pure_bind, fill_ite_bind]
  rfl


/-- The kind of a `deflate_fast` state: levels 1 to 3 with a strategy that hashes. -/
def FastKind (d : DeflateState) : Prop :=
  1 ≤ d.level.toInt ∧ d.level.toInt ≤ 3 ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3

/-- What the search of `deflate_fast` and `deflate_slow` leaves: only the engine scalars change,
the window and the symbols are untouched, the chains include `strstart` when there was lookahead
to insert it, and a match length of 3 or more names a real distance. -/
structure SearchOut (h h2 : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d d2 : DeflateState) : Prop where
  good : DGood h2 r ds z d2
  update : EngineUpdate d d2
  strstart : d2.strstart = d.strstart
  lookahead : d2.lookahead = d.lookahead
  insert : d2.insert = d.insert
  prevLength : d2.prev_length = d.prev_length
  available : d2.match_available = d.match_available
  bytes : h2.bytes = h.bytes
  static : h2.static = h.static
  frame : ByteFrame h h2 (fun i => i = ds)
  borrow : h2.libcErrorBorrow = h.libcErrorBorrow
  chains : HeapChains h2 d2 (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else d.strstart.toNat - d.insert.toNat)
  form : 3 ≤ d.lookahead.toNat → ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧
    InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d2.ins_h
  matchShape : d2.match_length.toNat ≤ 258
  matched : 3 ≤ d2.match_length.toNat → d2.match_length.toNat ≤ d.lookahead.toNat ∧
    1 ≤ (d2.strstart - d2.match_start).toNat ∧ (d2.strstart - d2.match_start).toNat ≤ d.w_size.toNat - 262

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The search of `deflate_fast`.** From a loop head with lookahead and matcher room. -/
theorem fast_search_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head FastKind h r ds z d) (look : 1 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ hh h2 d2, fastSearch (some (.tab ds)) h = .ok (hh, h2) ∧ SearchOut h h2 r ds z d d2 := by
  have inv := head.inv
  have good := inv.good
  have shape := inv.shape
  obtain ⟨k1, k3, s2, s3⟩ := head.kind
  have lazyBound := shape.fastLazy k1 k3 s2 s3
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by simp [rdD_eq, good.live.hs]
  have wsLo := (slide_window_sizes good).1
  by_cases ready : 3 ≤ d.lookahead.toNat
  · have readyU : d.lookahead ≥ MIN_MATCH_u := by
      rw [GE.ge, UInt32.le_iff_toNat_le]; exact ready
    have insertZero : d.insert = 0 := shape.insertDone ready
    obtain ⟨w, p, q, wa, pa, qa, env, H⟩ := heap_chains_environment good (inv.chains head.level)
    obtain ⟨w0, wa0, win0, get0, form⟩ := inv.hashing.rolling s2 s3 ready
    have wid : w0 = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans env.wbytes)
    subst wa0
    have zeroIns : d.insert.toNat = 0 := by rw [insertZero]; rfl
    obtain ⟨key, keyBound, hash, insertRun, goodI, chainsI, older, published, linked⟩ :=
      insert_published_three good env H (by omega) shape.room ready form
    let hi := insertedHeap h ds p q d pa qa key
    let di : DeflateState := { d with ins_h := key }
    let cand := (wfn qa key.toNat).toUInt32
    let pa' := pa.set! (d.strstart &&& d.w_mask).toNat (wfn qa key.toNat)
    let qa' := qa.set! key.toNat d.strstart.toUInt16
    have rdStart : rd (some (.tab ds)) (·.strstart) h = .ok (d.strstart, h) := by simp [rdD_eq, good.live.hs]
    have stateI : hi.dstates ds = some di := goodI.live.hs
    have ldI : ldDeflateState (some (.tab ds)) hi = .ok (di, hi) := ldDeflateState_tab stateI
    have getW : hi.bytes w = some wa := by simpa only [hi, insertedHeap] using env.wbytes
    have getP : hi.words p = some pa' := by simp [hi, pa', insertedHeap, env.hne.symm]
    have getQ : hi.words q = some qa' := by simp [hi, qa', insertedHeap]
    have actual := heap_chains_arrays chainsI env.win env.prevp env.headp getW getP getQ
    have frameI : ByteFrame h hi (fun i => i = ds) :=
      ⟨rfl, fun _ _ => rfl, fun i outside => by simp [hi, insertedHeap, upd_ne _ _ _ _ outside], fun _ _ => rfl⟩
    have nextForm : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key := by
      rw [hash, ← hkey_of_form env.params form]
      exact form_next form
    have readyB : (d.lookahead ≥ MIN_MATCH_u) = True := by simp [readyU]
    have prefixRun : ∀ {α : Type} (k : UInt32 → M α),
        (do
          let mut hash_head : UInt32 := 0
          if (← rd (some (.tab ds)) (·.lookahead)) ≥ MIN_MATCH_u then
            hash_head ← INSERT_STRING (some (.tab ds)) (← rd (some (.tab ds)) (·.strstart))
          k hash_head) h = k cand hi := by
      intro α k
      simp only [bind_app, rdLook, M_ite_app, readyU, decide_true, ite_true, rdStart, insertRun]
      rfl
    by_cases guard : (cand != 0 && di.strstart - cand ≤ di.w_size - MIN_LOOKAHEAD_u) = true
    · have conditions := guard
      simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at conditions
      have nz : cand ≠ 0 := conditions.1
      have nonzero : 1 ≤ cand.toNat := by
        have ne : cand.toNat ≠ 0 := by intro eq; exact nz (UInt32.toNat_inj.mp eq)
        omega
      have candLt : cand.toNat < d.strstart.toNat := older (by intro e; exact nz (UInt32.toNat_inj.mp e))
      have distance := machine_distance (d := di) candLt (by change 262 ≤ d.w_size.toNat; omega) conditions.2
      obtain ⟨len, ms, best, lmRun, lenEq, lower, upper, matching, goodL, chainsL⟩ :=
        longest_match_chains_room goodI chainsI env.win env.prevp env.headp getW getP getQ actual
          (by rw [hash]) keyBound published linked nonzero candLt distance shape.room room shape.prevLength
      let d2 : DeflateState := { di with match_start := ms, match_length := len }
      let h2 := setD (hAt hi ds di ms) ds d2
      have stateL : (hAt hi ds di ms).dstates ds = some { di with match_start := ms } := goodL.live.hs
      have write : wr (some (.tab ds)) (fun d => { d with match_length := len }) (hAt hi ds di ms) = .ok ((), h2) := by
        rw [wrD_eq, stateL]
      have good2 : DGood h2 r ds z d2 := engine_update_good goodL rfl
      have lenNat : len.toNat = lmResult best d.lookahead.toNat := by
        rw [lenEq]; unfold lmResult; split <;> simp <;> omega
      refine ⟨cand, h2, d2, ?_, ⟨good2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩⟩
      · unfold fastSearch
        rw [prefixRun]
        simp only [bind_app, ldI, M_ite_app, guard, ite_true]
        rw [show longest_match (some (.tab ds)) cand hi = .ok (len, hAt hi ds di ms) from lmRun]
        simp only [bind_app, write, pure_app]
      · have mid : ByteFrame hi (hAt hi ds di ms) (fun i => i = ds) :=
          ⟨rfl, fun _ _ => rfl, fun i outside => by simp [hAt, upd_ne _ _ _ _ outside], fun _ _ => rfl⟩
        exact (frameI.trans mid).trans (byte_frame_setD _ ds d2)
      · rw [if_pos ready]
        obtain ⟨w', p', q', wa', pa'', qa'', win', prev', head', hw', hp', hq', H'⟩ := chainsL
        exact ⟨w', p', q', wa', pa'', qa'', win', prev', head', by simpa [h2] using hw', by simpa [h2] using hp',
          by simpa [h2] using hq', H'⟩
      · intro _; exact ⟨w, wa, env.win, env.wbytes, nextForm⟩
      · change len.toNat ≤ 258
        rw [lenNat]; have := lmResult_le best d.lookahead.toNat; omega
      · intro large
        change 3 ≤ len.toNat at large
        rw [lenNat] at large ⊢
        have le := lmResult_le best d.lookahead.toNat
        refine ⟨le.2, ?_⟩
        have e1 : di.strstart = d.strstart := rfl
        have e2 : di.w_size = d.w_size := rfl
        have e3 : di.prev_length = d.prev_length := rfl
        rcases matching with ⟨same, _⟩ | ⟨_, msLt, msDist, _, _⟩
        · have pl := lazyBound.2; rw [e3] at same; omega
        · rw [e1] at msLt msDist
          rw [e2] at msDist
          change 1 ≤ (d.strstart - ms).toNat ∧ (d.strstart - ms).toNat ≤ d.w_size.toNat - 262
          rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]
          omega
    · have guardF : (cand != 0 && di.strstart - cand ≤ di.w_size - MIN_LOOKAHEAD_u) = false := by simpa using guard
      refine ⟨cand, hi, di, ?_, ⟨goodI, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, frameI, rfl, ?_, ?_, ?_, ?_⟩⟩
      · unfold fastSearch
        rw [prefixRun]
        simp only [bind_app, ldI, M_ite_app, guardF, Bool.false_eq_true, ite_false, pure_app]
      · rw [if_pos ready]; exact chainsI
      · intro _; exact ⟨w, wa, env.win, env.wbytes, nextForm⟩
      · exact shape.matchLength
      · intro large
        have := lazyBound.1
        change 3 ≤ d.match_length.toNat at large
        omega
  · have notReady : (d.lookahead ≥ MIN_MATCH_u) = False := by
      simp only [GE.ge, UInt32.le_iff_toNat_le, eq_iff_iff, iff_false]
      change ¬ 3 ≤ d.lookahead.toNat; exact ready
    have ld0 : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab good.live.hs
    refine ⟨0, h, d, ?_, ⟨good, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ByteFrame.refl h _, rfl, ?_, ?_,
      shape.matchLength, ?_⟩⟩
    · unfold fastSearch
      simp only [bind_app, rdLook, M_ite_app, notReady, ite_false, pure_app, ld0]
      rfl
    · rw [if_neg ready]; exact inv.chains head.level
    · intro r3; exact absurd r3 ready
    · intro large
      have := lazyBound.1
      omega


/-! ## `deflate_fast`: the emission -/

/-- The tail of an emission: no flush, or a block flush that either continues or returns
`need_more`. -/
theorem lazy_tail_step (safe : FlushSafe) {kind : DeflateState → Prop}
    (kindKeep : ∀ d d' : DeflateState, d'.strategy = d.strategy → d'.level = d.level → kind d → kind d')
    {h3 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d3 : DeflateState} (st : LoopS) (hh : UInt32)
    (bflush : Bool) (buffers3 : StreamBuffers h3 r) (out : z.next_out ≠ .null)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level3 : d3.level ≠ 0) (kind3 : kind d3)
    (pending3 : d3.pending = 0)
    (full : bflush = true → ∃ pb buf xs, BlockReady h3 r ds z d3 pb buf xs)
    (notFull : bflush = false → DInv h3 r ds z d3) :
    ∃ st' h', lazyTail (some (.tab ds)) st hh bflush h3 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head kind h' r ds z' d' ∧ d'.pending = 0 ∧
          z'.avail_in = z.avail_in ∧ d'.lookahead = d3.lookahead) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head kind h' r ds z' d')) := by
  cases bflush with
  | false =>
    exact ⟨{ st with hash_head := hh, bflush := false }, h3, by simp [lazyTail], rfl,
      Or.inl ⟨rfl, z, d3, ⟨notFull rfl, buffers3, out, input, level3, kind3⟩, pending3, rfl, rfl⟩⟩
  | true =>
    obtain ⟨pb, buf, xs, ready⟩ := full rfl
    obtain ⟨opt, produced, after, z', result, flushRun, invA, buffersA, account, keeps, outA, idle, choice, _, _⟩ :=
      flush_block_macro safe ready false
    have flushRun' : FLUSH_BLOCK (some (.tab ds)) 0 h3 = .ok (opt, after) := flushRun
    have inputA : z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
      rw [keeps.availIn, keeps.nextIn]; exact input
    have headA : Head kind after r ds z' result :=
      ⟨invA, buffersA, outA, inputA, by rw [keeps.level]; exact level3,
        kindKeep d3 result keeps.strategy keeps.level kind3⟩
    rcases choice rfl with none' | more
    · subst none'
      exact ⟨{ st with hash_head := hh, bflush := true }, after, by simp [lazyTail, bind_app, flushRun'], rfl,
        Or.inl ⟨rfl, z', result, headA, (idle rfl).1, keeps.availIn, keeps.lookahead⟩⟩
    · subst more
      exact ⟨{ st with hash_head := hh, bflush := true, ret := some need_more }, after,
        by simp [lazyTail, bind_app, flushRun'], rfl, Or.inr ⟨rfl, z', result, headA⟩⟩

theorem fast_kind_keep : ∀ d d' : DeflateState, d'.strategy = d.strategy → d'.level = d.level →
    FastKind d → FastKind d' := by
  intro d d' es el k
  unfold FastKind at *
  rw [es, el]; exact k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The literal emission of `deflate_fast`** after a search that found no match of 3. -/
theorem fast_literal_emit (safe : FlushSafe) {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head FastKind h r ds z d) (pending : d.pending = 0)
    (look : 1 ≤ d.lookahead.toNat) (search : SearchOut h h2 r ds z d d2)
    (small : d2.match_length.toNat < 3) (st : LoopS) (hh : UInt32) :
    ∃ st' h', fastEmit (some (.tab ds)) st hh h2 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head FastKind h' r ds z' d' ∧ d'.pending = 0 ∧
          z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head FastKind h' r ds z' d')) := by
  have inv := head.inv
  have shape := inv.shape
  have upd := search.update
  -- the fields of d2 that the literal reads
  have eWin : d2.window = d.window := by rw [upd]
  have eSym : d2.sym_next = d.sym_next := by rw [upd]
  have eEnd : d2.sym_end = d.sym_end := by rw [upd]
  have eWs : d2.window_size = d.window_size := by rw [upd]
  have eW : d2.w_size = d.w_size := by rw [upd]
  have eSs := search.strstart
  have eLa := search.lookahead
  have eIns := search.insert
  have buffers2 : StreamBuffers h2 r := by
    obtain ⟨win, prev, hd, pb⟩ : d2.window = d.window ∧ d2.prev = d.prev ∧ d2.head = d.head ∧
        d2.pending_buf = d.pending_buf := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz search.good.live.hz head.buffers search.frame
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good search.good win prev hd pb) (stream_accounting_self z) search.borrow
  have recorded2 : ∃ xs, Recorded h2 d2 xs ∧ ∀ s ∈ xs, s.distance ≤ d2.w_size.toNat - 262 := by
    obtain ⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩ := inv.symbols.recorded
    refine ⟨xs, ⟨b, a, by rw [upd]; exact pbuf, by rw [search.bytes]; exact get, ?_⟩, by rw [eW]; exact dist⟩
    rw [upd]; exact ledger.keep rfl rfl rfl rfl
  have room2 : d2.strstart.toNat + d2.lookahead.toNat ≤ d2.window_size.toNat := by
    rw [eSs, eLa, eWs]; exact shape.room
  have strict2 : d2.sym_next.toNat < d2.sym_end.toNat := by rw [eSym, eEnd]; exact shape.symRoom
  have look2 : 1 ≤ d2.lookahead.toNat := by rw [eLa]; exact look
  obtain ⟨b, buf, buf', xs, c, h3, run, h3def, trees, ledger, dist, bufEq, good3, trees3, ledger3, chains3,
    count, ssEq, laEq, notFull⟩ := literal_step_core search.good recorded2 room2 strict2 search.chains look2
      (lazyTail (some (.tab ds)) st hh)
  have ld2 : ldDeflateState (some (.tab ds)) h2 = .ok (d2, h2) := ldDeflateState_tab search.good.live.hs
  have notBig : ¬ (d2.match_length ≥ MIN_MATCH_u) := by
    rw [GE.ge, UInt32.le_iff_toNat_le]; change ¬ 3 ≤ _; omega
  have emit : fastEmit (some (.tab ds)) st hh h2 = lazyTail (some (.tab ds)) st hh (d2.sym_next + 3 == d2.sym_end) h3 := by
    have := run
    simp only [bind_app, ld2] at this
    unfold fastEmit
    simp only [bind_app, ld2, if_neg notBig]
    exact this
  let d3 := literalStep d2 c
  have staticEq : h3.static = h.static := by rw [h3def]; exact search.static
  obtain ⟨w, wa, win, getW, _⟩ := window_block inv.good
  have pbuf := trees.base.pbuf
  have wb : w ≠ b := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have be : b0 = b := by
      rw [show d2.pending_buf = d.pending_buf by rw [upd]] at pbuf
      simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w0 b0; exact blocks.wb
  have getW3 : h3.bytes w = some wa := by
    rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ wb, search.bytes, getW]
  have ss3 : d3.strstart.toNat = d.strstart.toNat + 1 := by rw [ssEq, eSs]
  have la3 : d3.lookahead.toNat = d.lookahead.toNat - 1 := by rw [laEq, eLa]
  have chainsA : Chains h3 d3 := by
    unfold Chains
    change HeapChains h3 d3 (d3.strstart.toNat - d2.insert.toNat)
    rw [ss3, eIns]
    by_cases ready : 3 ≤ d.lookahead.toNat
    · rw [if_pos ready] at chains3
      have zero : d.insert = 0 := shape.insertDone ready
      have z0 : d.insert.toNat = 0 := by rw [zero]; rfl
      rw [z0, Nat.sub_zero]; exact chains3
    · rw [if_neg ready] at chains3
      exact heap_chains_raise chains3 (by omega)
  have kind := head.kind
  have hashingA : Hashing h3 d3 := by
    refine ⟨fun _ => chainsA, fun one => ?_, fun _ _ large => ?_⟩
    · have zero := shape.slides.2 head.level
      change d2.«matches» = 1 at one
      rw [show d2.«matches» = d.«matches» by rw [upd], zero] at one; cases one
    · change 3 ≤ d3.lookahead.toNat at large
      rw [la3] at large
      obtain ⟨w0, wa0, win0, get0, form⟩ := search.form (by omega)
      have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
      subst w0
      have aid : wa0 = wa := Option.some.inj (get0.symm.trans getW)
      subst aid
      refine ⟨w, wa0, by change d2.window = _; rw [eWin]; exact win, getW3, ?_⟩
      change InsHForm d2.hash_shift d2.hash_mask (bfn wa0) d3.strstart.toNat d2.ins_h
      rw [ss3, show d2.hash_shift = d.hash_shift by rw [upd], show d2.hash_mask = d.hash_mask by rw [upd]]
      exact form
  have span := shape.blockSpan head.level
  have ml2 : d2.match_length.toNat ≤ 2 := by omega
  have mlEq : d3.match_length = d2.match_length := rfl
  have shapeCore : ∀ (sr : d3.sym_next.toNat < d3.sym_end.toNat ∨ True),
      d3.strstart.toNat + d3.lookahead.toNat ≤ d3.window_size.toNat ∧
      d3.insert.toNat ≤ d3.strstart.toNat ∧ (3 ≤ d3.lookahead.toNat → d3.insert = 0) ∧
      d3.block_start.toInt ≤ d3.strstart.toNat ∧
      (d3.match_available ≠ 0 → 1 ≤ d3.strstart.toNat) := by
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [ss3, la3]; change _ ≤ d2.window_size.toNat; rw [eWs]; have := shape.room; omega
    · rw [ss3]; change d2.insert.toNat ≤ _; rw [eIns]; have := shape.insert; omega
    · intro large; rw [la3] at large; change d2.insert = 0; rw [eIns]; exact shape.insertDone (by omega)
    · rw [ss3]; change d2.block_start.toInt ≤ _; rw [show d2.block_start = d.block_start by rw [upd]]
      have := shape.blockStart; omega
    · intro _; rw [ss3]; omega
  have ePl : d2.prev_length = d.prev_length := search.prevLength
  have eMa : d2.match_available = d.match_available := search.available
  have eBs : d2.block_start = d.block_start := by rw [upd]
  have eLv : d2.level = d.level := by rw [upd]
  have eSt : d2.strategy = d.strategy := by rw [upd]
  have eHw : d2.high_water = d.high_water := by rw [upd]
  have eLf : d2.last_flush = d.last_flush := by rw [upd]
  have eWr : d2.wrap = d.wrap := by rw [upd]
  have eStat : d2.status = d.status := by rw [upd]
  have eBv : d2.bi_valid = d.bi_valid := by rw [upd]
  have ePd : d2.pending = d.pending := by rw [upd]
  have ePo : d2.pending_out = d.pending_out := by rw [upd]
  have ePb : d2.pending_buf = d.pending_buf := by rw [upd]
  have eMt : d2.«matches» = d.«matches» := by rw [upd]
  have eLit : d2.lit_bufsize = d.lit_bufsize := by rw [upd]
  have eBl : d2.bl_tree = d.bl_tree := by rw [upd]
  have eOpt : d2.opt_len = d.opt_len := by rw [upd]
  have eStc : d2.static_len = d.static_len := by rw [upd]
  have lazyB := shape.fastLazy kind.1 kind.2.1 kind.2.2.1 kind.2.2.2
  obtain ⟨cRoom, cIns, cDone, cStart, cAvail⟩ := shapeCore (Or.inr trivial)
  have pendingMatch3 : 3 ≤ d3.match_length.toNat →
      1 ≤ (d3.strstart - 1 - d3.match_start).toNat ∧
      (d3.strstart - 1 - d3.match_start).toNat ≤ d3.w_size.toNat - 262 ∧
      d3.match_length.toNat ≤ d3.lookahead.toNat + 1 := by
    intro large; change 3 ≤ d2.match_length.toNat at large; omega
  have fast3 : 1 ≤ d3.level.toInt → d3.level.toInt ≤ 3 → d3.strategy.toInt ≠ 2 → d3.strategy.toInt ≠ 3 →
      d3.match_length.toNat ≤ 2 ∧ d3.prev_length.toNat ≤ 2 := by
    intro _ _ _ _
    exact ⟨ml2, by change d2.prev_length.toNat ≤ 2; rw [ePl]; exact lazyB.2⟩
  have biValid3 : d3.bi_valid.toInt ≤ 7 := by change d2.bi_valid.toInt ≤ 7; rw [eBv]; exact shape.biValid
  have cursor3 : d3.pending = 0 → d3.pending_out = d3.pending_buf := by
    change d2.pending = 0 → d2.pending_out = d2.pending_buf; rw [ePd, ePo, ePb]; exact shape.cursor
  have slides3 : d3.«matches».toNat ≤ 2 ∧ (d3.level ≠ 0 → d3.«matches» = 0) := by
    change d2.«matches».toNat ≤ 2 ∧ (d2.level ≠ 0 → d2.«matches» = 0); rw [eMt, eLv]; exact shape.slides
  have hw3 : d3.high_water.toNat ≤ d3.window_size.toNat := by
    change d2.high_water.toNat ≤ d2.window_size.toNat; rw [eHw, eWs]; exact shape.highWater
  have lf3 : -2 ≤ d3.last_flush.toInt ∧ d3.last_flush.toInt ≤ 5 := by
    change -2 ≤ d2.last_flush.toInt ∧ d2.last_flush.toInt ≤ 5; rw [eLf]; exact shape.lastFlush
  have tr3 : d3.wrap.toInt < 0 → d3.status = FINISH_STATE := by
    change d2.wrap.toInt < 0 → d2.status = FINISH_STATE; rw [eWr, eStat]; exact shape.trailer
  have ma3 : d3.match_available = 0 ∨ d3.match_available = 1 := by
    change d2.match_available = 0 ∨ d2.match_available = 1; rw [eMa]; exact shape.matchAvailable
  have pl3 : d3.prev_length.toNat ≤ 258 := by change d2.prev_length.toNat ≤ 258; rw [ePl]; exact shape.prevLength
  have level3 : d3.level ≠ 0 := by change d2.level ≠ 0; rw [eLv]; exact head.level
  have kind3 : FastKind d3 := by
    unfold FastKind; change 1 ≤ d2.level.toInt ∧ d2.level.toInt ≤ 3 ∧ d2.strategy.toInt ≠ 2 ∧ d2.strategy.toInt ≠ 3
    rw [eLv, eSt]; exact kind
  have pending3 : d3.pending = 0 := by change d2.pending = 0; rw [ePd]; exact pending
  have globals3 : LibraryGlobals h3 := by unfold LibraryGlobals; rw [staticEq]; exact inv.globals
  have clear3 : BlockInit.BlockClear d3 := by
    have c := inv.symbols.clear
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · change d2.bl_tree[k]!.fc = 0; rw [eBl]; exact c.bl k hk
    · change d2.opt_len = 0; rw [eOpt]; exact c.opt
    · change d2.static_len = 0; rw [eStc]; exact c.fixed
  have distA : ∀ s ∈ xs ++ [⟨0, c.toNat⟩], s.distance ≤ d3.w_size.toNat - 262 := by
    intro s mem
    rcases List.mem_append.mp mem with old | new
    · exact dist s old
    · simp only [List.mem_singleton] at new; subst new; exact Nat.zero_le _
  have getB3 : h3.bytes b = some buf' := by rw [h3def]; simp
  have blockLow : -(2 : Int) ^ 62 ≤ d3.block_start.toInt := by
    change -(2 : Int) ^ 62 ≤ d2.block_start.toInt; rw [eBs]; exact block_start_low inv head.level
  have out := head.out
  have input := head.input
  obtain ⟨st', h', tailRun, brk', cases⟩ := lazy_tail_step safe fast_kind_keep st hh (d2.sym_next + 3 == d2.sym_end)
    (by rw [h3def]; rw [h3def] at good3
        exact private_write_buffers search.good buffers2 pbuf ⟨rfl, rfl, rfl, rfl⟩ good3)
    out input level3 kind3 pending3
    (fun full => ⟨b, buf', xs ++ [⟨0, c.toNat⟩], ⟨good3, inv.alloc, globals3, trees3, ledger3, clear3,
      flushed_shape cRoom cIns cDone pl3 search.matchShape ma3 (fun zero => absurd zero level3) cAvail
        pendingMatch3 fast3 hw3 lf3 tr3 biValid3 cursor3
        (by change 0 < d2.sym_end.toNat; rw [eEnd]; have := shape.symRoom; omega) slides3,
      hashingA, pending3, blockLow, cStart, level3,
      (by rw [h3def]; rw [h3def] at good3
          exact private_write_buffers search.good buffers2 pbuf ⟨rfl, rfl, rfl, rfl⟩ good3), out⟩⟩)
    (fun flag => by
      have strictA := notFull flag
      refine ⟨good3, inv.alloc, globals3, ⟨cRoom, cIns, cDone, pl3, search.matchShape, ma3, cStart, ?_,
        (fun zero => absurd zero level3), cAvail, pendingMatch3, fast3, hw3, lf3, tr3, biValid3, cursor3, strictA,
        slides3⟩, hashingA, ⟨⟨_, ⟨b, buf', pbuf, getB3, ledger3⟩, distA⟩, clear3, ?_⟩⟩
      · intro _
        change ((d3.strstart.toNat : Int)) - d2.block_start.toInt ≤
          258 * (d3.sym_next.toNat / 3 : Nat) + d2.match_available.toInt
        rw [ss3, count, eBs, eMa, eSym]
        have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
        rw [div]
        push_cast
        omega
      · intro b0 off pout _
        change d2.pending_out = _ at pout
        rw [ePo, shape.cursor pending, ← ePb, pbuf] at pout
        simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
        change off + d2.pending.toNat ≤ d2.lit_bufsize.toNat
        rw [← pout.2, ePd, pending]
        exact Nat.zero_le _)
  refine ⟨st', h', emit.trans tailRun, brk', ?_⟩
  rcases cases with ⟨retEq, z', d', head', pending', availEq, laEq'⟩ | more
  · refine Or.inl ⟨retEq, z', d', head', pending', ?_⟩
    rw [availEq, laEq', la3]; omega
  · exact Or.inr more


/-- Lowering the valid-data end keeps the chains when every reached position is below `top`
and `top + 2` is within the new end. -/
theorem chains_lower_lim {h1 p1 : Nat → UInt16} {w : Nat → UInt8} {n hsh hm : UInt32}
    {ws top lim lim' : Nat} (hc : HashChains h1 p1 w n hsh hm ws top lim) (fits : top + 2 ≤ lim') :
    HashChains h1 p1 w n hsh hm ws top lim' := by
  refine ⟨fun k p hk hr hp ht => ?_⟩
  obtain ⟨a, _, c, e⟩ := hc.node k p hk hr hp ht
  exact ⟨a, by omega, c, e⟩

theorem heap_chains_lower {h : Heap} {d d' : DeflateState} {top : Nat} (chains : HeapChains h d top)
    (win : d'.window = d.window) (prev : d'.prev = d.prev) (head : d'.head = d.head)
    (size : d'.hash_size = d.hash_size) (shift : d'.hash_shift = d.hash_shift) (mask : d'.hash_mask = d.hash_mask)
    (wsize : d'.w_size = d.w_size)
    (fits : top + 2 ≤ d'.strstart.toNat + d'.lookahead.toNat) : HeapChains h d' top := by
  obtain ⟨w, p, q, wa, pa, qa, win0, prev0, head0, hw, hp, hq, H⟩ := chains
  refine ⟨w, p, q, wa, pa, qa, by rw [win]; exact win0, by rw [prev]; exact prev0, by rw [head]; exact head0,
    hw, hp, hq, ?_⟩
  rw [size, shift, mask, wsize]
  exact chains_lower_lim H fits

/-- The state after the match of a search is recorded and the lookahead lowered by its length. -/
def matchRecorded (d2 : DeflateState) : DeflateState :=
  let d3 := matchSymbolState d2 (d2.strstart - d2.match_start) (d2.match_length - MIN_MATCH_u)
  { d3 with lookahead := d3.lookahead - d3.match_length }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The match record of `deflate_fast`**: `_tr_tally_dist` of the match the search found, then
`s->lookahead -= s->match_length`. -/
theorem fast_match_record {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head FastKind h r ds z d) (search : SearchOut h h2 r ds z d d2)
    (big : 3 ≤ d2.match_length.toNat) {α : Type} (k : Bool → M α) :
    ∃ b buf buf' xs h4,
      (do
        let bflush ← tally_dist (some (.tab ds)) (d2.strstart - d2.match_start) (d2.match_length - MIN_MATCH_u)
        wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - d.match_length })
        k bflush) h2 = k (d2.sym_next + 3 == d2.sym_end) h4 ∧
      h4 = setD (Zlib.Trees.Proofs.Out.setB h2 b buf') ds (matchRecorded d2) ∧
      d2.pending_buf = .ref (.blk b) 0 ∧ h2.bytes b = some buf ∧
      DGood h4 r ds z (matchRecorded d2) ∧ TreesInvAt h4 ds (matchRecorded d2) b buf' ∧
      SymbolLedger buf' (matchRecorded d2)
        (xs ++ [⟨(d2.strstart - d2.match_start).toNat, (d2.match_length - MIN_MATCH_u).toNat⟩]) ∧
      (∀ s ∈ xs ++ [⟨(d2.strstart - d2.match_start).toNat, (d2.match_length - MIN_MATCH_u).toNat⟩],
        s.distance ≤ d.w_size.toNat - 262) ∧
      HeapChainsAt h4 (matchRecorded d2) (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat) ∧
      StreamBuffers h4 r ∧
      (matchRecorded d2).sym_next.toNat = d.sym_next.toNat + 3 ∧
      (matchRecorded d2).lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat ∧
      ((d2.sym_next + 3 == d2.sym_end) = false →
        (matchRecorded d2).sym_next.toNat < (matchRecorded d2).sym_end.toNat) ∧
      h4.static = h.static ∧ h4.libcErrorBorrow = h.libcErrorBorrow := by
  have inv := head.inv
  have shape := inv.shape
  have upd := search.update
  obtain ⟨within, dlo, dhi⟩ := search.matched big
  have eW : d2.w_size = d.w_size := by rw [upd]
  have eSym : d2.sym_next = d.sym_next := by rw [upd]
  have eEnd : d2.sym_end = d.sym_end := by rw [upd]
  have ready : 3 ≤ d.lookahead.toNat := by omega
  have buffers2 : StreamBuffers h2 r := by
    obtain ⟨win, prev, hd, pb⟩ : d2.window = d.window ∧ d2.prev = d.prev ∧ d2.head = d.head ∧
        d2.pending_buf = d.pending_buf := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz search.good.live.hz head.buffers search.frame
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good search.good win prev hd pb) (stream_accounting_self z) search.borrow
  obtain ⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩ := inv.symbols.recorded
  have pbuf2 : d2.pending_buf = .ref (.blk b) 0 := by rw [upd]; exact pbuf
  have get2 : h2.bytes b = some a := by rw [search.bytes]; exact get
  have ledger2 : SymbolLedger a d2 xs := by rw [upd]; exact ledger.keep rfl rfl rfl rfl
  have trees2 : TreesInvAt h2 ds d2 b a := trees_at_of_good search.good pbuf2 get2
  have strict2 : d2.sym_next.toNat < d2.sym_end.toNat := by rw [eSym, eEnd]; exact shape.symRoom
  have roomT := literal_room search.good.inv strict2
  let dist0 := d2.strstart - d2.match_start
  let len0 := d2.match_length - MIN_MATCH_u
  have dlo0 : 1 ≤ dist0.toNat := dlo
  have dhi0 : dist0.toNat ≤ d.w_size.toNat - 262 := dhi
  have lenNat : len0.toNat = d2.match_length.toNat - 3 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by change 3 ≤ _; exact big))
  have wsHi := (slide_window_sizes inv.good).2
  have tallyRun := tally_match_run trees2.base dist0 len0 dlo0 (by omega) roomT
  have ledger3 := ledger_match trees2.base ledger2 roomT dist0 len0 dlo0 (by omega)
    (by rw [lenNat]; have := search.matchShape; omega)
  let buf' := matchBytes a d2 dist0.toUInt16 len0.toUInt8
  let d3 := matchSymbolState d2 dist0 len0
  obtain ⟨h3, h3def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h2 b buf') ds d3 := ⟨_, rfl⟩
  have tallyRun' : tally_dist (some (.tab ds)) (d2.strstart - d2.match_start) (d2.match_length - MIN_MATCH_u) h2 =
      .ok (d2.sym_next + 3 == d2.sym_end, h3) := by
    rw [h3def]; exact tallyRun
  have good3 : DGood h3 r ds z d3 := by rw [h3def]; exact match_good_after search.good trees2 dist0 len0 roomT
  have chains2 : HeapChains h2 d2 (d.strstart.toNat + 1) := by
    have := search.chains; rw [if_pos ready] at this; exact this
  have chains3 : HeapChains h3 d3 (d.strstart.toNat + 1) := by
    rw [h3def]
    obtain ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, H⟩ :=
      pending_write_chains search.good chains2 trees2.base.pbuf buf' 0
    exact ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, H⟩
  let d4 := matchRecorded d2
  obtain ⟨h4, h4def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h2 b buf') ds d4 := ⟨_, rfl⟩
  have h4eq : h4 = setD h3 ds d4 := by rw [h4def, h3def, setD_setD]
  have good4 : DGood h4 r ds z d4 := by rw [h4eq]; exact engine_update_good good3 rfl
  have state3 : h3.dstates ds = some d3 := by rw [h3def]; simp
  have write : wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - d.match_length }) h3 = .ok ((), h4) := by
    rw [wrD_eq, state3, h4eq]; rfl
  have count : d4.sym_next.toNat = d.sym_next.toNat + 3 := by
    rw [← eSym]; exact literal_count trees2.base roomT 0
  have laEq : d4.lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat := by
    change (d2.lookahead - d2.match_length).toNat = _
    rw [search.lookahead, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]
  refine ⟨b, a, buf', xs, h4, ?_, h4def, pbuf2, get2, good4, trees_at_of_good good4 pbuf2 (by rw [h4def]; simp),
    ledger3.keep rfl rfl rfl rfl, ?_, ?_, ?_, count, laEq, ?_, ?_, ?_⟩
  · simp only [bind_app, tallyRun', write]
  · intro s mem
    rcases List.mem_append.mp mem with old | new
    · exact dist s old
    · simp only [List.mem_singleton] at new; subst new; exact dhi
  · have at3 : HeapChainsAt h3 d3 (d.strstart.toNat + 1) (d2.strstart.toNat + d2.lookahead.toNat) := chains3
    rw [search.strstart, search.lookahead] at at3
    exact at3.keep (by rw [h4eq]; rfl) (by rw [h4eq]; rfl) rfl rfl rfl rfl rfl rfl rfl
  · rw [h4def]; rw [h4def] at good4
    exact private_write_buffers search.good buffers2 pbuf2 ⟨rfl, rfl, rfl, rfl⟩ good4
  · intro flag
    exact literal_not_full trees2 0 roomT flag
  · rw [h4def]; exact search.static
  · rw [h4def]; exact search.borrow


/-- Facts about the state after the match record that both match branches use. -/
structure MatchBase (h h4 : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d d4 : DeflateState)
    (b : Nat) (buf' : Array UInt8) (xs : List Symbol) : Prop where
  good : DGood h4 r ds z d4
  ledger : SymbolLedger buf' d4 xs
  dist : ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262
  pbuf : d4.pending_buf = .ref (.blk b) 0
  bytesB : h4.bytes b = some buf'
  chainsAt : HeapChainsAt h4 d4 (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat)
  buffers : StreamBuffers h4 r
  static : h4.static = h.static


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **After a match of `deflate_fast`**: the state at `strstart + ml` with no pending match, the
chains through the new position and the rolling hash there is `DInv` again, or ready for the
block flush when the symbol buffer is full. -/
theorem fast_match_final {h h2 h4 h7 : Heap} {r : ZStreamRef} {ds b : Nat} {z : ZStream}
    {d d2 d7 : DeflateState} {buf' : Array UInt8} {xs : List Symbol}
    (head : Head FastKind h r ds z d) (pending : d.pending = 0) (search : SearchOut h h2 r ds z d d2)
    (big : 3 ≤ d2.match_length.toNat)
    (good4 : DGood h4 r ds z (matchRecorded d2)) (ledger4 : SymbolLedger buf' (matchRecorded d2) xs)
    (dist4 : ∀ s ∈ xs, s.distance ≤ d.w_size.toNat - 262)
    (pbuf : d2.pending_buf = .ref (.blk b) 0) (bytes4 : h4.bytes b = some buf')
    (buffers4 : StreamBuffers h4 r) (static4 : h4.static = h.static) (borrow4 : h4.libcErrorBorrow = h.libcErrorBorrow)
    (count4 : (matchRecorded d2).sym_next.toNat = d.sym_next.toNat + 3)
    (la4 : (matchRecorded d2).lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat)
    (good7 : DGood h7 r ds z d7)
    (fields : d7 = { matchRecorded d2 with strstart := d7.strstart, match_length := 0, ins_h := d7.ins_h })
    (ss7 : d7.strstart.toNat = d.strstart.toNat + d2.match_length.toNat)
    (bytes7 : h7.bytes = h4.bytes) (static7 : h7.static = h4.static)
    (borrow7 : h7.libcErrorBorrow = h4.libcErrorBorrow) (dstates7 : ∀ i, i ≠ ds → h7.dstates i = h4.dstates i)
    (ro7 : ∀ i, i ≠ ds → h7.ro i = h4.ro i)
    (chains7 : HeapChains h7 d7 (d.strstart.toNat + d2.match_length.toNat))
    (form7 : 3 ≤ d.lookahead.toNat - d2.match_length.toNat → ∃ w wa, d.window = .ref (.blk w) 0 ∧
      h7.bytes w = some wa ∧ InsHForm d.hash_shift d.hash_mask (bfn wa) d7.strstart.toNat d7.ins_h)
    (bflush : Bool) (flagEq : bflush = (d2.sym_next + 3 == d2.sym_end))
    (notFull4 : bflush = false → (matchRecorded d2).sym_next.toNat < (matchRecorded d2).sym_end.toNat) :
    StreamBuffers h7 r ∧ (bflush = true → ∃ pb buf xs, BlockReady h7 r ds z d7 pb buf xs) ∧
      (bflush = false → DInv h7 r ds z d7) ∧ d7.level ≠ 0 ∧ FastKind d7 ∧ d7.pending = 0 ∧
      d7.lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat := by
  have inv := head.inv
  have shape := inv.shape
  have upd := search.update
  have kind := head.kind
  have lazyB := shape.fastLazy kind.1 kind.2.1 kind.2.2.1 kind.2.2.2
  obtain ⟨within, dlo, dhi⟩ := search.matched big
  have ready : 3 ≤ d.lookahead.toNat := by omega
  have insertZero : d.insert = 0 := shape.insertDone ready
  have mlHi := search.matchShape
  -- every field of d7 other than the three is that of matchRecorded d2, hence of d
  have f : ∀ {β : Type} (g : DeflateState → β),
      (∀ x : DeflateState, g { x with strstart := d7.strstart, match_length := 0, ins_h := d7.ins_h } = g x) →
      g d7 = g (matchRecorded d2) := by
    intro β g hg; rw [fields, hg]
  have eLv : d7.level = d.level := by rw [f DeflateState.level (fun _ => rfl)]; change d2.level = _; rw [upd]
  have eSt : d7.strategy = d.strategy := by rw [f DeflateState.strategy (fun _ => rfl)]; change d2.strategy = _; rw [upd]
  have ePd : d7.pending = d.pending := by rw [f DeflateState.pending (fun _ => rfl)]; change d2.pending = _; rw [upd]
  have ePo : d7.pending_out = d.pending_out := by
    rw [f DeflateState.pending_out (fun _ => rfl)]; change d2.pending_out = _; rw [upd]
  have ePb : d7.pending_buf = d.pending_buf := by
    rw [f DeflateState.pending_buf (fun _ => rfl)]; change d2.pending_buf = _; rw [upd]
  have eLa : d7.lookahead = (matchRecorded d2).lookahead := f DeflateState.lookahead (fun _ => rfl)
  have eSym : d7.sym_next = (matchRecorded d2).sym_next := f DeflateState.sym_next (fun _ => rfl)
  have eEnd : d7.sym_end = d.sym_end := by rw [f DeflateState.sym_end (fun _ => rfl)]; change d2.sym_end = _; rw [upd]
  have eIns : d7.insert = d.insert := by
    rw [f DeflateState.insert (fun _ => rfl)]; change d2.insert = _; exact search.insert
  have ePl : d7.prev_length = d.prev_length := by
    rw [f DeflateState.prev_length (fun _ => rfl)]; change d2.prev_length = _; exact search.prevLength
  have eMa : d7.match_available = d.match_available := by
    rw [f DeflateState.match_available (fun _ => rfl)]; change d2.match_available = _; exact search.available
  have eBs : d7.block_start = d.block_start := by
    rw [f DeflateState.block_start (fun _ => rfl)]; change d2.block_start = _; rw [upd]
  have eWs : d7.window_size = d.window_size := by
    rw [f DeflateState.window_size (fun _ => rfl)]; change d2.window_size = _; rw [upd]
  have eW : d7.w_size = d.w_size := by rw [f DeflateState.w_size (fun _ => rfl)]; change d2.w_size = _; rw [upd]
  have eWin : d7.window = d.window := by rw [f DeflateState.window (fun _ => rfl)]; change d2.window = _; rw [upd]
  have eHw : d7.high_water = d.high_water := by
    rw [f DeflateState.high_water (fun _ => rfl)]; change d2.high_water = _; rw [upd]
  have eLf : d7.last_flush = d.last_flush := by
    rw [f DeflateState.last_flush (fun _ => rfl)]; change d2.last_flush = _; rw [upd]
  have eWr : d7.wrap = d.wrap := by rw [f DeflateState.wrap (fun _ => rfl)]; change d2.wrap = _; rw [upd]
  have eStat : d7.status = d.status := by rw [f DeflateState.status (fun _ => rfl)]; change d2.status = _; rw [upd]
  have eBv : d7.bi_valid = d.bi_valid := by rw [f DeflateState.bi_valid (fun _ => rfl)]; change d2.bi_valid = _; rw [upd]
  have eMt : d7.«matches» = d.«matches» := by rw [f DeflateState.«matches» (fun _ => rfl)]; change d2.«matches» = _; rw [upd]
  have eLit : d7.lit_bufsize = d.lit_bufsize := by
    rw [f DeflateState.lit_bufsize (fun _ => rfl)]; change d2.lit_bufsize = _; rw [upd]
  have eBl : d7.bl_tree = d.bl_tree := by rw [f DeflateState.bl_tree (fun _ => rfl)]; change d2.bl_tree = _; rw [upd]
  have eOpt : d7.opt_len = d.opt_len := by rw [f DeflateState.opt_len (fun _ => rfl)]; change d2.opt_len = _; rw [upd]
  have eStc : d7.static_len = d.static_len := by
    rw [f DeflateState.static_len (fun _ => rfl)]; change d2.static_len = _; rw [upd]
  have eHs : d7.hash_shift = d.hash_shift := by
    rw [f DeflateState.hash_shift (fun _ => rfl)]; change d2.hash_shift = _; rw [upd]
  have eHm : d7.hash_mask = d.hash_mask := by
    rw [f DeflateState.hash_mask (fun _ => rfl)]; change d2.hash_mask = _; rw [upd]
  have eMl : d7.match_length = 0 := by rw [fields]
  have la7 : d7.lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat := by rw [eLa]; exact la4
  have sym7 : d7.sym_next.toNat = d.sym_next.toNat + 3 := by rw [eSym]; exact count4
  have level7 : d7.level ≠ 0 := by rw [eLv]; exact head.level
  have kind7 : FastKind d7 := by unfold FastKind; rw [eLv, eSt]; exact kind
  have pending7 : d7.pending = 0 := by rw [ePd]; exact pending
  have buffers7 : StreamBuffers h7 r := by
    have frame : ByteFrame h4 h7 (fun i => i = ds) :=
      ⟨static7, fun i _ => by rw [bytes7], fun i out => dstates7 i out, fun i out => ro7 i out⟩
    obtain ⟨win, prev, hd, pb⟩ : d7.window = (matchRecorded d2).window ∧ d7.prev = (matchRecorded d2).prev ∧
        d7.head = (matchRecorded d2).head ∧ d7.pending_buf = (matchRecorded d2).pending_buf := by
      rw [fields]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read good4.live.hz good7.live.hz buffers4 frame
      (fun i mine => (stream_owned_deflate good4 i).mpr (Or.inl mine))
      (stream_owned_keys good4 good7 win prev hd pb) (stream_accounting_self z) borrow7
  have pbuf7 : d7.pending_buf = .ref (.blk b) 0 := by
    rw [ePb]; rw [show d2.pending_buf = d.pending_buf by rw [upd]] at pbuf; exact pbuf
  have getB7 : h7.bytes b = some buf' := by rw [bytes7]; exact bytes4
  have ledger7 : SymbolLedger buf' d7 xs := by
    rw [fields]; exact ledger4.keep rfl rfl rfl rfl
  have trees7 : TreesInvAt h7 ds d7 b buf' := trees_at_of_good good7 pbuf7 getB7
  have globals7 : LibraryGlobals h7 := by unfold LibraryGlobals; rw [static7, static4]; exact inv.globals
  have clear7 : BlockInit.BlockClear d7 := by
    have c := inv.symbols.clear
    exact ⟨fun k hk => by rw [eBl]; exact c.bl k hk, by rw [eOpt]; exact c.opt, by rw [eStc]; exact c.fixed⟩
  have chainsC : Chains h7 d7 := by
    unfold Chains; rw [eIns, ss7, insertZero]; exact chains7
  have hashing7 : Hashing h7 d7 := by
    refine ⟨fun _ => chainsC, fun one => ?_, fun _ _ large => ?_⟩
    · rw [eMt, shape.slides.2 head.level] at one; cases one
    · rw [la7] at large
      obtain ⟨w, wa, win, get, form⟩ := form7 large
      exact ⟨w, wa, by rw [eWin]; exact win, get, by rw [eHs, eHm]; exact form⟩
  have room7 : d7.strstart.toNat + d7.lookahead.toNat ≤ d7.window_size.toNat := by
    rw [ss7, la7, eWs]; have := shape.room; omega
  have ins7 : d7.insert.toNat ≤ d7.strstart.toNat := by rw [eIns, ss7]; have := shape.insert; omega
  have done7 : 3 ≤ d7.lookahead.toNat → d7.insert = 0 := fun _ => by rw [eIns]; exact insertZero
  have pl7 : d7.prev_length.toNat ≤ 258 := by rw [ePl]; exact shape.prevLength
  have ml7 : d7.match_length.toNat ≤ 258 := by rw [eMl]; decide
  have ma7 : d7.match_available = 0 ∨ d7.match_available = 1 := by rw [eMa]; exact shape.matchAvailable
  have bs7 : d7.block_start.toInt ≤ d7.strstart.toNat := by rw [eBs, ss7]; have := shape.blockStart; omega
  have av7 : d7.match_available ≠ 0 → 1 ≤ d7.strstart.toNat := fun _ => by rw [ss7]; omega
  have pm7 : 3 ≤ d7.match_length.toNat → 1 ≤ (d7.strstart - 1 - d7.match_start).toNat ∧
      (d7.strstart - 1 - d7.match_start).toNat ≤ d7.w_size.toNat - 262 ∧
      d7.match_length.toNat ≤ d7.lookahead.toNat + 1 := by
    intro large; rw [eMl] at large; exact absurd large (by decide)
  have fl7 : 1 ≤ d7.level.toInt → d7.level.toInt ≤ 3 → d7.strategy.toInt ≠ 2 → d7.strategy.toInt ≠ 3 →
      d7.match_length.toNat ≤ 2 ∧ d7.prev_length.toNat ≤ 2 := fun _ _ _ _ => ⟨by rw [eMl]; decide, by rw [ePl]; exact lazyB.2⟩
  have hw7 : d7.high_water.toNat ≤ d7.window_size.toNat := by rw [eHw, eWs]; exact shape.highWater
  have lf7 : -2 ≤ d7.last_flush.toInt ∧ d7.last_flush.toInt ≤ 5 := by rw [eLf]; exact shape.lastFlush
  have tr7 : d7.wrap.toInt < 0 → d7.status = FINISH_STATE := by rw [eWr, eStat]; exact shape.trailer
  have bv7 : d7.bi_valid.toInt ≤ 7 := by rw [eBv]; exact shape.biValid
  have cu7 : d7.pending = 0 → d7.pending_out = d7.pending_buf := by rw [ePd, ePo, ePb]; exact shape.cursor
  have sl7 : d7.«matches».toNat ≤ 2 ∧ (d7.level ≠ 0 → d7.«matches» = 0) := by rw [eMt, eLv]; exact shape.slides
  have blockLow : -(2 : Int) ^ 62 ≤ d7.block_start.toInt := by rw [eBs]; exact block_start_low inv head.level
  have distOk : ∀ s ∈ xs, s.distance ≤ d7.w_size.toNat - 262 := by rw [eW]; exact dist4
  refine ⟨buffers7, fun _ => ⟨b, buf', xs, ⟨good7, inv.alloc, globals7, trees7, ledger7, clear7,
    flushed_shape room7 ins7 done7 pl7 ml7 ma7 (fun zero => absurd zero level7) av7 pm7 fl7 hw7 lf7 tr7 bv7 cu7
      (by rw [eEnd]; have := shape.symRoom; omega) sl7, hashing7, pending7, blockLow, bs7, level7, buffers7,
    head.out⟩⟩, fun flag => ?_, level7, kind7, pending7, la7⟩
  have eEnd' : d7.sym_end = (matchRecorded d2).sym_end := f DeflateState.sym_end (fun _ => rfl)
  have strict : d7.sym_next.toNat < d7.sym_end.toNat := by rw [eSym, eEnd']; exact notFull4 flag
  refine ⟨good7, inv.alloc, globals7, ⟨room7, ins7, done7, pl7, ml7, ma7, bs7, ?_,
    (fun zero => absurd zero level7), av7, pm7, fl7, hw7, lf7, tr7, bv7, cu7, strict, sl7⟩, hashing7,
    ⟨⟨xs, ⟨b, buf', pbuf7, getB7, ledger7⟩, distOk⟩, clear7, ?_⟩⟩
  · intro _
    rw [ss7, sym7, eBs, eMa]
    have span := shape.blockSpan head.level
    have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
    rw [div]
    push_cast
    omega
  · intro b0 off pout _
    rw [ePo, shape.cursor pending, ← ePb, pbuf7] at pout
    simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
    rw [← pout.2, pending7]
    exact Nat.zero_le _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The match emission of `deflate_fast`** after a search that found a match of 3 or more. -/
theorem fast_match_emit (safe : FlushSafe) {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head FastKind h r ds z d) (pending : d.pending = 0)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (search : SearchOut h h2 r ds z d d2)
    (big : 3 ≤ d2.match_length.toNat) (st : LoopS) (hh : UInt32) :
    ∃ st' h', fastEmit (some (.tab ds)) st hh h2 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head FastKind h' r ds z' d' ∧ d'.pending = 0 ∧
          z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head FastKind h' r ds z' d')) := by
  have inv := head.inv
  have shape := inv.shape
  have upd := search.update
  have kind := head.kind
  have lazyB := shape.fastLazy kind.1 kind.2.1 kind.2.2.1 kind.2.2.2
  obtain ⟨within, dlo, dhi⟩ := search.matched big
  have ready : 3 ≤ d.lookahead.toNat := by omega
  have insertZero : d.insert = 0 := shape.insertDone ready
  have mlHi := search.matchShape
  obtain ⟨w, wa, win, getW, wsize⟩ := window_block inv.good
  have wsz := inv.good.inv.wsz
  have wsHi := (slide_window_sizes inv.good).2
  have ld2 : ldDeflateState (some (.tab ds)) h2 = .ok (d2, h2) := ldDeflateState_tab search.good.live.hs
  have bigU : d2.match_length ≥ MIN_MATCH_u := by rw [GE.ge, UInt32.le_iff_toNat_le]; exact big
  -- the continuation after the record
  let K : Bool → M LoopS := fun bflush => do
    let d ← ldDeflateState (some (.tab ds))
    if d.match_length ≤ d.max_lazy_match && d.lookahead ≥ MIN_MATCH_u then
      wr (some (.tab ds)) (fun d => { d with match_length := d.match_length - 1 })
      let hh ← cdoWhile (fastMatchBody (some (.tab ds))) (fastMatchCond (some (.tab ds))) hh
      wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + 1 })
      lazyTail (some (.tab ds)) st hh bflush
    else
      wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + d.match_length, match_length := 0 })
      let d ← ldDeflateState (some (.tab ds))
      let c ← index8 d.window d.strstart.toNat
      wr (some (.tab ds)) (fun d => { d with ins_h := c.toUInt32 })
      UPDATE_HASH (some (.tab ds)) (← index8 d.window (d.strstart + 1).toNat)
      lazyTail (some (.tab ds)) st hh bflush
  obtain ⟨b, buf, buf', xs, h4, recRun, h4def, pbuf2, get2, good4, trees4, ledger4, dist4, chainsAt4, buffers4,
    count4, la4, notFull4, static4, borrow4⟩ := fast_match_record head search big K
  have emit : fastEmit (some (.tab ds)) st hh h2 = K (d2.sym_next + 3 == d2.sym_end) h4 := by
    have := recRun
    unfold fastEmit
    simp only [bind_app, ld2, if_pos bigU]
    exact this
  let d4 := matchRecorded d2
  have upd4 : d4.strstart = d.strstart := by change d2.strstart = _; exact search.strstart
  have ss4 : d4.strstart.toNat = d.strstart.toNat := by rw [upd4]
  have ld4 : ldDeflateState (some (.tab ds)) h4 = .ok (d4, h4) := ldDeflateState_tab good4.live.hs
  have wb : w ≠ b := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have be : b0 = b := by
      rw [show d2.pending_buf = d.pending_buf by rw [upd]] at pbuf2
      simpa only [pbuf2, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w0 b0; exact blocks.wb
  have getW4 : h4.bytes w = some wa := by
    rw [h4def]; simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ wb, search.bytes, getW]
  have win4 : d4.window = .ref (.blk w) 0 := by change d2.window = _; rw [upd]; exact win
  have getB4 : h4.bytes b = some buf' := by rw [h4def]; simp
  have ml4 : d4.match_length = d2.match_length := rfl
  have hsh : HashParams d.hash_size d.hash_shift d.hash_mask := hash_parameters inv.good.inv
  have upd5 : ∀ {β : Type} (g : DeflateState → β), (∀ x : DeflateState, g (matchRecorded x) = g x) →
      g d4 = g d2 := fun g hg => hg d2
  have eHs4 : d4.hash_shift = d.hash_shift := by change d2.hash_shift = _; rw [upd]
  have eHm4 : d4.hash_mask = d.hash_mask := by change d2.hash_mask = _; rw [upd]
  have eWs4 : d4.window_size = d.window_size := by change d2.window_size = _; rw [upd]
  have eIns4 : d4.ins_h = d2.ins_h := rfl
  -- the rolling hash of the search, on the window of h4
  obtain ⟨w0, wa0, win0, get0, form2⟩ := search.form ready
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
  subst w0
  have aid : wa0 = wa := Option.some.inj (get0.symm.trans getW)
  subst aid
  -- the chains of the record, at the window arrays
  obtain ⟨w1, p1, q1, wa1, pa1, qa1, win1, prev1, head1, hw1, hp1, hq1, H1⟩ := chainsAt4
  have wid1 : w1 = w := by have e := win1.symm.trans win4; simpa using e
  subst wid1
  have aid1 : wa1 = wa0 := Option.some.inj (hw1.symm.trans getW4)
  subst aid1
  have runK := emit
  by_cases cond : (d4.match_length ≤ d4.max_lazy_match && d4.lookahead ≥ MIN_MATCH_u) = true
  · -- insert the rest of a short match
    have cond' := cond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at cond'
    have la4' : 3 ≤ d4.lookahead.toNat := by
      have := UInt32.le_iff_toNat_le.mp cond'.2; change 3 ≤ _ at this; exact this
    let d5 : DeflateState := { d4 with match_length := d4.match_length - 1 }
    let h5 := setD h4 ds d5
    have wrA : wr (some (.tab ds)) (fun d => { d with match_length := d.match_length - 1 }) h4 = .ok ((), h5) := by
      rw [wrD_eq, good4.live.hs]
    have good5 : DGood h5 r ds z d5 := engine_update_good good4 rfl
    have la4n : d4.lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat := la4
    have chains5 : HeapChains h5 d5 (d5.strstart.toNat + 1) := by
      rw [show d5.strstart.toNat = d.strstart.toNat from ss4]
      refine ⟨w1, p1, q1, wa1, pa1, qa1, win1, prev1, head1, by simpa [h5] using hw1, by simpa [h5] using hp1,
        by simpa [h5] using hq1, ?_⟩
      change HashChains _ _ _ d4.hash_size d4.hash_shift d4.hash_mask d4.w_size.toNat _
        (d4.strstart.toNat + d4.lookahead.toNat)
      exact chains_lower_lim H1 (by rw [ss4]; omega)
    have form5 : InsHForm d5.hash_shift d5.hash_mask (bfn wa1) (d5.strstart.toNat + 1) d5.ins_h := by
      change InsHForm d4.hash_shift d4.hash_mask (bfn wa1) (d4.strstart.toNat + 1) d2.ins_h
      rw [eHs4, eHm4, ss4]; exact form2
    have getW5 : h5.bytes w1 = some wa1 := by simpa [h5] using getW4
    have pos5 : 1 ≤ d5.match_length.toNat := by
      change 1 ≤ (d2.match_length - 1).toNat; rw [u32_sub_one (by omega)]; omega
    have ml5 : d5.match_length.toNat = d2.match_length.toNat - 1 := by
      change (d2.match_length - 1).toNat = _; exact u32_sub_one (by omega)
    obtain ⟨cand, h6, d6, loopRun, good6, chains6, win6, bytesW6, ml6, ss6, la6, form6, frame6, bytes6, bframe6,
      borrow6⟩ := fast_match_insert_loop good5 chains5 win4 getW5 pos5 (by omega) la4'
        (by change d4.strstart.toNat + d5.match_length.toNat + 1 + d4.lookahead.toNat ≤ d4.window_size.toNat
            rw [ml5, ss4, la4n, eWs4]; have := shape.room; omega) form5 hh
    let d7 : DeflateState := { d6 with strstart := d6.strstart + 1 }
    let h7 := setD h6 ds d7
    have wr7 : wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + 1 }) h6 = .ok ((), h7) := by
      rw [wrD_eq, good6.live.hs]
    have good7 : DGood h7 r ds z d7 := engine_update_good good6 rfl
    have ss6n : d6.strstart.toNat = d.strstart.toNat + d2.match_length.toNat - 1 := by
      rw [ss6]; change d4.strstart.toNat + d5.match_length.toNat = _; rw [ss4, ml5]; omega
    have ss7 : d7.strstart.toNat = d.strstart.toNat + d2.match_length.toNat := by
      change (d6.strstart + 1).toNat = _
      rw [UInt32.toNat_add]; simp only [show (1 : UInt32).toNat = 1 from rfl]
      rw [Nat.mod_eq_of_lt (by have := shape.room; omega)]; omega
    have fields7 : d7 = { matchRecorded d2 with strstart := d7.strstart, match_length := 0, ins_h := d7.ins_h } := by
      have fr := frame6
      unfold FastInsertFrame at fr
      calc d7 = { d6 with strstart := d6.strstart + 1 } := rfl
        _ = { ({ d5 with strstart := d6.strstart, ins_h := d6.ins_h, match_length := d6.match_length } : DeflateState)
              with strstart := d6.strstart + 1 } := by rw [← fr]
        _ = { matchRecorded d2 with strstart := d7.strstart, match_length := 0, ins_h := d7.ins_h } := by
              rw [ml6]
    have runA : K (d2.sym_next + 3 == d2.sym_end) h4 =
        lazyTail (some (.tab ds)) st cand (d2.sym_next + 3 == d2.sym_end) h7 := by
      simp only [K, bind_app, ld4, cond, ite_true, wrA, loopRun, wr7]
    have bytes7 : h7.bytes = h4.bytes := by change h6.bytes = _; rw [bytes6]; rfl
    obtain ⟨buffers7, fullCase, notFullCase, level7, kind7, pending7, la7⟩ :=
      fast_match_final (h7 := h7) (d7 := d7) head pending search big good4 ledger4 dist4 pbuf2 getB4 buffers4
        static4 borrow4 count4 la4 good7 fields7 ss7 bytes7
        (by change h6.static = _; rw [bframe6.static]; rfl)
        (by change h6.libcErrorBorrow = _; rw [borrow6]; rfl)
        (fun i ne => by
          change (setD h6 ds d7).dstates i = _
          rw [setD_dstates_ne _ _ _ _ ne, bframe6.dstates i ne]; simp [h5, setD_dstates_ne _ _ _ _ ne])
        (fun i ne => by change h6.ro i = _; rw [bframe6.ro i ne]; rfl)
        (by
          obtain ⟨w', p', q', wa', pa', qa', win', prev', head', hw', hp', hq', H'⟩ := chains6
          refine ⟨w', p', q', wa', pa', qa', win', prev', head', by simpa [h7] using hw', by simpa [h7] using hp',
            by simpa [h7] using hq', ?_⟩
          change HashChains _ _ _ d6.hash_size d6.hash_shift d6.hash_mask d6.w_size.toNat _
            (d7.strstart.toNat + d6.lookahead.toNat)
          rw [← ss7]
          have e : d6.strstart.toNat + 1 = d7.strstart.toNat := by rw [ss7, ss6n]; omega
          rw [← e]
          exact chains_mono H' (Nat.le_refl _) (by omega))
        (fun large => ⟨w1, wa1, win, by simpa [h7] using bytesW6, by
          change InsHForm d.hash_shift d.hash_mask (bfn wa1) d7.strstart.toNat d6.ins_h
          have e : d6.strstart.toNat + 1 = d7.strstart.toNat := by rw [ss7, ss6n]; omega
          rw [← e]
          have hs : d6.hash_shift = d.hash_shift := by
            unfold FastInsertFrame at frame6; rw [frame6]; exact eHs4
          have hm : d6.hash_mask = d.hash_mask := by
            unfold FastInsertFrame at frame6; rw [frame6]; exact eHm4
          rw [← hs, ← hm]; exact form6⟩)
        (d2.sym_next + 3 == d2.sym_end) rfl notFull4
    obtain ⟨st', h', tailRun, brk', cases⟩ := lazy_tail_step safe fast_kind_keep st cand
      (d2.sym_next + 3 == d2.sym_end) buffers7 head.out head.input level7 kind7 pending7 fullCase notFullCase
    refine ⟨st', h', (emit.trans runA).trans tailRun, brk', ?_⟩
    rcases cases with ⟨retEq, z', d', head', pending', availEq, laEq'⟩ | more
    · exact Or.inl ⟨retEq, z', d', head', pending', by rw [availEq, laEq', la7]; omega⟩
    · exact Or.inr more
  · -- skip the rest of a long match and prime the hash at the new position
    have condF : (d4.match_length ≤ d4.max_lazy_match && d4.lookahead ≥ MIN_MATCH_u) = false := by
      simpa using cond
    have la4n : d4.lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat := la4
    let d5 : DeflateState := { d4 with strstart := d4.strstart + d4.match_length, match_length := 0 }
    let h5 := setD h4 ds d5
    have wrB : wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + d.match_length, match_length := 0 }) h4 =
        .ok ((), h5) := by rw [wrD_eq, good4.live.hs]
    have good5 : DGood h5 r ds z d5 := engine_update_good good4 rfl
    have ss5 : d5.strstart.toNat = d.strstart.toNat + d2.match_length.toNat := by
      change (d4.strstart + d2.match_length).toNat = _
      rw [UInt32.toNat_add, ss4, Nat.mod_eq_of_lt (by have := shape.room; omega)]
    have ld5 : ldDeflateState (some (.tab ds)) h5 = .ok (d5, h5) := ldDeflateState_tab good5.live.hs
    have getW5 : h5.bytes w1 = some wa1 := by simpa [h5] using getW4
    have win5 : d5.window = .ref (.blk w1) 0 := win4
    have read1 : index8 d5.window d5.strstart.toNat h5 = .ok (bfn wa1 (d.strstart.toNat + d2.match_length.toNat), h5) := by
      rw [win5, ss5]; exact index8_bfn getW5 (by simp) (by omega)
    obtain ⟨c1, c1def⟩ : ∃ x, x = bfn wa1 (d.strstart.toNat + d2.match_length.toNat) := ⟨_, rfl⟩
    rw [← c1def] at read1
    let d6 : DeflateState := { d5 with ins_h := c1.toUInt32 }
    let h6 := setD h5 ds d6
    have wr6 : wr (some (.tab ds)) (fun d => { d with ins_h := c1.toUInt32 }) h5 = .ok ((), h6) := by
      rw [wrD_eq, good5.live.hs]
    have good6 : DGood h6 r ds z d6 := engine_update_good good5 rfl
    have getW6 : h6.bytes w1 = some wa1 := by simpa [h6] using getW5
    have ss5' : (d5.strstart + 1).toNat = d.strstart.toNat + d2.match_length.toNat + 1 := by
      rw [UInt32.toNat_add, ss5]; simp only [show (1 : UInt32).toNat = 1 from rfl]
      rw [Nat.mod_eq_of_lt (by have := shape.room; omega)]
    have read2 : index8 d5.window (d5.strstart + 1).toNat h6 =
        .ok (bfn wa1 (d.strstart.toNat + d2.match_length.toNat + 1), h6) := by
      rw [win5, ss5']; exact index8_bfn getW6 (by simp) (by omega)
    obtain ⟨c2, c2def⟩ : ∃ x, x = bfn wa1 (d.strstart.toNat + d2.match_length.toNat + 1) := ⟨_, rfl⟩
    rw [← c2def] at read2
    have shift6 : d6.hash_shift < 32 := by
      change d4.hash_shift < 32; rw [eHs4, UInt32.lt_iff_toNat_lt]; exact hsh.hsh_lt
    have upd7 := UPDATE_HASH_ok (h := h6) (sr := ds) (d := d6) c2 good6.live.hs shift6
    let d7 : DeflateState := { d6 with ins_h := updHash d6.hash_shift d6.hash_mask d6.ins_h c2 }
    let h7 := setD h6 ds d7
    have upd7' : UPDATE_HASH (some (.tab ds)) c2 h6 = .ok ((), h7) := upd7
    have good7 : DGood h7 r ds z d7 := engine_update_good good6 rfl
    have runB : K (d2.sym_next + 3 == d2.sym_end) h4 =
        lazyTail (some (.tab ds)) st hh (d2.sym_next + 3 == d2.sym_end) h7 := by
      simp only [K, bind_app, ld4, condF, Bool.false_eq_true, ite_false, wrB, ld5, read1, wr6, read2, upd7']
    have fields7 : d7 = { matchRecorded d2 with strstart := d7.strstart, match_length := 0, ins_h := d7.ins_h } := rfl
    have ss7 : d7.strstart.toNat = d.strstart.toNat + d2.match_length.toNat := ss5
    obtain ⟨buffers7, fullCase, notFullCase, level7, kind7, pending7, la7⟩ :=
      fast_match_final (h7 := h7) (d7 := d7) head pending search big good4 ledger4 dist4 pbuf2 getB4 buffers4
        static4 borrow4 count4 la4 good7 fields7 ss7 rfl rfl rfl
        (fun i ne => by simp [h7, h6, h5, setD_dstates_ne _ _ _ _ ne]) (fun _ _ => rfl)
        (by
          refine ⟨w1, p1, q1, wa1, pa1, qa1, win1, prev1, head1, by simpa [h7, h6, h5] using hw1,
            by simpa [h7, h6, h5] using hp1, by simpa [h7, h6, h5] using hq1, ?_⟩
          change HashChains _ _ _ d4.hash_size d4.hash_shift d4.hash_mask d4.w_size.toNat _
            (d7.strstart.toNat + d4.lookahead.toNat)
          rw [ss7, la4n]
          have lim : d.strstart.toNat + d2.match_length.toNat + (d.lookahead.toNat - d2.match_length.toNat) =
              d.strstart.toNat + d.lookahead.toNat := by omega
          rw [lim]
          exact chains_mono H1 (by omega) (Nat.le_refl _))
        (fun _ => ⟨w1, wa1, win, by simpa [h7, h6, h5] using getW4, by
          change InsHForm d.hash_shift d.hash_mask (bfn wa1) d7.strstart.toNat
            (updHash d4.hash_shift d4.hash_mask c1.toUInt32 c2)
          rw [ss7, eHs4, eHm4, c1def, c2def]
          exact form_init hsh (bfn wa1) (d.strstart.toNat + d2.match_length.toNat)⟩)
        (d2.sym_next + 3 == d2.sym_end) rfl notFull4
    obtain ⟨st', h', tailRun, brk', cases⟩ := lazy_tail_step safe fast_kind_keep st hh
      (d2.sym_next + 3 == d2.sym_end) buffers7 head.out head.input level7 kind7 pending7 fullCase notFullCase
    refine ⟨st', h', (emit.trans runB).trans tailRun, brk', ?_⟩
    rcases cases with ⟨retEq, z', d', head', pending', availEq, laEq'⟩ | more
    · exact Or.inl ⟨retEq, z', d', head', pending', by rw [availEq, laEq', la7]; omega⟩
    · exact Or.inr more


/-- The states of the `deflate_fast` loop. -/
def FastLoop (r : ZStreamRef) (ds : Nat) (st : LoopS) (h : Heap) : Prop :=
  ∃ z d, Head FastKind h r ds z d ∧
    ((st.brk = false ∧ st.ret = none ∧ d.pending = 0) ∨ st.ret = some need_more ∨
     (st.brk = true ∧ st.ret = none ∧ d.pending = 0 ∧ d.lookahead = 0 ∧ z.avail_in = 0))

/-- One search and emission of `deflate_fast` from a loop head with lookahead and matcher room. -/
theorem fast_iter (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head FastKind h r ds z d) (pending : d.pending = 0)
    (look : 1 ≤ d.lookahead.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (st : LoopS) :
    ∃ st' h', (do
        let hash_head ← fastSearch (some (.tab ds))
        fastEmit (some (.tab ds)) st hash_head) h = .ok (st', h') ∧ st'.brk = st.brk ∧
      ((st'.ret = st.ret ∧ ∃ z' d', Head FastKind h' r ds z' d' ∧ d'.pending = 0 ∧
          z'.avail_in.toNat + d'.lookahead.toNat < z.avail_in.toNat + d.lookahead.toNat) ∨
       (st'.ret = some need_more ∧ ∃ z' d', Head FastKind h' r ds z' d')) := by
  obtain ⟨hh, h2, d2, searchRun, search⟩ := fast_search_run head look room
  by_cases big : 3 ≤ d2.match_length.toNat
  · obtain ⟨st', h', emitRun, rest⟩ := fast_match_emit safe head pending room search big st hh
    exact ⟨st', h', by simp only [bind_app, searchRun]; exact emitRun, rest⟩
  · obtain ⟨st', h', emitRun, rest⟩ := fast_literal_emit safe head pending look search (by omega) st hh
    exact ⟨st', h', by simp only [bind_app, searchRun]; exact emitRun, rest⟩

set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_fast`** from a loop head. -/
theorem fast_body_step (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head FastKind h r ds z d) (pending : d.pending = 0) (flush : Int32)
    (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_fast_body (some (.tab ds)) flush st h = .ok (st', h') ∧ FastLoop r ds st' h' ∧
      loopMeasure r ds st' h' < loopMeasure r ds st h := by
  have measure0 := loop_measure_head head.inv.good.live.hz head.inv.good.live.hs brk ret
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head FastKind h1 r ds z1 d1 →
      d1.pending = 0 → 1 ≤ d1.lookahead.toNat → d1.strstart.toNat + 262 ≤ d1.window_size.toNat →
      z1.avail_in.toNat + d1.lookahead.toNat ≤ z.avail_in.toNat + d.lookahead.toNat →
      ∃ st' h', (do
          let hash_head ← fastSearch (some (.tab ds))
          fastEmit (some (.tab ds)) st hash_head) h1 = .ok (st', h') ∧ FastLoop r ds st' h' ∧
        loopMeasure r ds st' h' < loopMeasure r ds st h := by
    intro h1 z1 d1 head1 pending1 look1 room1 sum
    obtain ⟨st', h', iterRun, brk', choice⟩ := fast_iter safe head1 pending1 look1 room1 st
    refine ⟨st', h', iterRun, ?_, ?_⟩
    · rcases choice with ⟨retEq, z', d', head', pending', _⟩ | ⟨retEq, z', d', head'⟩
      · exact ⟨z', d', head', Or.inl ⟨brk'.trans brk, retEq.trans ret, pending'⟩⟩
      · exact ⟨z', d', head', Or.inr (Or.inl retEq)⟩
    · rcases choice with ⟨retEq, z', d', head', pending', count⟩ | ⟨retEq, _⟩
      · rw [loop_measure_head head'.inv.good.live.hz head'.inv.good.live.hs (brk'.trans brk) (retEq.trans ret),
          measure0]
        omega
      · rw [loop_measure_exit (Or.inr (by rw [retEq]; rfl)), measure0]; omega
  rw [fast_body_source]
  by_cases small : d.lookahead < MIN_LOOKAHEAD_u
  · have short : d.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨sLevel, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, sPending, _⟩ := post.same
    have head1 : Head FastKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold FastKind; rw [sStrategy, sLevel]; exact k)
    have pending1 : d1.pending = 0 := sPending.trans pending
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    have consumed := post.consumed
    have room1 := fill_room post
    have fillRun' : fill_window (some (.tab ds)) h = .ok ((), after1) := fillRun
    by_cases stop1 : (d1.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · refine ⟨{ st with ret := some need_more }, after1, ?_, ⟨z1, d1, head1, Or.inr (Or.inl rfl)⟩, ?_⟩
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
          ⟨z1, d1, head1, Or.inr (Or.inr ⟨rfl, ret, pending1, empty1, availZero⟩)⟩, ?_⟩
        · simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
            Bool.false_eq_true, ite_false, empty1B]
          rfl
        · rw [loop_measure_exit (Or.inl rfl), measure0]; omega
      · have empty1B : (d1.lookahead == 0) = false := by simpa using empty1
        have look1 : 1 ≤ d1.lookahead.toNat := by
          have : d1.lookahead.toNat ≠ 0 := fun e => empty1 (UInt32.toNat_inj.mp e)
          omega
        obtain ⟨st', h', iterRun, loop', less⟩ := finishIter head1 pending1 look1 room1 (by omega)
        refine ⟨st', h', ?_, loop', less⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        simp only [bind_app] at iterRun
        exact iterRun
  · have big : 262 ≤ d.lookahead.toNat := by
      have := small; rw [UInt32.lt_iff_toNat_lt] at this; change ¬ _ < 262 at this; omega
    have room := head.inv.shape.room
    obtain ⟨st', h', iterRun, loop', less⟩ := finishIter head pending (by omega) (by omega) (Nat.le_refl _)
    refine ⟨st', h', ?_, loop', less⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    simp only [bind_app] at iterRun
    exact iterRun

/-- The `deflate_fast` loop ends in a `need_more` return or a `break` at the end of the input. -/
theorem fast_loop (safe : FlushSafe) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head FastKind h r ds z d) (pending : d.pending = 0) (flush : Int32) :
    ∃ st h', cwhile forever (deflate_fast_body (some (.tab ds)) flush) {} h = .ok (st, h') ∧
      FastLoop r ds st h' ∧ (st.brk = true ∨ st.ret.isSome = true) := by
  have start : FastLoop r ds {} h := ⟨z, d, head, Or.inl ⟨rfl, rfl, pending⟩⟩
  obtain ⟨st, h', run, loop, exit⟩ := cwhile_measure (cond := forever)
    (body := deflate_fast_body (some (.tab ds)) flush) (FastLoop r ds)
    (fun st h => FastLoop r ds st h ∧ (st.brk = true ∨ st.ret.isSome = true)) (loopMeasure r ds)
    (fun st h ⟨z, d, head, cases⟩ => by
      rcases cases with ⟨brk, ret, pending⟩ | ret | ⟨brk, ret, pending, _, _⟩
      · refine ⟨true, st, h, (by simp [forever, brk, ret]), (fun _ => ?_), (fun e => by cases e)⟩
        exact fast_body_step safe head pending flush st brk ret
      · refine ⟨false, st, h, (by simp [forever, ret]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z, d, head, Or.inr (Or.inl ret)⟩, Or.inr (by rw [ret]; rfl)⟩
      · refine ⟨false, st, h, (by simp [forever, brk]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z, d, head, Or.inr (Or.inr ⟨brk, ret, pending, by assumption, by assumption⟩)⟩, Or.inl brk⟩)
    start (loop_measure_bound r ds {} h)
  exact ⟨st, h', run, loop, exit⟩

end Zlib.Deflate.Universal
