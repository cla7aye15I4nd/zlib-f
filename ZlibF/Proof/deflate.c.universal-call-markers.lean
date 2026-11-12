import ZlibF.Proof.«deflate.c.universal-call-trailer»

/-!
# deflate.c: the flush markers of one `deflate` call

Batch C (`deflate_header_trailer`). After a strategy returns `block_done`, `deflate` writes the
marker the flush asks for: the empty static block for `Z_PARTIAL_FLUSH`, the empty stored block
for `Z_SYNC_FLUSH` and `Z_FULL_FLUSH` (with the hash table cleared for a full flush), nothing for
`Z_BLOCK`; then it flushes.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees («_tr_init» «_tr_flush_bits» «_tr_flush_block» «_tr_stored_block» «_tr_align»)
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- The marker after `block_done`, the flush and its early return. -/
def markerTail (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) : M Int32 := do
  if flush == Z_PARTIAL_FLUSH then
    «_tr_align» s
  else if flush != Z_BLOCK then
    «_tr_stored_block» s (Ptr.null : BPtr) 0 0
    if flush == Z_FULL_FLUSH then
      CLEAR_HASH s
      if (← rd s (·.lookahead)) == 0 then
        wr s (fun d => { d with strstart := 0, block_start := 0, insert := 0 })
  flush_pending strm
  if (← zrd strm (·.avail_out)) == 0 then
    wr s (fun d => { d with last_flush := -1 })
    return Z_OK
  k

/-- What follows a strategy: `FINISH_STATE`, the early returns, and the markers. -/
def strategyAfter (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (bstate : block_state)
    (k : M Int32) : M Int32 := do
  if bstate == finish_started || bstate == finish_done then
    wr s (fun d => { d with status := FINISH_STATE })
  if bstate == need_more || bstate == finish_started then
    if (← zrd strm (·.avail_out)) == 0 then
      wr s (fun d => { d with last_flush := -1 })
    return Z_OK
  if bstate == block_done then markerTail strm s flush k else k

def strategyPhase' (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) : M Int32 := do
  let d ← ldDeflateState s
  if (← zrd strm (·.avail_in)) != 0 || d.lookahead != 0 || (flush != Z_NO_FLUSH && d.status != FINISH_STATE) then
    let bstate : block_state ←
      if d.level == 0 then deflate_stored s flush
      else if d.strategy == Z_HUFFMAN_ONLY then deflate_huff s flush
      else if d.strategy == Z_RLE then deflate_rle s flush
      else do
        match (← config_at d.level).func with
        | .stored => deflate_stored s flush
        | .fast => deflate_fast s flush
        | .slow => deflate_slow s flush
    strategyAfter strm s flush bstate k
  else k

set_option maxRecDepth 20000 in
theorem strategy_phase_split (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) :
    strategyPhase strm s flush k = strategyPhase' strm s flush k := by
  delta strategyPhase strategyPhase' strategyAfter markerTail
  exact rfl

/-- The marker itself. -/
def markerPart (s : DeflateStatePtr) (flush : Int32) : M Unit := do
  if flush == Z_PARTIAL_FLUSH then
    «_tr_align» s
  else if flush != Z_BLOCK then
    «_tr_stored_block» s (Ptr.null : BPtr) 0 0
    if flush == Z_FULL_FLUSH then
      CLEAR_HASH s
      if (← rd s (·.lookahead)) == 0 then
        wr s (fun d => { d with strstart := 0, block_start := 0, insert := 0 })

/-- The flush after the marker and its early return. -/
def markerFlush (strm : ZStreamPtr) (s : DeflateStatePtr) (k : M Int32) : M Int32 := do
  flush_pending strm
  if (← zrd strm (·.avail_out)) == 0 then
    wr s (fun d => { d with last_flush := -1 })
    return Z_OK
  k

theorem stored_empty_any (s : DeflateStatePtr) (p q : BPtr) (last : Int32) :
    «_tr_stored_block» s p 0 last = «_tr_stored_block» s q 0 last := by
  unfold «_tr_stored_block»
  simp only [show ((0 : UInt64) != 0) = false from rfl, Bool.false_eq_true, ite_false]

/-- The narrow block frame of a flush marker: as `OutputStorage`, and the `head` block, which
`CLEAR_HASH` clears after a full flush. -/
structure HeadStorage (h g : Heap) (r : ZStreamRef) (ds pb ob q : Nat) : Prop where
  shape : Zlib.Deflate.Proofs.Shape h g
  nalloc : g.nalloc = h.nalloc
  nextBlk : g.nextBlk = h.nextBlk
  frame : Frame h g (fun x => StreamRoot r x ∨ x = ds ∨ x = pb ∨ x = ob ∨ x = q)

theorem HeadStorage.trans {h g j : Heap} {r : ZStreamRef} {ds pb ob q : Nat}
    (one : HeadStorage h g r ds pb ob q) (two : HeadStorage g j r ds pb ob q) : HeadStorage h j r ds pb ob q :=
  ⟨one.shape.trans two.shape, two.nalloc.trans one.nalloc, two.nextBlk.trans one.nextBlk,
    full_frame_trans_shape one.frame two.frame one.shape⟩

theorem HeadStorage.of_output {h g : Heap} {r : ZStreamRef} {ds pb ob q : Nat}
    (storage : OutputStorage h g r ds pb ob) : HeadStorage h g r ds pb ob q :=
  ⟨storage.shape, storage.nalloc, storage.nextBlk, full_frame_weaken storage.frame (by
    intro x changed
    rcases changed with root | e | e | e
    · exact Or.inl root
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e))))⟩

/-- The heap frame of the flush markers: as `StageFrame`, with the `head` words allowed to change. -/
def MarkerFrame (h after : Heap) (r : ZStreamRef) (ds pb : Nat) (d : DeflateState) (z z' : ZStream)
    (produced : Nat) : Prop :=
  StratFrame h after r ds d z z' 0 produced ∧
    ∀ ob q, ByteRoot z.next_out ob → d.head = .ref (.blk q) 0 → HeadStorage h after r ds pb ob q

theorem MarkerFrame.of_stage {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {d : DeflateState}
    {z z' : ZStream} (stage : StageFrame h after r ds pb d z z' produced) : MarkerFrame h after r ds pb d z z' produced :=
  ⟨stage.1, fun ob _ root _ => HeadStorage.of_output (stage.2 ob root)⟩

theorem MarkerFrame.trans {h m k : Heap} {r : ZStreamRef} {ds pb : Nat} {d d1 : DeflateState}
    {z z1 z2 : ZStream} {p1 p2 : Nat}
    (one : MarkerFrame h m r ds pb d z z1 p1) (two : MarkerFrame m k r ds pb d1 z1 z2 p2)
    (owned : ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b) (head : d1.head = d.head)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    MarkerFrame h k r ds pb d z z2 (p1 + p2) := by
  obtain ⟨strat1, storage1⟩ := one
  obtain ⟨strat2, storage2⟩ := two
  have next1 : z1.next_out = advance z.next_out p1 := strat1.1.1.2.2.2.2.2.1
  refine ⟨by simpa using StratFrame.trans strat1 strat2 owned good.uniq (output_target good buffers), ?_⟩
  intro ob q root hq
  exact (storage1 ob q root hq).trans
    (storage2 ob q (by rw [next1]; exact byte_root_advance.mpr root) (by rw [head]; exact hq))

/-- **`CLEAR_HASH`** is a marker part. -/
theorem MarkerFrame.clear {h : Heap} {r : ZStreamRef} {ds pb q : Nat} {d : DeflateState} {z : ZStream}
    {qa : Array UInt16} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pbuf : d.pending_buf = .ref (.blk pb) 0) (head : d.head = .ref (.blk q) 0) (getQ : h.words q = some qa)
    (a : Array UInt16) (d' : DeflateState) :
    MarkerFrame h (setD (setW h q a) ds d') r ds pb d z z 0 := by
  have stateW : (setW h q a).dstates ds = some d := good.live.hs
  have shape : Zlib.Deflate.Proofs.Shape h (setD (setW h q a) ds d') :=
    (shape_setW getQ a).trans (shape_setD stateW d')
  have slots : ∀ x, x ≠ q → x ≠ ds → Zlib.Deflate.Proofs.DefaultInit.SlotSame h (setD (setW h q a) ds d') x := by
    intro x nq nd
    simp [Zlib.Deflate.Proofs.DefaultInit.SlotSame, setD, setW, upd_ne _ _ _ _ nq, upd_ne _ _ _ _ nd]
  have frame : Frame h (setD (setW h q a) ds d') (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun x _ out => slots x ?_ ?_⟩
    · intro e; subst e; exact out (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl head)))))
    · intro e; exact out (Or.inr (Or.inl e))
  refine ⟨strat_frame_private (stream_accounting_zero z) (by simp) rfl frame shape (full_shape_live_change shape)
    rfl good.uniq (output_target good buffers), fun ob q' _ hq => ⟨shape, rfl, rfl, ?_⟩⟩
  have same : q' = q := by rw [head] at hq; cases hq; rfl
  subst same
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun x _ out => slots x ?_ ?_⟩
  · intro e; exact out (Or.inr (Or.inr (Or.inr (Or.inr e))))
  · intro e; exact out (Or.inr (Or.inl e))

/-- **The facts of a marker part for `deflate_call`**: the totals, the output frame, the static
tables, the window, `prev` and `pending_buf` (the `head` words may change). -/
theorem MarkerFrame.call_facts {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {d : DeflateState}
    {z z' : ZStream} (frame : MarkerFrame h after r ds pb d z z' produced) (good : DGood h r ds z d)
    (buffers : StreamBuffers h r) (pbuf : d.pending_buf = .ref (.blk pb) 0) (out : z.next_out ≠ .null) :
    z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] ∧
    after.static = h.static ∧
    (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
    (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
    (∀ b, d.pending_buf = .ref (.blk b) 0 → ∃ a', after.bytes b = some a') := by
  obtain ⟨⟨⟨_, totalIn, totalOut, buffer, _, _⟩, _⟩, storageAll⟩ := frame
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  have root : ByteRoot z.next_out ob := by
    rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩ <;> rw [ptr] <;> rfl
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have storage := storageAll ob q root blocks.head
  have outside := output_target good buffers
  have notOb : ∀ x, DeflateOwned ds d x → x ≠ ob := by
    intro x owned same
    subst same
    rcases outside with null | ⟨ob', oo, arr, ptr, _, no⟩ | ⟨owner, oo, f, ptr, _, no⟩
    · rw [null] at root; exact root
    · rw [ptr] at root; change x = ob' at root; subst root; exact no (Or.inr owned)
    · rw [ptr] at root; change x = owner at root; subst root; exact no (Or.inr owned)
  have bpb : b = pb := by have e := blocks.pbuf; rw [pbuf] at e; cases e; rfl
  subst bpb
  have hs := good.live.hs
  obtain ⟨wa, gw, _⟩ := blocks.wa
  obtain ⟨pa, gp, _⟩ := blocks.pa
  obtain ⟨ba, gb, _⟩ := blocks.ba
  have slots := storage.frame.2.2.2.2.2
  have notRoot : ∀ x, (h.bytes x ≠ none ∨ h.words x ≠ none) → ¬ StreamRoot r x := by
    intro x some
    rcases some with e | e
    · obtain ⟨a, ga⟩ := Option.ne_none_iff_exists'.mp e
      exact not_root_of_unique good.uniq good.live.hz ⟨(good.uniq.bytes_only ga).2.1, (good.uniq.bytes_only ga).2.2.2.2.2⟩
    · obtain ⟨a, ga⟩ := Option.ne_none_iff_exists'.mp e
      exact not_root_of_unique good.uniq good.live.hz ⟨(good.uniq.words_only ga).2.1, (good.uniq.words_only ga).2.2.2.2.2⟩
  refine ⟨by simpa using totalIn, totalOut, buffer, storage.frame.1.symm, ?_, ?_, ?_⟩
  · intro w' e
    rw [blocks.win] at e; cases e
    refine (slots w (by simp [Heap.live, gw]) ?_).1
    rintro (rt | e | e | e | e)
    · exact notRoot w (Or.inl (by rw [gw]; simp)) rt
    · rw [e] at gw; rw [(good.uniq.bytes_only gw).2.2.2.1] at hs; cases hs
    · exact blocks.wb e
    · exact notOb w (Or.inr (Or.inl blocks.win)) e
    · obtain ⟨qa, gq, _⟩ := blocks.qa; rw [← e] at gq; rw [(good.uniq.words_only gq).1] at gw; cases gw
  · intro p' e
    rw [blocks.prev] at e; cases e
    refine (slots p (by simp [Heap.live, gp]) ?_).2.1
    rintro (rt | e | e | e | e)
    · exact notRoot p (Or.inr (by rw [gp]; simp)) rt
    · rw [e] at gp; rw [(good.uniq.words_only gp).2.2.2.1] at hs; cases hs
    · rw [e] at gp; rw [(good.uniq.words_only gp).1] at gb; cases gb
    · exact notOb p (Or.inr (Or.inr (Or.inl blocks.prev))) e
    · exact blocks.pq e
  · intro b' e
    rw [blocks.pbuf] at e; cases e
    have some := (storage.shape b).1
    rw [gb] at some
    cases ga : after.bytes b with
    | none => rw [ga] at some; cases some
    | some a' => exact ⟨a', rfl⟩

/-- What the flush markers change in the state record: the pending and bit fields, `last_flush`,
`slid` (cleared by `CLEAR_HASH`) and the positions `strstart`, `block_start`, `insert` (reset after a
full flush with no lookahead). Every other field is kept. -/
def MarkerShape (d d' : DeflateState) : Prop :=
  ∃ (p : UInt64) (po : BPtr) (bb : UInt16) (bv bu lf sl : Int32) (ss : UInt32) (bs : Int64) (ins : UInt32),
    d' = { d with
      pending := p, pending_out := po, bi_buf := bb, bi_valid := bv, bi_used := bu, last_flush := lf,
      slid := sl, strstart := ss, block_start := bs, insert := ins }

theorem MarkerShape.refl (d : DeflateState) : MarkerShape d d :=
  ⟨d.pending, d.pending_out, d.bi_buf, d.bi_valid, d.bi_used, d.last_flush, d.slid, d.strstart, d.block_start,
    d.insert, rfl⟩

theorem MarkerShape.trans {a b c : DeflateState} (first : MarkerShape a b) (second : MarkerShape b c) :
    MarkerShape a c := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := first
  obtain ⟨p, po, bb, bv, bu, lf, sl, ss, bs, ins, rfl⟩ := second
  exact ⟨p, po, bb, bv, bu, lf, sl, ss, bs, ins, rfl⟩

/-- The record equation of the marker shape, in the form `DInv.lift` takes. -/
theorem MarkerShape.fields {d d' : DeflateState} (shape : MarkerShape d d') :
    d' = { d with
      pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf, bi_valid := d'.bi_valid,
      bi_used := d'.bi_used, last_flush := d'.last_flush, slid := d'.slid, strstart := d'.strstart,
      block_start := d'.block_start, insert := d'.insert } := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := shape; rfl

theorem MarkerShape.of_bits {d d1 : DeflateState}
    (fields : d1 = { d with
      pending := d1.pending, pending_out := d1.pending_out, bi_buf := d1.bi_buf,
      bi_valid := d1.bi_valid, bi_used := d1.bi_used }) : MarkerShape d d1 :=
  ⟨d1.pending, d1.pending_out, d1.bi_buf, d1.bi_valid, d1.bi_used, d.last_flush, d.slid, d.strstart,
    d.block_start, d.insert, fields⟩

theorem MarkerShape.of_diff {d d1 : DeflateState} (diff : BitsDiff d d1) : MarkerShape d d1 := by
  obtain ⟨p, a, v, u, rfl⟩ := diff
  exact ⟨p, d.pending_out, a, v, u, d.last_flush, d.slid, d.strstart, d.block_start, d.insert, rfl⟩

theorem MarkerShape.lastFlush (d : DeflateState) (v : Int32) : MarkerShape d { d with last_flush := v } :=
  ⟨d.pending, d.pending_out, d.bi_buf, d.bi_valid, d.bi_used, v, d.slid, d.strstart, d.block_start, d.insert, rfl⟩

theorem MarkerShape.slid (d : DeflateState) : MarkerShape d { d with slid := 0 } :=
  ⟨d.pending, d.pending_out, d.bi_buf, d.bi_valid, d.bi_used, d.last_flush, 0, d.strstart, d.block_start,
    d.insert, rfl⟩

theorem MarkerShape.positions (d : DeflateState) :
    MarkerShape d { d with strstart := 0, block_start := 0, insert := 0 } :=
  ⟨d.pending, d.pending_out, d.bi_buf, d.bi_valid, d.bi_used, d.last_flush, d.slid, 0, 0, 0, rfl⟩

theorem MarkerShape.owned {ds : Nat} {d d' : DeflateState} (shape : MarkerShape d d') :
    ∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := shape
  intro b; exact Iff.rfl

/-- **A flush with room in `pending_buf`** for the held bits, for either kind of output view. -/
theorem room_flush {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) (out : z.next_out ≠ .null) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' d' ∧
      (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧
      produced = min (d.pending.toNat + d.bi_valid.toInt.toNat / 8) z.avail_out.toNat ∧
      d'.pending.toNat + produced = d.pending.toNat + d.bi_valid.toInt.toNat / 8 ∧ d'.bi_valid.toInt < 8 ∧
      d' = { d with
        pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf,
        bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      (d'.pending = 0 → d'.pending_out = d'.pending_buf) := by
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  have treesOf : ∀ {after : Heap} {z' : ZStream} {d' : DeflateState}, DGood after r ds z' d' → ByteSizes h after →
      d'.pending_buf = d.pending_buf → ∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size := by
    intro after z' d' goodA sizes pbufEq
    obtain ⟨d0, b0, buf0, treesA⟩ := goodA.trees
    have state : d0 = d' := Option.some.inj (treesA.base.dstate.symm.trans goodA.live.hs)
    subst d0
    have block : b0 = pb := by
      have p1 := treesA.base.pbuf
      rw [pbufEq, trees.base.pbuf] at p1
      simpa using p1.symm
    subst b0
    obtain ⟨next, getN, sizeN⟩ := sizes.get (.blk pb) buf trees.base.bytes
    have same : buf0 = next := Option.some.inj (treesA.base.bytes.symm.trans getN)
    subst same
    exact ⟨buf0, ⟨treesA.base, treesA.run⟩, sizeN⟩
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, sizes, _st, copied, left,
      low, _valid, fields, _b, _p, _o⟩ := flush_pending_raw_bits good trees buffers ptr cursor room
    exact ⟨produced, after, z', d', run, goodA, treesOf goodA sizes (by rw [fields]), buffersA, account, copied,
      left, low, fields, raw_pending_run_empty_cursor good trees buffers ptr cursor room run goodA.live.hs⟩
  · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, sizes, _st, copied, left,
      low, _valid, fields, _b, _p, _o, _bf⟩ := flush_pending_foreign_bits_frame good trees buffers ptr cursor room
    exact ⟨produced, after, z', d', run, goodA, treesOf goodA sizes (by rw [fields]), buffersA, account, copied,
      left, low, fields, foreign_pending_run_empty_cursor good trees buffers ptr cursor room run goodA.live.hs⟩

/-- **The flush after a marker** and its early return when the output is full. -/
theorem marker_flush {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) (out : z.next_out ≠ .null)
    (k : M Int32) :
    ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
      DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ StageFrame h after r ds pb d z z' produced ∧
      d'.bi_valid.toInt < 8 ∧ d'.pending_buf = d.pending_buf ∧ z'.next_out ≠ .null ∧
      MarkerShape d d' ∧ d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert ∧
      d'.slid = d.slid ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧
      ((markerFlush (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧ z'.avail_out = 0 ∧ d'.last_flush = -1) ∨
       (markerFlush (some r) (some (.tab ds)) k h = k after ∧ z'.avail_out ≠ 0 ∧
         d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush ∧
         d' = { d with
           pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf,
           bi_valid := d'.bi_valid, bi_used := d'.bi_used })) := by
  obtain ⟨produced, H1, z1, d1, run1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, copied, left, low1, fields1,
    empty1⟩ := room_flush good trees buffers cursor room out
  have out1 : z1.next_out ≠ .null := by rw [account1.2.2.2.2.2.1]; exact advance_ne_null out _
  have pbuf1 : d1.pending_buf = d.pending_buf := by rw [fields1]
  have stage1 := StageFrame.of_flush_room good trees buffers cursor room out run1 good1.live.hz account1
  have shape1 : HeaderShape d d1 := ⟨_, _, _, _, _, _, _, _, fields1⟩
  have mshape1 : MarkerShape d d1 := MarkerShape.of_bits fields1
  have ss1 : d1.strstart = d.strstart := by have e := congrArg DeflateState.strstart fields1; exact e
  have bs1 : d1.block_start = d.block_start := by have e := congrArg DeflateState.block_start fields1; exact e
  have ins1 : d1.insert = d.insert := by have e := congrArg DeflateState.insert fields1; exact e
  have sl1 : d1.slid = d.slid := by have e := congrArg DeflateState.slid fields1; exact e
  by_cases full : z1.avail_out = 0
  · obtain ⟨good5, buffers5, _⟩ := last_flush_frame (pb := pb) good1 trees1 buffers1 (-1)
    refine ⟨_, z1, _, produced, good5, ⟨buf1, trees_at_buffer good5 trees1.base.pbuf trees1.base.bytes, size1⟩,
      buffers5, account1,
      by
        have s := StageFrame.trans stage1 (StageFrame.state good1 buffers1 trees1.base.pbuf { d1 with last_flush := -1 })
          (HeaderShape.owned shape1) good buffers
        rwa [Nat.add_zero] at s,
      low1, pbuf1, out1, mshape1.trans (MarkerShape.lastFlush d1 (-1)), ss1, bs1, ins1, sl1,
      fun z0 => empty1 z0, Or.inl ⟨?_, full, rfl⟩⟩
    unfold markerFlush
    simp only [bind_app]
    rw [run1]
    simp [zrd_eq, good1.live.hz, full, wrD_eq, good1.live.hs]
  · have avail : produced < z.avail_out.toNat := by
      have a := account1.2.2.2.1
      have : z1.avail_out.toNat ≠ 0 := fun e => full (UInt32.toNat_inj.mp (by rw [e]; rfl))
      omega
    have zero : d1.pending = 0 := by
      have : d1.pending.toNat = 0 := by rw [copied] at left avail; omega
      exact UInt64.toNat_inj.mp (by rw [this]; rfl)
    refine ⟨H1, z1, d1, produced, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, low1, pbuf1, out1,
      mshape1, ss1, bs1, ins1, sl1, empty1, Or.inr ⟨?_, full, zero, empty1 zero, by rw [fields1], fields1⟩⟩
    unfold markerFlush
    simp only [bind_app]
    rw [run1]
    simp [zrd_eq, good1.live.hz, full]

/-- A step that changes only `pending_buf` and the pending and bit fields keeps the engine
invariants, the caller buffers and the cursor. -/
theorem bits_step {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d result : DeflateState}
    {buf next : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (size : next.size = buf.size)
    (diff : BitsDiff d result)
    (treesA : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ds result pb next) :
    DGood (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) r ds z result ∧
      StreamBuffers (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) r ∧
      result.pending_out = result.pending_buf ∧ result.pending_buf = d.pending_buf := by
  refine ⟨output_bits_good good cursor trees.base.bytes size diff treesA,
    output_bits_buffers good buffers cursor trees.base.bytes size diff treesA, ?_, ?_⟩ <;>
  · obtain ⟨_, _, _, _, e⟩ := diff; rw [e]; try exact cursor

/-- **The empty stored block** (`_tr_stored_block(s, (char*)0, 0L, 0)`) on a drained `pending_buf`. -/
theorem empty_stored_block {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) :
    ∃ (after : Heap) (d1 : DeflateState) (buf1 : Array UInt8),
      «_tr_stored_block» (some (.tab ds)) (Ptr.null : BPtr) 0 0 h = .ok ((), after) ∧
      DGood after r ds z d1 ∧ TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size ∧ StreamBuffers after r ∧
      d1.pending_out = d1.pending_buf ∧ d1.pending_buf = d.pending_buf ∧ d1.bi_valid.toInt = 0 ∧
      d1.pending.toNat ≤ 6 ∧ BitsDiff d d1 ∧ StageFrame h after r ds pb d z z 0 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have pbEq : b = pb := by
    have := blocks.pbuf; rw [trees.base.pbuf] at this; simpa using this.symm
  subst pbEq
  obtain ⟨wa, getW, _⟩ := blocks.wa
  have sizeLo : 6 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have zeroN : d.pending.toNat = 0 := by rw [pending]; rfl
  obtain ⟨next, result, run, treesA, _out, size, aligned, room, diff⟩ :=
    Zlib.Trees.Proofs.Out.stored_block_emit (offset := 0) trees getW (Ne.symm blocks.wb) bits 0 (by simp)
      (by simp; omega) false
  obtain ⟨goodA, buffersA, cursorA, pbufA⟩ := bits_step good trees buffers cursor size diff treesA
  refine ⟨_, result, next, ?_, goodA, treesA, size, buffersA, cursorA, pbufA, aligned, by simp at room; omega, diff,
    StageFrame.bytes good buffers trees.base.pbuf trees.base.bytes next result⟩
  rw [stored_empty_any _ _ (.ref (.blk w) 0)]
  exact run

/-- **The hash clearing of a full flush** (`CLEAR_HASH`). -/
theorem clear_hash_step {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) :
    ∃ (after : Heap), CLEAR_HASH (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z { d with slid := 0 } ∧ TreesInvAt after ds { d with slid := 0 } pb buf ∧
      StreamBuffers after r ∧ after.bytes = h.bytes ∧ MarkerFrame h after r ds pb d z z 0 ∧
      ∀ q, d.head = .ref (.blk q) 0 → ∃ qa, after.words q = some qa ∧ ∀ j, j < d.hash_size.toNat → wfn qa j = 0 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨qa, getQ, sizeQ⟩ := blocks.qa
  have hashLo : 1 ≤ d.hash_size.toNat := by
    rw [good.inv.hsize]; exact Nat.one_le_two_pow
  have run := clearHash_run good.live.hs blocks.head getQ hashLo (by omega)
  let cleared := setW h q (clearHead qa d.hash_size.toNat)
  have goodW : DGood cleared r ds z d := good.words_set q _ qa getQ (size_clearHead _ _)
  let result : DeflateState := { d with slid := 0 }
  have inv : DStInv cleared ds result :=
    { goodW.inv with blocks := goodW.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA := goodW.setD' (d' := result) rfl goodW.live.status inv (by trkeep)
  have treesA := trees_at_buffer goodA trees.base.pbuf trees.base.bytes
  have sizesW : ByteSizes h cleared := ⟨fun ref a get => ⟨a, by cases ref <;> exact get, rfl⟩, fun ref => by cases ref <;> rfl⟩
  have sizes := sizesW.trans (block_record_sizes (d := d) (result := result) goodW.live.hs rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  refine ⟨_, run, goodA, treesA, buffersA, rfl,
    MarkerFrame.clear good buffers trees.base.pbuf blocks.head getQ (clearHead qa d.hash_size.toNat) result, ?_⟩
  intro q' hq
  have same : q' = q := by rw [blocks.head] at hq; cases hq; rfl
  subst same
  refine ⟨clearHead qa d.hash_size.toNat, setW_words_same h _ _, fun j hj => ?_⟩
  unfold wfn
  rw [Array.getD_eq_getD_getElem?, clear_head_zero qa _ (by omega) (by omega) j hj]
  rfl

/-- Resetting the positions after a full flush with no lookahead keeps the engine invariants. -/
theorem positions_reset {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) :
    let result : DeflateState := { d with strstart := 0, block_start := 0, insert := 0 }
    DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r := by
  intro result
  have inv : DStInv h ds result :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA := good.setD' (d' := result) rfl good.live.status inv (by trkeep)
  have treesA := trees_at_buffer goodA trees.base.pbuf trees.base.bytes
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth from rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  exact ⟨goodA, treesA, stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)⟩

/-- **The flush marker after `block_done`** on a drained `pending_buf`, for every flush value: the
record changes as `MarkerShape` says; without a full flush the positions and the `head` words are
kept; after a full flush every `head` entry below `hash_size` is zero, and the positions are kept
with lookahead and zero without it. The continue branch keeps `last_flush`. -/
theorem marker_tail {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (out : z.next_out ≠ .null)
    (flush : Int32) (k : M Int32) :
    ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
      DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ MarkerFrame h after r ds pb d z z' produced ∧
      d'.bi_valid.toInt < 8 ∧ MarkerShape d d' ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧
      z'.next_out ≠ .null ∧
      (flush ≠ Z_FULL_FLUSH → d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert ∧
        d'.slid = d.slid ∧ ∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) ∧
      (flush = Z_FULL_FLUSH →
        (∀ q, d.head = .ref (.blk q) 0 → ∃ qa, after.words q = some qa ∧ ∀ j, j < d.hash_size.toNat → wfn qa j = 0) ∧
        (d.lookahead ≠ 0 → d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert) ∧
        (d.lookahead = 0 → d'.strstart = 0 ∧ d'.block_start = 0 ∧ d'.insert = 0)) ∧
      ((markerTail (some r) (some (.tab ds)) flush k h = .ok (Z_OK, after) ∧ d'.last_flush = -1) ∨
       (markerTail (some r) (some (.tab ds)) flush k h = k after ∧ d'.pending = 0 ∧
         d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush)) := by
  have zeroN : d.pending.toNat = 0 := by rw [pending]; rfl
  have sizeLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have bitsLo := trees.run.bi_lo
  have keepD : ∀ {d1 : DeflateState}, BitsDiff d d1 → d1.last_flush = d.last_flush ∧ d1.strstart = d.strstart ∧
      d1.block_start = d.block_start ∧ d1.insert = d.insert ∧ d1.lookahead = d.lookahead ∧
      d1.hash_size = d.hash_size ∧ d1.slid = d.slid := by
    intro d1 diff; obtain ⟨_, _, _, _, rfl⟩ := diff; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the flush from the state after the marker
  have finish : ∀ {H : Heap} {d1 : DeflateState} {buf1 : Array UInt8},
      DGood H r ds z d1 → TreesInvAt H ds d1 pb buf1 → buf1.size = buf.size → StreamBuffers H r →
      d1.pending_out = d1.pending_buf → 8 * d1.pending.toNat + d1.bi_valid.toInt.toNat ≤ 8 * buf1.size →
      MarkerFrame h H r ds pb d z z 0 → (∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b) → d1.head = d.head →
      MarkerShape d d1 → d1.last_flush = d.last_flush →
      ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
        DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
        StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ MarkerFrame h after r ds pb d z z' produced ∧
        d'.bi_valid.toInt < 8 ∧ MarkerShape d d' ∧
        d'.strstart = d1.strstart ∧ d'.block_start = d1.block_start ∧ d'.insert = d1.insert ∧
        d'.slid = d1.slid ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧ z'.next_out ≠ .null ∧
        (∀ q, d.head = .ref (.blk q) 0 → after.words q = H.words q) ∧
        ((markerFlush (some r) (some (.tab ds)) k H = .ok (Z_OK, after) ∧ d'.last_flush = -1) ∨
         (markerFlush (some r) (some (.tab ds)) k H = k after ∧ d'.pending = 0 ∧
           d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush)) := by
    intro H d1 buf1 good1 trees1 size1 buffers1 cursor1 room1 pre owned1 head1 shape0 lf0
    obtain ⟨after, z', d', produced, goodA, ⟨b', tA, sA⟩, buffersA, account, stageA, low, _, outA, shapeF, ssF, bsF,
      insF, slF, curF, outcome⟩ := marker_flush good1 trees1 buffers1 cursor1 room1 out k
    have keepsA := StageFrame.keeps stageA good1 buffers1 trees1.base.pbuf out
    have mf := MarkerFrame.trans pre (MarkerFrame.of_stage stageA) owned1 head1 good buffers
    rw [Nat.zero_add] at mf
    refine ⟨after, z', d', produced, goodA, ⟨b', tA, sA.trans size1⟩, buffersA, account, mf, low,
      shape0.trans shapeF, ssF, bsF, insF, slF, curF, outA, fun q hq => keepsA.2.2.2.1 q (by rw [head1]; exact hq), ?_⟩
    rcases outcome with ⟨e, _, lf⟩ | ⟨e, _, zero, cur, lfk, _⟩
    · exact Or.inl ⟨e, lf⟩
    · exact Or.inr ⟨e, zero, cur, lfk.trans lf0⟩
  by_cases isPartial : flush = Z_PARTIAL_FLUSH
  · subst isPartial
    obtain ⟨next, d1, run, trees1, outBits1, size, _, _, _, diff⟩ :=
      Zlib.Trees.Proofs.Out.tr_align_emit trees (by omega)
    obtain ⟨good1, buffers1, cursor1, _⟩ := bits_step good trees buffers cursor size diff trees1
    have len := congrArg List.length outBits1
    simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append,
      Zlib.Trees.Proofs.Out.natBits_length, List.length_nil] at len
    have o1 : ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b := by
      obtain ⟨_, _, _, _, e⟩ := diff; rw [e]; exact fun _ => Iff.rfl
    have q1 : d1.head = d.head := by obtain ⟨_, _, _, _, e⟩ := diff; rw [e]
    have k1 := keepD diff
    have stage0 := StageFrame.bytes good buffers trees.base.pbuf trees.base.bytes next d1
    have keeps1 := StageFrame.keeps stage0 good buffers trees.base.pbuf out
    obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
      outcome⟩ := finish good1 trees1 size buffers1 cursor1 (by rw [size]; omega)
        (MarkerFrame.of_stage stage0) o1 q1 (MarkerShape.of_diff diff) k1.1
    refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
      fun _ => ⟨ssA.trans k1.2.1, bsA.trans k1.2.2.1, insA.trans k1.2.2.2.1, slA.trans k1.2.2.2.2.2.2,
        fun q hq => (wordsA q hq).trans (keeps1.2.2.2.1 q hq)⟩,
      fun e => absurd e (by decide), ?_⟩
    have eq : markerTail (some r) (some (.tab ds)) Z_PARTIAL_FLUSH k h =
        markerFlush (some r) (some (.tab ds)) k (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds d1) := by
      unfold markerTail markerFlush
      simp only [show (Z_PARTIAL_FLUSH == Z_PARTIAL_FLUSH) = true from rfl, ite_true, bind_app]
      rw [run]
      rfl
    rw [eq]; exact outcome
  · have np : (flush == Z_PARTIAL_FLUSH) = false := beq_eq_false_iff_ne.mpr isPartial
    by_cases isBlock : flush = Z_BLOCK
    · subst isBlock
      obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
        outcome⟩ := finish good trees rfl buffers cursor (by rw [zeroN]; omega)
          (MarkerFrame.of_stage (StageFrame.refl good buffers trees.base.pbuf)) (fun _ => Iff.rfl) rfl
          (MarkerShape.refl d) rfl
      refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
        fun _ => ⟨ssA, bsA, insA, slA, wordsA⟩, fun e => absurd e (by decide), ?_⟩
      have eq : markerTail (some r) (some (.tab ds)) Z_BLOCK k h = markerFlush (some r) (some (.tab ds)) k h := by
        unfold markerTail markerFlush
        simp only [np, Bool.false_eq_true, ite_false, show (Z_BLOCK != Z_BLOCK) = false from rfl, bind_app, pure_app]
      rw [eq]; exact outcome
    · have nb : (flush != Z_BLOCK) = true := bne_iff_ne.mpr isBlock
      obtain ⟨H1, d1, buf1, run1, good1, trees1, size1, buffers1, cursor1, _, zero1, pend1, diff1, stage1⟩ :=
        empty_stored_block good trees buffers cursor pending bits
      have o1 : ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b := by
        obtain ⟨_, _, _, _, e⟩ := diff1; rw [e]; exact fun _ => Iff.rfl
      have q1 : d1.head = d.head := by obtain ⟨_, _, _, _, e⟩ := diff1; rw [e]
      have k1 := keepD diff1
      have look1 : d1.lookahead = d.lookahead := k1.2.2.2.2.1
      have keeps1 := StageFrame.keeps stage1 good buffers trees.base.pbuf out
      by_cases isFull : flush = Z_FULL_FLUSH
      · subst isFull
        obtain ⟨H2, run2, good2, trees2, buffers2, bytes2, clear2, cleared2⟩ := clear_hash_step good1 trees1 buffers1
        have mf2 := MarkerFrame.trans (MarkerFrame.of_stage stage1) clear2 o1 q1 good buffers
        have room2 : 8 * ({ d1 with slid := 0 } : DeflateState).pending.toNat +
            ({ d1 with slid := 0 } : DeflateState).bi_valid.toInt.toNat ≤ 8 * buf1.size := by
          change 8 * d1.pending.toNat + d1.bi_valid.toInt.toNat ≤ _; rw [zero1, size1]; simp; omega
        have zeroHead : ∀ {G : Heap}, (∀ q, d.head = .ref (.blk q) 0 → G.words q = H2.words q) →
            ∀ q, d.head = .ref (.blk q) 0 → ∃ qa, G.words q = some qa ∧ ∀ j, j < d.hash_size.toNat → wfn qa j = 0 := by
          intro G words q hq
          obtain ⟨qa, getQ, zero⟩ := cleared2 q (by rw [q1]; exact hq)
          exact ⟨qa, (words q hq).trans getQ, fun j hj => zero j (by rw [k1.2.2.2.2.2.1]; exact hj)⟩
        by_cases look : d1.lookahead = 0
        · obtain ⟨good3, trees3, buffers3⟩ := positions_reset good2 trees2 buffers2
          have mf3 := MarkerFrame.trans mf2 (MarkerFrame.of_stage (StageFrame.state good2 buffers2 trees2.base.pbuf
            { ({ d1 with slid := 0 } : DeflateState) with strstart := 0, block_start := 0, insert := 0 }))
            (fun b => o1 b) q1 good buffers
          obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
            outcome⟩ := finish good3 trees3 size1 buffers3 cursor1 room2 (by simpa using mf3) (fun b => o1 b) q1
              ((MarkerShape.of_diff diff1).trans ((MarkerShape.slid d1).trans (MarkerShape.positions _))) k1.1
          refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
            fun ne => absurd rfl ne,
            fun _ => ⟨zeroHead wordsA, fun hl => absurd (by rw [← look1]; exact look) hl,
              fun _ => ⟨ssA, bsA, insA⟩⟩, ?_⟩
          have eq : markerTail (some r) (some (.tab ds)) Z_FULL_FLUSH k h =
              markerFlush (some r) (some (.tab ds)) k (setD H2 ds
                { ({ d1 with slid := 0 } : DeflateState) with strstart := 0, block_start := 0, insert := 0 }) := by
            unfold markerTail markerFlush
            simp only [show (Z_FULL_FLUSH == Z_PARTIAL_FLUSH) = false from rfl,
              show (Z_FULL_FLUSH != Z_BLOCK) = true from rfl, show (Z_FULL_FLUSH == Z_FULL_FLUSH) = true from rfl,
              Bool.false_eq_true, ite_false, ite_true, bind_app]
            rw [run1]; simp only []
            rw [run2]
            simp only [rdD_eq, good2.live.hs]
            simp only [look, show ((0 : UInt32) == 0) = true from rfl, ite_true, bind_app, wrD_eq, good2.live.hs]
          rw [eq]; exact outcome
        · obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
            outcome⟩ := finish good2 trees2 size1 buffers2 cursor1 room2 (by simpa using mf2) (fun b => o1 b) q1
              ((MarkerShape.of_diff diff1).trans (MarkerShape.slid d1)) k1.1
          refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
            fun ne => absurd rfl ne,
            fun _ => ⟨zeroHead wordsA, fun _ => ⟨ssA.trans k1.2.1, bsA.trans k1.2.2.1, insA.trans k1.2.2.2.1⟩,
              fun hl => absurd (by rw [look1]; exact hl) look⟩, ?_⟩
          have eq : markerTail (some r) (some (.tab ds)) Z_FULL_FLUSH k h =
              markerFlush (some r) (some (.tab ds)) k H2 := by
            unfold markerTail markerFlush
            simp only [show (Z_FULL_FLUSH == Z_PARTIAL_FLUSH) = false from rfl,
              show (Z_FULL_FLUSH != Z_BLOCK) = true from rfl, show (Z_FULL_FLUSH == Z_FULL_FLUSH) = true from rfl,
              Bool.false_eq_true, ite_false, ite_true, bind_app]
            rw [run1]; simp only []
            rw [run2]
            simp only [rdD_eq, good2.live.hs, beq_eq_false_iff_ne.mpr look, Bool.false_eq_true, ite_false, pure_app]
            rfl
          rw [eq]; exact outcome
      · obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
          outcome⟩ := finish good1 trees1 size1 buffers1 cursor1 (by rw [zero1]; simp; omega)
            (MarkerFrame.of_stage stage1) o1 q1 (MarkerShape.of_diff diff1) k1.1
        refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
          fun _ => ⟨ssA.trans k1.2.1, bsA.trans k1.2.2.1, insA.trans k1.2.2.2.1, slA.trans k1.2.2.2.2.2.2,
            fun q hq => (wordsA q hq).trans (keeps1.2.2.2.1 q hq)⟩,
          fun e => absurd e isFull, ?_⟩
        have eq : markerTail (some r) (some (.tab ds)) flush k h = markerFlush (some r) (some (.tab ds)) k H1 := by
          unfold markerTail markerFlush
          simp only [np, nb, beq_eq_false_iff_ne.mpr isFull, Bool.false_eq_true, ite_false, ite_true, bind_app]
          rw [run1]
        rw [eq]; exact outcome

end Zlib.Deflate.Universal.Call
