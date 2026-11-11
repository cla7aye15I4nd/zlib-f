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
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ d'.bi_valid.toInt < 8 ∧
      d'.pending_buf = d.pending_buf ∧ z'.next_out ≠ .null ∧
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
  by_cases full : z1.avail_out = 0
  · obtain ⟨good5, buffers5, _⟩ := last_flush_frame (pb := pb) good1 trees1 buffers1 (-1)
    refine ⟨_, z1, _, produced, good5, ⟨buf1, trees_at_buffer good5 trees1.base.pbuf trees1.base.bytes, size1⟩,
      buffers5, account1, low1, pbuf1, out1, Or.inl ⟨?_, full, rfl⟩⟩
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
    refine ⟨H1, z1, d1, produced, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, low1, pbuf1, out1,
      Or.inr ⟨?_, full, zero, empty1 zero, by rw [fields1], fields1⟩⟩
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
      d1.pending.toNat ≤ 6 ∧ BitsDiff d d1 := by
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
  refine ⟨_, result, next, ?_, goodA, treesA, size, buffersA, cursorA, pbufA, aligned, by simp at room; omega, diff⟩
  rw [stored_empty_any _ _ (.ref (.blk w) 0)]
  exact run

/-- **The hash clearing of a full flush** (`CLEAR_HASH`). -/
theorem clear_hash_step {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) :
    ∃ (after : Heap), CLEAR_HASH (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z { d with slid := 0 } ∧ TreesInvAt after ds { d with slid := 0 } pb buf ∧
      StreamBuffers after r ∧ after.bytes = h.bytes := by
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
  exact ⟨_, run, goodA, treesA, buffersA, rfl⟩

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

/-- **The flush marker after `block_done`** on a drained `pending_buf`, for every flush value. -/
theorem marker_tail {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (out : z.next_out ≠ .null)
    (flush : Int32) (k : M Int32) :
    ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
      DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ d'.bi_valid.toInt < 8 ∧
      ((markerTail (some r) (some (.tab ds)) flush k h = .ok (Z_OK, after)) ∨
       (markerTail (some r) (some (.tab ds)) flush k h = k after ∧ d'.pending = 0 ∧
         d'.pending_out = d'.pending_buf)) := by
  have zeroN : d.pending.toNat = 0 := by rw [pending]; rfl
  have sizeLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have bitsLo := trees.run.bi_lo
  -- the flush from the state after the marker
  have finish : ∀ {H : Heap} {d1 : DeflateState} {buf1 : Array UInt8},
      DGood H r ds z d1 → TreesInvAt H ds d1 pb buf1 → buf1.size = buf.size → StreamBuffers H r →
      d1.pending_out = d1.pending_buf → 8 * d1.pending.toNat + d1.bi_valid.toInt.toNat ≤ 8 * buf1.size →
      ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
        DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
        StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ d'.bi_valid.toInt < 8 ∧
        ((markerFlush (some r) (some (.tab ds)) k H = .ok (Z_OK, after)) ∨
         (markerFlush (some r) (some (.tab ds)) k H = k after ∧ d'.pending = 0 ∧
           d'.pending_out = d'.pending_buf)) := by
    intro H d1 buf1 good1 trees1 size1 buffers1 cursor1 room1
    obtain ⟨after, z', d', produced, goodA, ⟨b', tA, sA⟩, buffersA, account, low, _, _, outcome⟩ :=
      marker_flush good1 trees1 buffers1 cursor1 room1 out k
    refine ⟨after, z', d', produced, goodA, ⟨b', tA, sA.trans size1⟩, buffersA, account, low, ?_⟩
    rcases outcome with ⟨e, _, _⟩ | ⟨e, _, zero, cur, _, _⟩
    · exact Or.inl e
    · exact Or.inr ⟨e, zero, cur⟩
  by_cases isPartial : flush = Z_PARTIAL_FLUSH
  · subst isPartial
    obtain ⟨next, d1, run, trees1, outBits1, size, _, _, _, diff⟩ :=
      Zlib.Trees.Proofs.Out.tr_align_emit trees (by omega)
    obtain ⟨good1, buffers1, cursor1, _⟩ := bits_step good trees buffers cursor size diff trees1
    have len := congrArg List.length outBits1
    simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append,
      Zlib.Trees.Proofs.Out.natBits_length, List.length_nil] at len
    obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, outcome⟩ :=
      finish good1 trees1 size buffers1 cursor1 (by rw [size]; omega)
    refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, ?_⟩
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
      obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, outcome⟩ :=
        finish good trees rfl buffers cursor (by rw [zeroN]; omega)
      refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, ?_⟩
      have eq : markerTail (some r) (some (.tab ds)) Z_BLOCK k h = markerFlush (some r) (some (.tab ds)) k h := by
        unfold markerTail markerFlush
        simp only [np, Bool.false_eq_true, ite_false, show (Z_BLOCK != Z_BLOCK) = false from rfl, bind_app, pure_app]
      rw [eq]; exact outcome
    · have nb : (flush != Z_BLOCK) = true := bne_iff_ne.mpr isBlock
      obtain ⟨H1, d1, buf1, run1, good1, trees1, size1, buffers1, cursor1, _, zero1, pend1, diff1⟩ :=
        empty_stored_block good trees buffers cursor pending bits
      have look1 : d1.lookahead = d.lookahead := by obtain ⟨_, _, _, _, e⟩ := diff1; rw [e]
      by_cases isFull : flush = Z_FULL_FLUSH
      · subst isFull
        obtain ⟨H2, run2, good2, trees2, buffers2, bytes2⟩ := clear_hash_step good1 trees1 buffers1
        have room2 : 8 * ({ d1 with slid := 0 } : DeflateState).pending.toNat +
            ({ d1 with slid := 0 } : DeflateState).bi_valid.toInt.toNat ≤ 8 * buf1.size := by
          change 8 * d1.pending.toNat + d1.bi_valid.toInt.toNat ≤ _; rw [zero1, size1]; simp; omega
        by_cases look : d1.lookahead = 0
        · obtain ⟨good3, trees3, buffers3⟩ := positions_reset good2 trees2 buffers2
          obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, outcome⟩ :=
            finish good3 trees3 size1 buffers3 cursor1 room2
          refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, ?_⟩
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
        · obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, outcome⟩ :=
            finish good2 trees2 size1 buffers2 cursor1 room2
          refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, ?_⟩
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
      · obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, outcome⟩ :=
          finish good1 trees1 size1 buffers1 cursor1 (by rw [zero1]; simp; omega)
        refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, low, ?_⟩
        have eq : markerTail (some r) (some (.tab ds)) flush k h = markerFlush (some r) (some (.tab ds)) k H1 := by
          unfold markerTail markerFlush
          simp only [np, nb, beq_eq_false_iff_ne.mpr isFull, Bool.false_eq_true, ite_false, ite_true, bind_app]
          rw [run1]
        rw [eq]; exact outcome

end Zlib.Deflate.Universal.Call
