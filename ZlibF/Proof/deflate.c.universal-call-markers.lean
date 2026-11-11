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

end Zlib.Deflate.Universal.Call
