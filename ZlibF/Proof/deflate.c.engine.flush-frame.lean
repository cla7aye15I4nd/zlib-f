import ZlibF.Proof.«deflate.c.engine.flush-arguments»

/-! # Exact state fields changed by tree preparation and block output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
open Zlib.Trees.Proofs (sourceWords SourceCodeFacts PreparedHeaderData dynamicHeaderBits dynamicTag)
open Zlib.Trees.Proofs.Out (payloadSymBits codeBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Preparation and output may change tree/work arrays, block counters
and bit output. Window/hash pointers, positions, match history and all
compression configuration fields retain their exact values. -/
def FlushWorkFrame (before after : DeflateState) : Prop :=
  after = { before with
    dyn_ltree := after.dyn_ltree, dyn_dtree := after.dyn_dtree, bl_tree := after.bl_tree,
    l_desc := after.l_desc, d_desc := after.d_desc, bl_desc := after.bl_desc,
    bl_count := after.bl_count, heap := after.heap, heap_len := after.heap_len,
    heap_max := after.heap_max, depth := after.depth,
    pending := after.pending, pending_out := after.pending_out,
    bi_buf := after.bi_buf, bi_valid := after.bi_valid, bi_used := after.bi_used,
    opt_len := after.opt_len, static_len := after.static_len, «matches» := after.matches, sym_next := after.sym_next }

theorem FlushWorkFrame.refl (d : DeflateState) : FlushWorkFrame d d := rfl

theorem FlushWorkFrame.trans {before middle after : DeflateState}
    (first : FlushWorkFrame before middle) (second : FlushWorkFrame middle after) : FlushWorkFrame before after := by
  unfold FlushWorkFrame at first second ⊢
  rw [second, first]

theorem FlushWorkFrame.prepare {before after : DeflateState} (frame : TreePreparationFrame before after) :
    FlushWorkFrame before after := by
  unfold TreePreparationFrame at frame
  unfold FlushWorkFrame
  rw [frame]

theorem FlushWorkFrame.bits {before after : DeflateState} (frame : BitsDiff before after) :
    FlushWorkFrame before after := by
  obtain ⟨_, _, _, _, fields⟩ := frame
  rw [fields]
  rfl

theorem FlushWorkFrame.block {before after : DeflateState} (frame : BlockOutputFrame before after) :
    FlushWorkFrame before after := by
  unfold BlockOutputFrame at frame
  unfold FlushWorkFrame
  rw [frame]

theorem FlushWorkFrame.reset (before : DeflateState) (a b c : Array CtData) :
    FlushWorkFrame before (Zlib.Trees.Proofs.Out.ibRec before a b c) := rfl

theorem FlushWorkFrame.output {before middle : DeflateState} (frame : FlushWorkFrame before middle)
    (pending : UInt64) (cursor : BPtr) (word : UInt16) (valid used : Int32) :
    FlushWorkFrame before { middle with
      pending := pending, pending_out := cursor, bi_buf := word, bi_valid := valid, bi_used := used } := by
  unfold FlushWorkFrame at frame ⊢
  rw [frame]

theorem FlushWorkFrame.block_start {before after : DeflateState} (frame : FlushWorkFrame before after)
    (position : Int64) :
    FlushWorkFrame { before with block_start := position } { after with block_start := position } := by
  unfold FlushWorkFrame at frame ⊢
  rw [frame]

/-- The actual common tail preserves all input/history/configuration
fields. It includes the real reset and both final-windup cases. This
frame is additional data for rebuilding the outer strategy invariant. -/
theorem flush_tail_frame_execution {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) (last : Bool) :
    ∃ after result next,
      Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  obtain ⟨a1, a2, a3, reset, resetRun, goodR, treesR, buffersR, _sizesR, _storageR,
    resetFields, _ledgerR, _outputR⟩ := init_block_engine (ob := ob) good trees buffers
  have frameR : FlushWorkFrame d reset := by rw [resetFields]; exact FlushWorkFrame.reset _ _ _ _
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursor
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * buf.size := by rw [resetFields]; exact room
  cases last with
  | false =>
    refine ⟨_, reset, buf, ?_, goodR, treesR, buffersR, frameR⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, resetRun, show ((0 : Int32) != 0) = false from rfl,
      Bool.false_eq_true, ite_false, pure_app]
  | true =>
    obtain ⟨next, result, windRun, goodA, treesA, buffersA, _sizesA, _storageA, diffA, _rest⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR roomR
    refine ⟨_, result, next, ?_, goodA, treesA, buffersA, frameR.trans (FlushWorkFrame.bits diffA)⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, resetRun, show ((1 : Int32) != 0) = true from rfl, ite_true, windRun]

/-- Actual stored output followed by the common tail retains all
non-output state fields needed by the strategy's logical history. -/
theorem stored_block_frame_execution {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (nonnegative : 0 ≤ d.block_start.toInt)
    (balance : BlockBalance d xs 0) (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (selectedRoom : represented xs + 6 ≤ 63488) (last : Bool) :
    ∃ after result next,
      (do Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat)
            (UInt64.ofNat (represented xs)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  obtain ⟨emittedBuf, emitted, emitRun, goodE, treesE, buffersE, _sizesE, _storageE, diffE,
    sizeE, cursorE, alignedE, pendingE, _outputE, _grammar⟩ :=
    stored_payload_engine (ob := ob) good trees buffers cursor memory pending bits win get range nonnegative
      balance accounted view selectedRoom last
  have room : 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [alignedE, sizeE]
    change 8 * emitted.pending.toNat ≤ 524288
    omega
  obtain ⟨after, result, next, tailRun, goodA, treesA, buffersA, frameA⟩ :=
    flush_tail_frame_execution (ob := ob) goodE treesE buffersE cursorE room last
  refine ⟨after, result, next, ?_, goodA, treesA, buffersA, (FlushWorkFrame.bits diffE).trans frameA⟩
  rw [bind_app, emitRun]
  exact tailRun

/-- Actual construction, dynamic header and complete payload retain the
exact strategy/history record frame. This stronger sibling preserves the
earlier theorem and derives the frame from each real construction and
bit-output call rather than assuming it as a callee contract. -/
theorem dynamic_prepared_payload_frame {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (last : Bool) :
    ∃ (mb : Int32) (ready : DeflateState) (after : Heap) (result : DeflateState) (next : Array UInt8),
      dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ TreePreparationFrame d ready ∧
      SourceCodeFacts d ready ∧ PreparedHeaderData ready mb ∧ SourceCodeFacts d result ∧
      next.size = 65536 ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * 63488 ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (dynamicTag last ++ dynamicHeaderBits ready mb ++
          xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist) (s.distance, s.value)) ++
            codeBits (sourceWords ready .lit) 256) ∧ FlushWorkFrame d result := by
  obtain ⟨mb, ready, prepare, goodR, treesR, buffersR, sizesR, storageR, frameR, outputR, data⟩ :=
    all_trees_dynamic_data_engine (ob := ob) good trees buffers ledger clear trees.run.sym_next_le memory pending bits
  obtain ⟨otherMb, other, codeRun, codes⟩ := Zlib.Trees.Proofs.prepare_source_code_facts trees
  have same : other = ready := Zlib.Trees.Proofs.same_record_of_runs codeRun prepare
  subst other
  have memoryR : ready.lit_bufsize.toNat = 16384 := by rw [frameR]; exact memory
  have cursorR : ready.pending_out = ready.pending_buf := by rw [frameR]; exact cursor
  have packedR : PackedSymbols buf ready.lit_bufsize.toNat xs := by rw [frameR]; exact ledger.packed
  have countR : ready.sym_next.toNat = 3 * xs.length := by rw [frameR]; exact ledger.count
  obtain ⟨headerBuf, headerState, headerRun, goodH, treesH, buffersH, sizesH, storageH,
    diffH, _headerSize, cursorH, packedH, _headerDataH, roomH, outputH⟩ :=
    dynamic_header_engine (ob := ob) goodR treesR buffersR cursorR data packedR last
  have memoryH : headerState.lit_bufsize.toNat = 16384 := by
    obtain ⟨_, _, _, _, fields⟩ := diffH
    rw [fields]
    exact memoryR
  have countH : headerState.sym_next.toNat = 3 * xs.length := by
    obtain ⟨_, _, _, _, fields⟩ := diffH
    rw [fields]
    exact countR
  have wordL : sourceWords headerState .lit = sourceWords ready .lit := by
    obtain ⟨_, _, _, _, fields⟩ := diffH
    rw [fields]
    rfl
  have wordD : sourceWords headerState .dist = sourceWords ready .dist := by
    obtain ⟨_, _, _, _, fields⟩ := diffH
    rw [fields]
    rfl
  obtain ⟨next, result, payloadRun, goodA, treesA, buffersA, sizesA, storageA, diffA,
    sizeA, cursorA, codesA, roomA, outputA⟩ :=
    dynamic_payload_ready (ob := ob) goodH treesH buffersH cursorH memoryH ledger (codes.bitsDiff diffH) packedH roomH countH
  refine ⟨mb, ready, _, result, next, ?_, goodA, treesA, buffersA,
    (sizesR.trans sizesH).trans sizesA, (storageR.trans storageH).trans storageA,
    frameR, codes, data.header, codesA, sizeA, cursorA, roomA, ?_, ?_⟩
  · unfold dynamicPreparedPayload
    rw [← M_bind_assoc, bind_app, prepare]
    simp only [bind_app, headerRun, Zlib.Trees.Proofs.Out.pLtree_run goodH.live.hs,
      Zlib.Trees.Proofs.Out.pDtree_run goodH.live.hs]
    exact payloadRun
  · rw [outputA, outputH, outputR, wordL, wordD]
    simp only [List.append_assoc]
  · exact ((FlushWorkFrame.prepare frameR).trans (FlushWorkFrame.bits diffH)).trans (FlushWorkFrame.bits diffA)

/-- Actual dynamic construction/output and both common-tail cases retain
all strategy/history fields outside the explicit tree/output footprint. -/
theorem dynamic_block_frame_execution {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (last : Bool) :
    ∃ after result next,
      (do dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  obtain ⟨mb, ready, emittedHeap, emitted, emittedBuf, emitRun, goodE, treesE, buffersE,
    _sizesE, _storageE, _prepareFrame, _codes, _header, _codesA, sizeE, cursorE, roomE, _outputE, frameE⟩ :=
    dynamic_prepared_payload_frame (ob := ob) good trees buffers cursor memory pending bits ledger clear last
  have room : 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [sizeE]
    omega
  obtain ⟨after, result, next, tailRun, goodA, treesA, buffersA, frameA⟩ :=
    flush_tail_frame_execution (ob := ob) goodE treesE buffersE cursorE room last
  refine ⟨after, result, next, ?_, goodA, treesA, buffersA, frameE.trans frameA⟩
  rw [bind_app, emitRun]
  exact tailRun

end Zlib.Deflate.Engine.Proofs
