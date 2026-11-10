import ZlibF.Proof.«deflate.c.engine.memory-stored-block»
import ZlibF.Proof.«deflate.c.engine.memory-dynamic-block»
import ZlibF.Proof.«deflate.c.engine.flush-frame»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
open Zlib.Trees.Proofs (sourceWords SourceCodeFacts PreparedHeaderData dynamicHeaderBits dynamicTag)
open Zlib.Trees.Proofs.Out (payloadSymBits codeBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem memory_stored_block_frame_execution {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (nonnegative : 0 ≤ d.block_start.toInt)
    (balance : BlockBalance d xs 0) (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (selectedRoom : represented xs + 6 ≤ buf.size) (lengthBound : represented xs < 65536) (last : Bool) :
    ∃ after result next,
      (do Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat)
            (UInt64.ofNat (represented xs)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  obtain ⟨emittedBuf, emitted, emitRun, goodE, treesE, buffersE, _sizesE, _storageE, diffE,
    sizeE, cursorE, alignedE, pendingE, _outputE, _grammar⟩ :=
    memory_stored_block_payload_engine (ob := ob) good trees buffers cursor pending bits win get range nonnegative
      balance accounted view selectedRoom lengthBound last
  have room : 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [alignedE]
    change 8 * emitted.pending.toNat ≤ 8 * emittedBuf.size
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
theorem memory_dynamic_prepared_payload_frame {memory : Nat} {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (capacity : d.lit_bufsize.toNat = 2 ^ (memory + 6))
    (memoryLow : 5 ≤ memory) (memoryHigh : memory ≤ 9)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (last : Bool) :
    ∃ (mb : Int32) (ready : DeflateState) (after : Heap) (result : DeflateState) (next : Array UInt8),
      dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ TreePreparationFrame d ready ∧
      SourceCodeFacts d ready ∧ PreparedHeaderData ready mb ∧ SourceCodeFacts d result ∧
      next.size = buf.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * result.pending_buf_size.toNat ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (dynamicTag last ++ dynamicHeaderBits ready mb ++
          xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist) (s.distance, s.value)) ++
            codeBits (sourceWords ready .lit) 256) ∧ FlushWorkFrame d result := by
  obtain ⟨mb, ready, prepare, goodR, treesR, buffersR, sizesR, storageR, frameR, outputR, data⟩ :=
    memory_all_trees_dynamic_data_engine (ob := ob) good trees buffers ledger clear trees.run.sym_next_le capacity memoryLow memoryHigh pending bits
  obtain ⟨otherMb, other, codeRun, codes⟩ := Zlib.Trees.Proofs.prepare_source_code_facts trees
  have same : other = ready := Zlib.Trees.Proofs.same_record_of_runs codeRun prepare
  subst other
  have cursorR : ready.pending_out = ready.pending_buf := by rw [frameR]; exact cursor
  have packedR : PackedSymbols buf ready.lit_bufsize.toNat xs := by rw [frameR]; exact ledger.packed
  have countR : ready.sym_next.toNat = 3 * xs.length := by rw [frameR]; exact ledger.count
  obtain ⟨headerBuf, headerState, headerRun, goodH, treesH, buffersH, sizesH, storageH,
    diffH, _headerSize, cursorH, packedH, _headerDataH, roomH, outputH⟩ :=
    memory_dynamic_header_engine (ob := ob) goodR treesR buffersR cursorR data packedR last
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
    memory_dynamic_payload_ready (ob := ob) goodH treesH buffersH cursorH ledger (codes.bitsDiff diffH) packedH roomH countH
  refine ⟨mb, ready, _, result, next, ?_, goodA, treesA, buffersA,
    (sizesR.trans sizesH).trans sizesA, (storageR.trans storageH).trans storageA,
    frameR, codes, data.header, codesA, sizeA.trans _headerSize, cursorA, roomA, ?_, ?_⟩
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
theorem memory_dynamic_block_frame_execution {memory : Nat} {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (capacity : d.lit_bufsize.toNat = 2 ^ (memory + 6))
    (memoryLow : 5 ≤ memory) (memoryHigh : memory ≤ 9)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (last : Bool) :
    ∃ after result next,
      (do dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  obtain ⟨mb, ready, emittedHeap, emitted, emittedBuf, emitRun, goodE, treesE, buffersE,
    _sizesE, _storageE, _prepareFrame, _codes, _header, _codesA, sizeE, cursorE, roomE, _outputE, frameE⟩ :=
    memory_dynamic_prepared_payload_frame (ob := ob) good trees buffers cursor capacity memoryLow memoryHigh pending bits ledger clear last
  have room : 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    have physicalSize := treesE.base.psize
    omega
  obtain ⟨after, result, next, tailRun, goodA, treesA, buffersA, frameA⟩ :=
    flush_tail_frame_execution (ob := ob) goodE treesE buffersE cursorE room last
  refine ⟨after, result, next, ?_, goodA, treesA, buffersA, frameE.trans frameA⟩
  rw [bind_app, emitRun]
  exact tailRun

end Zlib.Deflate.Engine.Proofs

#print axioms Zlib.Deflate.Engine.Proofs.memory_stored_block_frame_execution

#print axioms Zlib.Deflate.Engine.Proofs.memory_dynamic_prepared_payload_frame

#print axioms Zlib.Deflate.Engine.Proofs.memory_dynamic_block_frame_execution
