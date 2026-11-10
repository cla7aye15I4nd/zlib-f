import ZlibF.Proof.«deflate.c.engine.memory-four-dynamic-prepared»
import ZlibF.Proof.«deflate.c.engine.memory-block-frames»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A frame-only supplement for the existing mem-four dynamic adapter.
The real memory-four construction supplies header room; actual header and
payload BitsDiff facts preserve every strategy/history/configuration field. -/
theorem mem_four_dynamic_payload_frame_execution {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (capacity : d.lit_bufsize.toNat = 1024)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (last : Bool) :
    ∃ after result next,
      dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  obtain ⟨mb, ready, prepare, goodR, treesR, buffersR, _sizesR, _storageR, frameR, _outputR, data⟩ :=
    SmallMemory.mem_four_all_trees_dynamic_data_engine (ob := ob) good trees buffers ledger clear trees.run.sym_next_le capacity pending bits
  obtain ⟨_otherMb, other, codeRun, codes⟩ := Zlib.Trees.Proofs.prepare_source_code_facts trees
  have same : other = ready := Zlib.Trees.Proofs.same_record_of_runs codeRun prepare
  subst other
  have cursorR : ready.pending_out = ready.pending_buf := by rw [frameR]; exact cursor
  have packedR : PackedSymbols buf ready.lit_bufsize.toNat xs := by rw [frameR]; exact ledger.packed
  have countR : ready.sym_next.toNat = 3 * xs.length := by rw [frameR]; exact ledger.count
  obtain ⟨headerBuf, headerState, headerRun, goodH, treesH, buffersH, _sizesH, _storageH,
      diffH, _sizeH, cursorH, packedH, _dataH, roomH, _outputH⟩ :=
    memory_dynamic_header_engine (ob := ob) goodR treesR buffersR cursorR data packedR last
  have countH : headerState.sym_next.toNat = 3 * xs.length := by
    obtain ⟨_, _, _, _, fields⟩ := diffH
    rw [fields]
    exact countR
  obtain ⟨next, result, payloadRun, goodA, treesA, buffersA, _sizesA, _storageA, diffA, _restA⟩ :=
    memory_dynamic_payload_ready (ob := ob) goodH treesH buffersH cursorH ledger (codes.bitsDiff diffH) packedH roomH countH
  refine ⟨_, result, next, ?_, goodA, treesA, buffersA,
    ((FlushWorkFrame.prepare frameR).trans (FlushWorkFrame.bits diffH)).trans (FlushWorkFrame.bits diffA)⟩
  unfold dynamicPreparedPayload
  rw [← M_bind_assoc, bind_app, prepare]
  simp only [bind_app, headerRun, Zlib.Trees.Proofs.Out.pLtree_run goodH.live.hs,
    Zlib.Trees.Proofs.Out.pDtree_run goodH.live.hs]
  exact payloadRun

/-- Actual dynamic emission followed by real init_block and optional
windup preserves the complete strategy record at memory four. -/
theorem mem_four_dynamic_block_frame_execution {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (capacity : d.lit_bufsize.toNat = 1024)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (last : Bool) :
    ∃ after result next,
      (do dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  obtain ⟨heap, emitted, emittedBuf, run, goodE, treesE, buffersE, frameE⟩ :=
    mem_four_dynamic_payload_frame_execution (ob := ob) good trees buffers cursor capacity pending bits ledger clear last
  obtain ⟨_mb, _ready, other, otherD, _next, actual, goodP, _treesP, _buffersP, _sizesP, _storageP,
      _prepFrame, _codes, _header, _codesA, _sizeA, cursorE, roomE, _bitsE⟩ :=
    mem_four_dynamic_prepared_payload_engine (ob := ob) good trees buffers cursor capacity pending bits ledger clear last
  have heaps : other = heap := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  rw [heaps] at goodP
  have states : otherD = emitted := Option.some.inj (goodP.live.hs.symm.trans goodE.live.hs)
  subst otherD
  have room : 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    have physical := treesE.base.psize
    omega
  obtain ⟨after, result, next, tailRun, goodA, treesA, buffersA, frameA⟩ :=
    flush_tail_frame_execution (ob := ob) goodE treesE buffersE cursorE room last
  refine ⟨after, result, next, ?_, goodA, treesA, buffersA, frameE.trans frameA⟩
  rw [bind_app, run]
  exact tailRun
end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.mem_four_dynamic_payload_frame_execution
#print axioms Zlib.Deflate.Engine.Proofs.mem_four_dynamic_block_frame_execution
