import ZlibF.Proof.«deflate.c.engine.dynamic-wire-cost»
import ZlibF.Proof.«deflate.c.engine.dynamic-prepared-payload»
import ZlibF.Proof.«deflate.c.engine.block-windup»
import ZlibF.Math.DeflateStreamBudget

/-! # Actual dynamic emission has the prepared candidate's exact bit cost -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (sourceWords dynamicHeaderBits dynamicTag)
open Zlib.Trees.Proofs.Out (TreesInvAt outBits outBits_length payloadSymBits codeBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Real preparation, dynamic header and full dynamic payload use the
same final cost counter. The header's tag is the only additional three
bits. The natural counter equality is derived from actual output room,
so no caller-supplied no-wrap premise or callee contract is needed.
The common reset and final alignment remain the following source cut. -/
theorem dynamic_prepared_payload_bit_count {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (last : Bool) :
    ∃ (mb : Int32) (prepared : DeflateState) (after : Heap) (result : DeflateState) (next : Array UInt8),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds prepared) ∧
      dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      (outBits next result).length = (outBits buf d).length + 3 + prepared.opt_len.toNat ∧
      result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * 63488 := by
  obtain ⟨mb, ready, prepare, goodR, treesR, buffersR, _sizesR, _storageR, frameR, outputR, data⟩ :=
    all_trees_dynamic_data_engine (ob := 0) good trees buffers ledger clear trees.run.sym_next_le memory pending bits
  obtain ⟨costMb, costReady, costRun, _costTrees, cost⟩ := prepare_dynamic_wire_cost trees ledger clear
  have same : costReady = ready := Zlib.Trees.Proofs.same_record_of_runs costRun prepare
  have sameIndex : costMb = mb := (Prod.mk.inj (Except.ok.inj (costRun.symm.trans prepare))).1
  subst costReady
  subst costMb
  obtain ⟨codeMb, codeReady, codeRun, codes⟩ := Zlib.Trees.Proofs.prepare_source_code_facts trees
  have sameCode : codeReady = ready := Zlib.Trees.Proofs.same_record_of_runs codeRun prepare
  subst codeReady
  have memoryR : ready.lit_bufsize.toNat = 16384 := by rw [frameR]; exact memory
  have cursorR : ready.pending_out = ready.pending_buf := by rw [frameR]; exact cursor
  have packedR : PackedSymbols buf ready.lit_bufsize.toNat xs := by rw [frameR]; exact ledger.packed
  have countR : ready.sym_next.toNat = 3 * xs.length := by rw [frameR]; exact ledger.count
  obtain ⟨headerBuf, headerState, headerRun, goodH, treesH, buffersH, _sizesH, _storageH,
    diffH, _headerSize, cursorH, packedH, _headerDataH, roomH, outputH⟩ :=
    dynamic_header_engine (ob := 0) goodR treesR buffersR cursorR data packedR last
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
  obtain ⟨next, result, payloadRun, goodA, treesA, buffersA, _sizesA, _storageA, _diffA,
    _sizeA, cursorA, _codesA, roomA, outputA⟩ :=
    dynamic_payload_ready (ob := 0) goodH treesH buffersH cursorH memoryH ledger (codes.bitsDiff diffH) packedH roomH countH
  have output : outBits next result = outBits buf d ++
      (dynamicTag last ++ dynamicHeaderBits ready mb ++
        xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist)
          (s.distance, s.value)) ++ codeBits (sourceWords ready .lit) 256) := by
    rw [outputA, outputH, outputR, wordL, wordD]
    simp only [List.append_assoc]
  have length := congrArg List.length output
  simp only [List.length_append, dynamicTag, Zlib.Trees.Proofs.Out.natBits_length] at length
  have candidateSmall : (dynamicHeaderBits ready mb ++
        xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist)
          (s.distance, s.value)) ++ codeBits (sourceWords ready .lit) 256).length < 2 ^ 64 := by
    simp only [List.length_append]
    rw [outBits_length] at length
    omega
  have counter : ready.opt_len.toNat = (dynamicHeaderBits ready mb ++
        xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist)
          (s.distance, s.value)) ++ codeBits (sourceWords ready .lit) 256).length := by
    rw [cost, UInt64.toNat_ofNat', Nat.mod_eq_of_lt candidateSmall]
  refine ⟨mb, ready, _, result, next, prepare, ?_, goodA, treesA, buffersA, ?_, cursorA, roomA⟩
  · unfold dynamicPreparedPayload
    rw [← M_bind_assoc, bind_app, prepare]
    simp only [bind_app, headerRun, Zlib.Trees.Proofs.Out.pLtree_run goodH.live.hs,
      Zlib.Trees.Proofs.Out.pDtree_run goodH.live.hs]
    exact payloadRun
  · rw [counter]
    simp only [List.length_append]
    omega

/-- The complete actual prepared dynamic fragment, including reset and
optional final alignment, is bounded by the rounded candidate used by
block selection. Both final flags and every allowed entry bit offset are
included. Selecting this candidate and accumulating actual blocks across
the utility history remain separate obligations. -/
theorem dynamic_prepared_block_byte_count {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (last : Bool) :
    ∃ (mb : Int32) (prepared : DeflateState) (after : Heap) (result : DeflateState) (next : Array UInt8),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds prepared) ∧
      (do dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧
      ((outBits next result).length + 7) / 8 ≤
        ((outBits buf d).length + 7) / 8 + (prepared.opt_len.toNat + 10) / 8 ∧
      (last = true → result.bi_valid.toInt = 0) := by
  obtain ⟨mb, prepared, emittedHeap, emitted, emittedBuf, prepare, emit, goodE, treesE, buffersE,
    emittedCount, cursorE, roomE⟩ :=
    dynamic_prepared_payload_bit_count good trees buffers cursor memory pending bits ledger clear last
  obtain ⟨otherMb, otherReady, otherHeap, other, otherBuf, otherRun, otherGood, otherTrees,
    _otherBuffers, _sizes, _storage, _frame, _codesR, _headerData, _codesA, size, _cursor, _room, _output⟩ :=
    dynamic_prepared_payload_engine (ob := 0) good trees buffers cursor memory pending bits ledger clear last
  have heapEq : otherHeap = emittedHeap := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans emit))).2
  rw [heapEq] at otherGood otherTrees
  have stateEq : other = emitted := Option.some.inj (otherGood.live.hs.symm.trans goodE.live.hs)
  rw [stateEq] at otherTrees
  have bufferEq : otherBuf = emittedBuf := Option.some.inj (otherTrees.base.bytes.symm.trans treesE.base.bytes)
  rw [bufferEq] at size
  obtain ⟨a1, a2, a3, reset, resetRun, goodR, treesR, buffersR, _sizesR, _storageR,
    resetFields, _ledgerR, resetBits⟩ := init_block_engine (ob := 0) goodE treesE buffersE
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [resetFields, size]
    change 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * 65536
    omega
  have countR : (outBits emittedBuf reset).length = (outBits buf d).length + 3 + prepared.opt_len.toNat := by
    rw [resetBits]
    exact emittedCount
  have rounded : ((outBits emittedBuf reset).length + 7) / 8 ≤
      ((outBits buf d).length + 7) / 8 + (prepared.opt_len.toNat + 10) / 8 := by
    rw [countR]
    have bound := ZlibF.Math.DeflateBound.ceil_bytes_append (outBits buf d).length (3 + prepared.opt_len.toNat)
    omega
  cases last with
  | false =>
    change dynamicPreparedPayload (some (.tab ds)) 0 h = .ok ((), emittedHeap) at emit
    refine ⟨mb, prepared, _, reset, emittedBuf, prepare, ?_, goodR, treesR, rounded, by simp⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, emit, resetRun, show ((0 : Int32) != 0) = false from rfl,
      Bool.false_eq_true, ite_false, pure_app]
  | true =>
    change dynamicPreparedPayload (some (.tab ds)) 1 h = .ok ((), emittedHeap) at emit
    obtain ⟨next, result, windupRun, goodA, treesA, _buffersA, _sizesA, _storageA,
      _fieldsA, _sizeA, _pendingA, zeroA, _wordA, _cursorA, outputA⟩ :=
      windup_engine (ob := 0) goodR treesR buffersR cursorR roomR
    have windupCount := congrArg List.length outputA
    simp only [List.length_append, List.length_replicate, outBits_length] at windupCount
    have sameRounded : ((outBits next result).length + 7) / 8 =
        ((outBits emittedBuf reset).length + 7) / 8 := by
      rw [outBits_length, outBits_length]
      omega
    refine ⟨mb, prepared, _, result, next, prepare, ?_, goodA, treesA,
      by rw [sameRounded]; exact rounded, by intro _; exact zeroA⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, emit, resetRun, show ((1 : Int32) != 0) = true from rfl,
      ite_true, windupRun]

end Zlib.Deflate.Engine.Proofs
