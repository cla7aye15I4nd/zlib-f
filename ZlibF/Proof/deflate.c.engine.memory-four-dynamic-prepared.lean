import ZlibF.Proof.«deflate.c.engine.memory-four-dynamic-data»
import ZlibF.Proof.«deflate.c.engine.memory-dynamic-payload»
import ZlibF.Proof.«deflate.c.engine.dynamic-prepared-payload»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (sourceWords SourceCodeFacts PreparedHeaderData dynamicHeaderBits dynamicTag)
open Zlib.Trees.Proofs.Out (TreesInvAt payloadSymBits codeBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual memLevel-four dynamic preparation, header and payload emission.
The exact 1024-symbol allocation supplies the complete budget through the
proved small-memory tree producer; no callee or numeric room contract is assumed. -/
theorem mem_four_dynamic_prepared_payload_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (capacity : d.lit_bufsize.toNat = 1024)
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
            codeBits (sourceWords ready .lit) 256) := by
  obtain ⟨mb, ready, prepare, goodR, treesR, buffersR, sizesR, storageR, frameR, outputR, data⟩ :=
    SmallMemory.mem_four_all_trees_dynamic_data_engine (ob := ob) good trees buffers ledger clear trees.run.sym_next_le capacity pending bits
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
  obtain ⟨next, result, payloadRun, goodA, treesA, buffersA, sizesA, storageA, _diffA,
    sizeA, cursorA, codesA, roomA, outputA⟩ :=
    memory_dynamic_payload_ready (ob := ob) goodH treesH buffersH cursorH ledger (codes.bitsDiff diffH) packedH roomH countH
  refine ⟨mb, ready, _, result, next, ?_, goodA, treesA, buffersA,
    (sizesR.trans sizesH).trans sizesA, (storageR.trans storageH).trans storageA,
    frameR, codes, data.header, codesA, sizeA.trans _headerSize, cursorA, roomA, ?_⟩
  · unfold dynamicPreparedPayload
    rw [← M_bind_assoc, bind_app, prepare]
    simp only [bind_app, headerRun, Zlib.Trees.Proofs.Out.pLtree_run goodH.live.hs,
      Zlib.Trees.Proofs.Out.pDtree_run goodH.live.hs]
    exact payloadRun
  · rw [outputA, outputH, outputR, wordL, wordD]
    simp only [List.append_assoc]

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.mem_four_dynamic_prepared_payload_engine
