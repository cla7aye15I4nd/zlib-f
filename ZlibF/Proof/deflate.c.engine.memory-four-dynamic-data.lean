import ZlibF.Proof.«deflate.c.engine.memory-four-dynamic-budget»
import ZlibF.Proof.«deflate.c.engine.memory-dynamic-data»
import ZlibF.Proof.«deflate.c.engine.dynamic-data»

namespace Zlib.Deflate.Engine.Proofs.SmallMemory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (dynamicHeaderBits)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual memLevel-four preparation produces the existing generic writer
interface on the same heap, including actual pending_buf_size room. Header
format comes from actual construction and original EOB/BL initialization;
no emitter contract or numeric budget is assumed by the caller. -/
theorem mem_four_all_trees_dynamic_data_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (capacity : d.lit_bufsize.toNat = 1024)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb,setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ TreePreparationFrame d result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      MemoryDynamicWriteData result mb xs := by
  obtain ⟨mb,result,run,goodA,treesA,buffersA,sizes,storage,_lower,_upper,_guards,
    fields,output,headerSize,prefixRoom,blockRoom⟩ :=
    mem_four_dynamic_budget (ob := ob) good trees buffers ledger count capacity pending bits
  obtain ⟨otherMb,other,dataRun,data⟩ := Zlib.Trees.Proofs.prepare_header_data trees ledger.end_marker clear.bl
  have same : other = result := Zlib.Trees.Proofs.same_record_of_runs dataRun run
  have sameIndex : otherMb = mb := (Prod.mk.inj (Except.ok.inj (dataRun.symm.trans run))).1
  subst other otherMb
  have capacityA : result.lit_bufsize.toNat = 1024 := by rw [fields]; exact capacity
  have pendingSize : result.pending_buf_size.toNat = 4096 := by
    rw [treesA.base.psize,treesA.base.size,capacityA]
  have fullRoom : 8*result.pending.toNat+result.bi_valid.toInt.toNat+3+
      (dynamicHeaderBits result mb).length+(dynamicSymbolCosts result xs).sum+15+7 ≤
      8*result.pending_buf_size.toNat := by rw [pendingSize]; exact blockRoom
  exact ⟨mb,result,run,goodA,treesA,buffersA,sizes,storage,fields,output,
    data,headerSize,prefixRoom,fullRoom⟩

#print axioms mem_four_all_trees_dynamic_data_engine
end Zlib.Deflate.Engine.Proofs.SmallMemory
