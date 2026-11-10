import ZlibF.Proof.«deflate.c.engine.memory-four-dynamic-format»
import ZlibF.Proof.«deflate.c.engine.dynamic-block»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (dynamicTag)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual dynamic emission, reset and final windup preserve the empty
next-block ledger and the independent body grammar at memory four. -/
theorem mem_four_dynamic_prepared_block_ready {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (capacity : d.lit_bufsize.toNat = 1024)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs) (last : Bool) :
    ∃ after result next body padding,
      (do dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧
      next.size = buf.size ∧ result.pending.toNat ≤ next.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size ∧
      (last = true → result.bi_valid.toInt = 0 ∧ result.bi_buf = 0) ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (dynamicTag last ++ body ++ padding) ∧
      ∀ suffix, ZlibF.Spec.Body [] 2 (inputPrefix input base) (body ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨emittedHeap, emitted, emittedBuf, body, emittedRun, goodE, treesE, buffersE,
    sizesE, storageE, sizeE, cursorE, roomE, outputE, grammar⟩ :=
    mem_four_dynamic_prepared_payload_format (ob := ob) good trees buffers cursor capacity pending bits ledger clear trace last
  obtain ⟨reset, resetRun, goodR, treesR, buffersR, sizesR, storageR, ledgerR, clearR, resetBits⟩ :=
    init_block_clear_engine (ob := ob) goodE treesE buffersE
  obtain ⟨a1, a2, a3, reset2, resetRun2, _good2, _trees2, _buffers2, _sizes2, _storage2,
    resetFields, _ledger2, _output2⟩ := init_block_engine (ob := ob) goodE treesE buffersE
  have same : reset2 = reset := Zlib.Trees.Proofs.same_record_of_runs resetRun2 resetRun
  rw [same] at resetFields
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat + 7 ≤ 8 * reset.pending_buf_size.toNat := by
    rw [resetFields]
    exact roomE
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have bitsR := resetBits.trans outputE
  have sizes := sizesE.trans sizesR
  have storage := storageE.trans storageR
  have physicalRoom : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    have physicalSize := treesR.base.psize
    omega
  cases last with
  | false =>
    change dynamicPreparedPayload (some (.tab ds)) 0 h = .ok ((), emittedHeap) at emittedRun
    refine ⟨_, reset, emittedBuf, body, [], ?_, goodR, treesR, buffersR, sizes, storage,
      ledgerR, clearR, sizeE, by omega, cursorR, physicalRoom, by simp, by decide, by simp, ?_, grammar⟩
    · unfold Zlib.Trees.Proofs.flushBlockTail
      simp only [bind_app, emittedRun, resetRun, show ((0 : Int32) != 0) = false from rfl,
        Bool.false_eq_true, ite_false, pure_app]
    · simpa only [List.append_nil] using bitsR
  | true =>
    change dynamicPreparedPayload (some (.tab ds)) 1 h = .ok ((), emittedHeap) at emittedRun
    obtain ⟨next, result, windupRun, goodA, treesA, buffersA, sizesA, storageA, diffA,
      sizeA, _pendingA, zeroA, wordA, cursorA, outputA⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR physicalRoom
    let padding := List.replicate ((8 - reset.bi_valid.toInt.toNat % 8) % 8) false
    have padBound : padding.length < 8 := by
      simpa only [padding, List.length_replicate] using Nat.mod_lt (8 - reset.bi_valid.toInt.toNat % 8) (by decide : 0 < 8)
    have bitCount := congrArg List.length outputA
    change (Zlib.Trees.Proofs.Out.outBits next result).length =
      (Zlib.Trees.Proofs.Out.outBits emittedBuf reset ++ padding).length at bitCount
    simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append] at bitCount
    have bound : result.pending.toNat ≤ next.size := by
      have bound := treesA.base.pending_le
      have physicalSize := treesA.base.psize
      omega
    have size : next.size = buf.size := sizeA.trans sizeE
    have physical : 8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size := by
      rw [zeroA]
      change 8 * result.pending.toNat ≤ 8 * next.size
      omega
    refine ⟨_, result, next, body, padding, ?_, goodA, treesA, buffersA,
      sizes.trans sizesA, storage.trans storageA, empty_ledger_bits ledgerR diffA, clearR.bits diffA,
      size, bound, cursorA, physical, by intro _; exact ⟨zeroA, wordA⟩, padBound, by simp, ?_, grammar⟩
    · unfold Zlib.Trees.Proofs.flushBlockTail
      simp only [bind_app, emittedRun, resetRun, show ((1 : Int32) != 0) = true from rfl,
        ite_true, windupRun]
    · rw [outputA, bitsR]
      simp only [padding, List.append_assoc]

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.mem_four_dynamic_prepared_block_ready
