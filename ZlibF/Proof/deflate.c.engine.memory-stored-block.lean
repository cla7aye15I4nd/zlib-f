import ZlibF.Proof.«deflate.c.engine.memory-stored-payload»
import ZlibF.Proof.«deflate.c.engine.stored-block»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt storedTag storedBodyBits sourceBytes)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual stored emission, reset and optional windup restore an empty
ledger and independent stored body using the actual allocation extent. -/
theorem memory_stored_block_ready {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (nonnegative : 0 ≤ d.block_start.toInt)
    (balance : BlockBalance d xs 0) (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (selectedRoom : represented xs + 6 ≤ buf.size) (lengthBound : represented xs < 65536) (last : Bool) :
    ∃ after result next body,
      (do Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat)
            (UInt64.ofNat (represented xs)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧
      next.size = buf.size ∧ result.pending.toNat ≤ next.size ∧ result.pending_out = result.pending_buf ∧
      result.bi_valid.toInt = 0 ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++ (storedTag last ++ body) ∧
      ∀ suffix : List Bool, suffix.length % 8 = 0 →
        ZlibF.Spec.Body [] 0 (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨emittedBuf, emitted, emitRun, goodE, treesE, buffersE, sizesE, storageE, diffE,
    sizeE, cursorE, alignedE, pendingE, outputE, grammar⟩ :=
    memory_stored_block_payload_engine (ob := ob) good trees buffers cursor pending bits win get range nonnegative
      balance accounted view selectedRoom lengthBound last
  let body := storedBodyBits ((8 - (d.bi_valid.toInt.toNat + 3) % 8) % 8)
    (sourceBytes window d.block_start.toInt.toNat (represented xs))
  obtain ⟨reset, resetRun, goodR, treesR, buffersR, sizesR, storageR, ledgerR, clearR, resetBits⟩ :=
    init_block_clear_engine (ob := ob) goodE treesE buffersE
  obtain ⟨a1, a2, a3, reset2, resetRun2, _good2, _trees2, _buffers2, _sizes2, _storage2,
    resetFields, _ledger2, _output2⟩ := init_block_engine (ob := ob) goodE treesE buffersE
  have same : reset2 = reset := Zlib.Trees.Proofs.same_record_of_runs resetRun2 resetRun
  rw [same] at resetFields
  have alignedR : reset.bi_valid.toInt = 0 := by rw [resetFields]; exact alignedE
  have pendingR : reset.pending.toNat ≤ emittedBuf.size := by rw [resetFields]; exact pendingE
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have physical : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [alignedR]
    change 8 * reset.pending.toNat ≤ 8 * emittedBuf.size
    omega
  have outputR := resetBits.trans outputE
  have sizes := sizesE.trans sizesR
  have storage := storageE.trans storageR
  cases last with
  | false =>
    change Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat)
      (UInt64.ofNat (represented xs)) 0 h = .ok ((), _) at emitRun
    refine ⟨_, reset, emittedBuf, body, ?_, goodR, treesR, buffersR, sizes, storage,
      ledgerR, clearR, sizeE, pendingR, cursorR, alignedR, outputR, grammar⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, emitRun, resetRun, show ((0 : Int32) != 0) = false from rfl,
      Bool.false_eq_true, ite_false, pure_app]
  | true =>
    change Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat)
      (UInt64.ofNat (represented xs)) 1 h = .ok ((), _) at emitRun
    obtain ⟨next, result, windRun, goodA, treesA, buffersA, sizesA, storageA, diffA,
      sizeA, _pendingA, zeroA, _wordA, cursorA, outputA⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR physical
    have unchanged : Zlib.Trees.Proofs.Out.outBits next result =
        Zlib.Trees.Proofs.Out.outBits emittedBuf reset := by
      simpa only [alignedR, Int.toNat_zero, Nat.zero_mod, Nat.sub_zero,
        show 8 % 8 = 0 from rfl, List.replicate_zero, List.append_nil] using outputA
    have count := congrArg List.length unchanged
    simp only [Zlib.Trees.Proofs.Out.outBits_length, zeroA, alignedR, Int.toNat_zero, Nat.add_zero] at count
    have bound : result.pending.toNat ≤ next.size := by rw [sizeA]; omega
    refine ⟨_, result, next, body, ?_, goodA, treesA, buffersA, sizes.trans sizesA, storage.trans storageA,
      empty_ledger_bits ledgerR diffA, clearR.bits diffA, sizeA.trans sizeE, bound, cursorA, zeroA,
      unchanged.trans outputR, grammar⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, emitRun, resetRun, show ((1 : Int32) != 0) = true from rfl, ite_true, windRun]

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_stored_block_ready
