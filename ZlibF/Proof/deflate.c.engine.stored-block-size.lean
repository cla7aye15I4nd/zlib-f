import ZlibF.Proof.«deflate.c.engine.stored-block»
import ZlibF.Math.DeflateStreamBudget

/-! # Rounded cost of actual stored blocks and the common tail -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt outBits outBits_length)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual reset and optional windup leave the rounded output potential
unchanged. Both real tail branches participate in this execution. -/
theorem flush_tail_ceil_bytes {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) (last : Bool) :
    ∃ after result next,
      Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧
      ((outBits next result).length + 7) / 8 = ((outBits buf d).length + 7) / 8 := by
  obtain ⟨a1, a2, a3, reset, resetRun, goodR, treesR, buffersR, _sizesR, _storageR,
    resetFields, _ledgerR, outputR⟩ := init_block_engine (ob := 0) good trees buffers
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursor
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * buf.size := by
    rw [resetFields]; exact room
  cases last with
  | false =>
    refine ⟨_, reset, buf, ?_, goodR, treesR, by rw [outputR]⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, resetRun, show ((0 : Int32) != 0) = false from rfl,
      Bool.false_eq_true, ite_false, pure_app]
  | true =>
    obtain ⟨next, result, windRun, goodA, treesA, _buffersA, _sizesA, _storageA,
      _diffA, _sizeA, _pendingA, zeroA, _wordA, _cursorA, outputA⟩ :=
      windup_engine (ob := 0) goodR treesR buffersR cursorR roomR
    have count := congrArg List.length outputA
    simp only [List.length_append, List.length_replicate, outBits_length] at count
    have same : ((outBits next result).length + 7) / 8 = ((outBits buf reset).length + 7) / 8 := by
      rw [outBits_length, outBits_length]
      omega
    refine ⟨_, result, next, ?_, goodA, treesA, by rw [same, outputR]⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, resetRun, show ((1 : Int32) != 0) = true from rfl, ite_true, windRun]

/-- The actual stored writer, reset and final alignment add at most
represented input plus five rounded bytes. The bytes are the real window
slice. Whole selection and block-history counting remain separate. -/
theorem stored_block_byte_count {h : Heap} {r : ZStreamRef} {ds pb w origin base : Nat}
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
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧
      ((outBits next result).length + 7) / 8 ≤ ((outBits buf d).length + 7) / 8 + represented xs + 5 := by
  obtain ⟨emittedBuf, emitted, emitRun, goodE, treesE, buffersE, _sizesE, _storageE, _diffE,
    sizeE, cursorE, alignedE, pendingE, outputE, _grammar⟩ :=
    stored_payload_engine (ob := 0) good trees buffers cursor memory pending bits win get range nonnegative
      balance accounted view selectedRoom last
  have roomE : 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [alignedE, sizeE]
    change 8 * emitted.pending.toNat ≤ 524288
    omega
  obtain ⟨after, result, next, tailRun, goodA, treesA, sameRounded⟩ :=
    flush_tail_ceil_bytes goodE treesE buffersE cursorE roomE last
  refine ⟨after, result, next, by rw [bind_app, emitRun]; exact tailRun, goodA, treesA, ?_⟩
  rw [sameRounded, outputE]
  simp only [List.length_append, Zlib.Trees.Proofs.Out.storedTag, Zlib.Trees.Proofs.Out.storedBodyBits,
    Zlib.Trees.Proofs.Out.natBits_length, List.length_replicate,
    Zlib.Trees.Proofs.Out.stored_bytes_length, Zlib.Trees.Proofs.Out.sourceBytes_length, outBits_length]
  have bounded : d.bi_valid.toInt.toNat ≤ 7 := by omega
  omega

end Zlib.Deflate.Engine.Proofs
