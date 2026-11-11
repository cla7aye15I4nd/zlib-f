import ZlibF.Proof.«deflate.c.engine.fixed-block»
import ZlibF.Proof.«deflate.c.engine.fixed-payload»
import ZlibF.Proof.«deflate.c.engine.block-clear-preserve»

/-!
# trees.c: the fixed-code branch of a block flush, for every memLevel

Batch C of the deflate skeleton. `compress_block` with the static trees, then `init_block`
and, for the last block, `bi_windup`. The output room is derived from the recorded symbols
alone: at most 31 bits per symbol (`fixedPayloadPrefix_length`), three tag bits and the
seven-bit end code. With `n ≤ lit_bufsize - 1` symbols and `4 * lit_bufsize` pending bytes this
always fits, at every memLevel; the overlay of the unread symbols is the per-symbol bound inside
`compress_block_fixed_emit`.
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt fixedTag)
set_option autoImplicit false

/-- `compress_block(s, static_ltree, static_dtree)` on the recorded symbols, from a drained
entry with at most ten held bits, at any memLevel. The written bits are counted exactly. -/
theorem fixed_payload_safe {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 10)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) :
    ∃ next result,
      let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.compress_block (some (.tab ds)) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) h =
        .ok ((), ready) ∧
      DGood ready r ds z result ∧ TreesInvAt ready ds result pb next ∧ StreamBuffers ready r ∧
      ByteSizes h ready ∧ OutputStorage h ready r ds pb ob ∧ Zlib.Trees.Proofs.Out.BitsDiff d result ∧
      next.size = buf.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤
        d.bi_valid.toInt.toNat + 31 * xs.length + 7 ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits
          Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)) ++
          Zlib.Trees.Proofs.Out.codeBits Zlib.Trees.Proofs.fixedLiteralWords 256) := by
  have legal := packed_payload_legal packed valid
  obtain ⟨next, result, run, treesA, output, size, _frame, _lower, _upper, fields⟩ :=
    Zlib.Trees.Proofs.compress_block_fixed_emit trees pending bits xs.length count legal
  have goodA := output_bits_good good cursor trees.base.bytes size fields treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size fields treesA
  have sizes := output_bits_sizes good trees.base.bytes size fields
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have length := Zlib.Trees.Proofs.fixedPayloadPrefix_length buf d.lit_bufsize.toNat xs.length legal
  have bitCount := congrArg List.length output
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append, Zlib.Trees.Proofs.Out.codeBits,
    Zlib.Trees.Proofs.fixed_literal_end, Zlib.Trees.Proofs.Out.natBits_length,
    show (7 : UInt16).toNat = 7 from rfl, pending, UInt64.toNat_zero] at bitCount
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨_, _, _, _, equal⟩ := fields
    rw [equal]
    exact cursor
  have bound : 8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤
      d.bi_valid.toInt.toNat + 31 * xs.length + 7 := by omega
  rw [packed_fixed_payload_bits packed valid] at output
  exact ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, fields, size, cursorA, bound, output⟩

/-- The selected fixed branch and the common tail of `_tr_flush_block` (tag, payload,
`init_block`, and `bi_windup` for the last block), from a drained entry with at most seven held
bits, at any memLevel. The pending bytes stay within `pending_buf` and leave two bytes for the
final alignment. -/
theorem fixed_block_safe {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (last : Bool) :
    ∃ after result next,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ SymbolLedger next result [] ∧
      BlockOutputFrame d result ∧ BlockInit.BlockClear result ∧ next.size = buf.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 31 * xs.length + 33 ∧
      (last = true → result.bi_valid.toInt = 0) := by
  obtain ⟨tagged, headerRun, goodH, treesH, buffersH, sizesH, storageH, diffH,
    pendingH, bitsH, cursorH, _outputH⟩ :=
    fixed_header_engine (ob := ob) good trees buffers cursor pending bits last
  obtain ⟨_p, _a, _v, _u, fieldsH⟩ := diffH
  obtain ⟨emittedBuf, emitted, payloadRun, goodE, treesE, buffersE, sizesE, storageE,
    fieldsE, sizeE, cursorE, boundE, _outputE⟩ :=
    fixed_payload_safe (ob := ob) goodH treesH buffersH cursorH pendingH bitsH
      (by rw [fieldsH]; exact count) (by rw [fieldsH]; exact packed) valid
  obtain ⟨a1, a2, a3, reset, resetRun, goodR, treesR, buffersR, sizesR, storageR, resetFields,
    ledgerR, resetBits⟩ := init_block_engine (ob := ob) goodE treesE buffersE
  obtain ⟨clearReset, clearRun, _goodC, _treesC, _buffersC, _sizesC, _storageC, _ledgerC, clearR,
    _bitsC⟩ := init_block_clear_engine (ob := ob) goodE treesE buffersE
  have sameReset : clearReset = reset := Zlib.Trees.Proofs.same_record_of_runs clearRun resetRun
  rw [sameReset] at clearR
  have frameR : BlockOutputFrame d reset := by
    obtain ⟨_, _, _, _, emittedFields⟩ := fieldsE
    unfold BlockOutputFrame
    rw [resetFields, emittedFields, fieldsH]
    rfl
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have countR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 31 * xs.length + 17 := by
    have resetLength := congrArg List.length resetBits
    simp only [Zlib.Trees.Proofs.Out.outBits_length] at resetLength
    have lowH := treesH.run.bi_lo
    omega
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have sizeBuf : buf.size = 4 * d.lit_bufsize.toNat := trees.base.size
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [sizeE, sizeBuf]
    omega
  have sizes := (sizesH.trans sizesE).trans sizesR
  have storage := (storageH.trans storageE).trans storageR
  cases last with
  | false =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 0 h = .ok ((), setD h ds tagged) at headerRun
    refine ⟨_, reset, emittedBuf, ?_, goodR, treesR, buffersR, sizes, storage, ledgerR, frameR, clearR,
      sizeE, cursorR, by omega, by simp⟩
    unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, headerRun, payloadRun, resetRun,
      show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ite_false, pure_app]
  | true =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 1 h = .ok ((), setD h ds tagged) at headerRun
    obtain ⟨next, result, windupRun, goodA, treesA, buffersA, sizesA, storageA, fieldsA,
      sizeA, pendingA, zeroA, _wordA, cursorA, _outputA⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR roomR
    refine ⟨_, result, next, ?_, goodA, treesA, buffersA, sizes.trans sizesA,
      storage.trans storageA, empty_ledger_bits ledgerR fieldsA, frameR.bits fieldsA, clearR.bits fieldsA, sizeA.trans sizeE,
      cursorA, ?_, fun _ => zeroA⟩
    · unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
      simp only [bind_app, headerRun, payloadRun, resetRun,
        show ((1 : Int32) != 0) = true from rfl, ite_true, windupRun]
    · rw [zeroA]
      omega

end Zlib.Deflate.Universal.Block
