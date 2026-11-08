import ZlibF.Proof.«deflate.c.engine.loop-input-ledger»
import ZlibF.Proof.«deflate.c.engine.no-flush-loop-control»
import ZlibF.Proof.«deflate.c.engine.finish-stream-encoding»

/-! # Actual NO_FLUSH encoding and checksum match the consumed caller input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The actual complete NO_FLUSH strategy call returns need_more and an
exact final-heap caller slice. Its accepted logical input is exactly the old prefix followed by the consumed original caller bytes. It preserves cumulative independent block
meaning and the actual held-bit position through any number of refills,
slides and full computed block publications. The incoming mathematical
encoding history is not a callee contract. Zero and positive strategy-entry output are admitted. Public wrappers, pending
resumption and legal caller replacement remain separate obligations. -/
theorem deflate_slow_no_flush_ready_stream_encoding_input {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {before completed : List Bool} {previous : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (held : PendingBits h d before)
    (wirePrefix : ZlibF.Spec.bytesToBits previous ++ before = completed)
    (prefixMeaning : BlockPrefix [] 0 [] completed (inputPrefix input base)) :
    ∃ used after z' result extended nextOrigin base' ys written remaining encoded,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits (previous ++ written) ++ remaining = encoded ∧
      BlockPrefix [] 0 [] encoded (inputPrefix extended base') ∧
      encoded.length % 8 = result.bi_valid.toInt.toNat % 8 ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  have ready := publish
  have position : completed.length % 8 = d.bi_valid.toInt.toNat % 8 := by
    have count := congrArg List.length wirePrefix
    have pendingLength := pending_bits_exact_length held
    simp only [List.length_append, encoded_bytes_length] at count
    omega
  obtain ⟨final, after, used, z', result, extended, nextOrigin, base', ys, beforeL, written,
      remaining, blockBits, loopRun, stateA, endA, buffersA, accountA, agreesA, endpointA,
      baseA, pendingBefore, bytesA, pendingA, wireA, prefixA, positionA, checksumA, inputLedgerA⟩ :=
    slow_loop_ready_block_prefix_input (flush := Z_NO_FLUSH) (offset := completed.length) boundary frontier buffers
      positive pointer memory wrap publish inputValid snapshot checksum position
  have returned := slow_no_flush_loop_run_control boundary frontier buffers positive pointer memory wrap ready inputValid loopRun
  have actual : deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) := by
    rw [deflate_slow_eof_tail_source, bind_app, loopRun]
    simp only [returned, pure_app]
  have beforeEq : beforeL = before :=
    (pending_bits_zero_value ready.1 pendingBefore).trans (pending_bits_zero_value ready.1 held).symm
  rw [beforeEq] at wireA
  have wire : ZlibF.Spec.bytesToBits (previous ++ written) ++ remaining = completed ++ blockBits := by
    simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wireA wirePrefix ⊢
    rw [wireA, ← List.append_assoc, wirePrefix]
  have stepMeaning : BlockPrefix [] (0 + completed.length) (inputPrefix input base) blockBits (inputPrefix extended base') := by
    simpa only [Nat.zero_add] using prefixA
  exact ⟨used, after, z', result, extended, nextOrigin, base', ys, written, remaining, completed ++ blockBits,
    actual, stateA, endA, buffersA, accountA, bytesA, agreesA, endpointA, baseA, pendingA,
    wire, block_prefix_append prefixMeaning stepMeaning, by simpa only [List.length_append] using positionA, checksumA, inputLedgerA⟩

end Zlib.Deflate.Engine.Proofs
