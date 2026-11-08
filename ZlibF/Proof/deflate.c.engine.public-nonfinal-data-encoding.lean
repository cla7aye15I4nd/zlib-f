import ZlibF.Proof.«deflate.c.engine.public-partial-sync-data-encoding»
import ZlibF.Proof.«deflate.c.engine.public-full-data-encoding»
import ZlibF.Proof.«deflate.c.engine.public-block-data-encoding»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-input»

/-! # All valid nonfinal public data paths share one exact encoding contract -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every valid non-FINISH data dispatch has the same input/output
refinement. NO_FLUSH includes the actual inactive branch. Other flags
include EOF, marker/reset effects and retry stores. Every strategy-entry
capacity is covered; no public entry guard is assumed as a contract. -/
theorem public_busy_nonfinal_data_raw_prefix_input {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flag : flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨
      flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used after z' result extended nextOrigin nextBase ys written,
      publicDataTail (some r) (some (.tab ds)) flush h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      result.status = BUSY_STATE ∧ (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      RawPrefix after result extended nextBase (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  rcases flag with ordinary | partialFlag | sync | full | block
  · subst flush
    obtain ⟨used, after, z', result, extended, nextOrigin, nextBase, ys, written,
        run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
        statusA, lastA, encodingA, checksumA, inputLedgerA⟩ :=
      public_busy_no_flush_data_ready_raw_prefix_input boundary buffers status level strategy pointer memory wrap publish inputValid snapshot checksum encoding
    exact ⟨used, after, z', result, extended, nextOrigin, nextBase, ys, written,
      run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA, statusA, lastA.symm,
      encodingA, checksumA, inputLedgerA⟩
  · subst flush
    exact public_busy_partial_sync_data_raw_prefix_input (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid Z_PARTIAL_FLUSH (Or.inl rfl) snapshot checksum encoding
  · subst flush
    exact public_busy_partial_sync_data_raw_prefix_input (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid Z_SYNC_FLUSH (Or.inr rfl) snapshot checksum encoding
  · subst flush
    exact public_busy_full_data_raw_prefix_input (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid snapshot checksum encoding
  · subst flush
    exact public_busy_block_data_raw_prefix_input (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid snapshot checksum encoding

end Zlib.Deflate.Engine.Proofs
