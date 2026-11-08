import ZlibF.Proof.«deflate.c.engine.public-nonfinal-data-encoding»
import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»
import ZlibF.Proof.«deflate.c.engine.public-block-effects»

/-! # All nonfinal data paths retain their exact caller output interval -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The same actual nonfinal data execution has exact cumulative encoding
and the caller write interval needed to preserve earlier pending output.
The interval follows from proved execution effects of each concrete flag.
No caller or callee output frame is assumed. -/
theorem public_busy_nonfinal_data_raw_prefix_input_interval {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
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
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      RawOutputInterval h after ob oo written.length := by
  obtain ⟨used, after, z', result, extended, nextOrigin, nextBase, ys, written,
      run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
      statusA, lastA, encodingA, checksumA, inputLedgerA⟩ :=
    public_busy_nonfinal_data_raw_prefix_input boundary buffers status level strategy pointer memory wrap publish
      inputValid flush flag snapshot checksum encoding
  have interval : RawOutputInterval h after ob oo written.length := by
    have partialSync : (flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH) → RawOutputInterval h after ob oo written.length := by
      intro alternatives
      obtain ⟨_used, _other, _otherZ, _otherD, _nextInput, _nextOrigin, _nextBase, _symbols, _written,
          actual, otherState, _buffers, otherAccount, _bytes, _agrees, _endpoint, _base,
          _status, _last, _encoding, _checksum, _ledger, effect⟩ :=
        public_busy_partial_sync_data_raw_prefix_input_interval (boundary.strategy publish) boundary.end_frontier buffers
          status level strategy pointer memory wrap publish inputValid flush alternatives snapshot checksum encoding
      exact RawOutputInterval.identify actual run otherState.good.live.hz stateA.good.live.hz otherAccount accountA effect
    rcases flag with ordinary | partialFlag | sync | full | block
    · subst flush
      obtain ⟨_used, _produced, _other, _otherZ, _otherD, actual, otherGood, otherAccount,
          _inputEffect, _outputEffect, effect⟩ :=
        public_busy_slow_no_flush_output_execution boundary buffers status level strategy pointer memory wrap publish inputValid
      exact RawOutputInterval.identify actual run otherGood.live.hz stateA.good.live.hz otherAccount accountA effect
    · exact partialSync (Or.inl partialFlag)
    · exact partialSync (Or.inr sync)
    · subst flush
      obtain ⟨_used, _other, _otherZ, _otherD, _nextInput, _nextOrigin, _nextBase, _symbols, _written,
          actual, otherState, _buffers, otherAccount, _bytes, _agrees, _endpoint, _base,
          _status, _last, _encoding, _checksum, _ledger, effect⟩ :=
        public_busy_full_data_raw_prefix_input_interval (boundary.strategy publish) boundary.end_frontier buffers
          status level strategy pointer memory wrap publish inputValid snapshot checksum encoding
      exact RawOutputInterval.identify actual run otherState.good.live.hz stateA.good.live.hz otherAccount accountA effect
    · subst flush
      obtain ⟨_used, _produced, _other, _otherZ, _otherD, actual, otherGood, _buffers, otherAccount,
          _inputEffect, _outputEffect, effect, _storage⟩ :=
        public_busy_slow_block_effect_execution (boundary.strategy publish) boundary.end_frontier buffers
          status level strategy pointer memory wrap publish inputValid
      exact RawOutputInterval.identify actual run otherGood.live.hz stateA.good.live.hz otherAccount accountA effect
  exact ⟨used, after, z', result, extended, nextOrigin, nextBase, ys, written,
    run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
    statusA, lastA, encodingA, checksumA, inputLedgerA, interval⟩

end Zlib.Deflate.Engine.Proofs
