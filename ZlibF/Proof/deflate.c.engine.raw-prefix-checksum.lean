import ZlibF.Proof.«deflate.c.engine.raw-prefix»
import ZlibF.Proof.«deflate.c.engine.finish-encoding-checksum»
import ZlibF.Proof.«deflate.c.engine.no-flush-encoding-checksum»

/-! # Raw encoding and checksum meaning coexist at every prepared capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The complete actual NO_FLUSH strategy preserves the initialized raw
encoding invariant while extending both accepted input and published bytes. -/
theorem deflate_slow_no_flush_ready_raw_prefix_adler {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      RawPrefix after result extended base' (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 := by
  obtain ⟨before, completed, held, wire, meaning⟩ := encoding
  obtain ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
      remaining, encoded, run, stateA, endA, buffersA, accountA, bytesA,
      agreesA, endpointA, baseA, pendingA, wireA, meaningA, _positionA, checksumA⟩ :=
    deflate_slow_no_flush_ready_stream_encoding_adler boundary frontier buffers positive pointer memory wrap publish inputValid checksum held wire meaning
  exact ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
    run, stateA, endA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
    ⟨remaining, encoded, pendingA, wireA, meaningA⟩, checksumA⟩

/-- The complete actual FINISH strategy either preserves the raw prefix
at an early output stop or completes a valid raw stream, with the exact
remaining pending bytes included. Both alternatives share one actual run. -/
theorem deflate_slow_finish_ready_raw_prefix_adler {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base' ys ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (origin + fillEnd d + used))).toUInt64 ∧
      ((rc = need_more ∧ StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧
        EndFrontier after result ∧ RawPrefix after result extended base' (published ++ written)) ∨
       ((rc = finish_started ∨ rc = finish_done) ∧ ∃ tailBytes,
        Bytes after result.pending_out result.pending.toNat tailBytes ∧ result.bi_valid.toInt.toNat = 0 ∧
        ZlibF.Spec.Deflate.Valid (inputPrefix extended (origin + fillEnd d + used))
          (published ++ written ++ tailBytes))) := by
  obtain ⟨before, completed, held, wire, meaning⟩ := encoding
  obtain ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
      run, stateA, buffersA, accountA, bytesA, agreesA, checksumA, casesA⟩ :=
    deflate_slow_finish_ready_stream_encoding_adler boundary frontier buffers positive pointer memory wrap publish inputValid checksum held wire meaning
  refine ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
    run, stateA, buffersA, accountA, bytesA, agreesA, checksumA, ?_⟩
  rcases casesA with ⟨returned, remaining, encoded, strategyA, endA, pendingA, wireA, meaningA, _positionA⟩ | done
  · exact Or.inl ⟨returned, strategyA, endA, remaining, encoded, pendingA, wireA, meaningA⟩
  · exact Or.inr done

end Zlib.Deflate.Engine.Proofs
