import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-input-phase»
import ZlibF.Proof.«deflate.c.engine.finish-raw-input-phase»

/-! # Raw encoding and checksum describe the exact consumed caller input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The complete actual FINISH strategy either preserves the raw prefix
at an early output stop or completes a valid raw stream, with the exact
remaining pending bytes included. The independent raw format and checksum use the original caller snapshot, not an existential logical input. Both alternatives share one actual run. -/
theorem default_foreign_deflate_slow_finish_ready_raw_input_phase {h : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base' ys ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      inputPrefix extended (origin + fillEnd d + used) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d) ++ actualInput.take used)).toUInt64 ∧
      ((rc = need_more ∧ StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧
        EndFrontier after result ∧ nextOrigin + fillEnd result = origin + fillEnd d + used ∧ RawPrefix after result extended base' (published ++ written)) ∨
       ((rc = finish_started ∨ rc = finish_done) ∧ ∃ tailBytes,
        Bytes after result.pending_out result.pending.toNat tailBytes ∧ result.bi_valid.toInt.toNat = 0 ∧
        ZlibF.Spec.Deflate.Valid (inputPrefix input (origin + fillEnd d) ++ actualInput.take used)
          (published ++ written ++ tailBytes))) := by
  obtain ⟨before, completed, held, wire, meaning⟩ := encoding
  obtain ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
      run, stateA, buffersA, accountA, bytesA, agreesA, inputLedgerA, checksumA, casesA⟩ :=
    default_foreign_deflate_slow_finish_ready_stream_input_phase boundary frontier buffers positive pointer memory wrap publish inputValid snapshot checksum held wire meaning
  refine ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
    run, stateA, buffersA, accountA, bytesA, agreesA, inputLedgerA, by simpa only [inputLedgerA] using checksumA, ?_⟩
  rcases casesA with ⟨returned, remaining, encoded, strategyA, endA, endpointA, pendingA, wireA, meaningA, _positionA⟩ | done
  · exact Or.inl ⟨returned, strategyA, endA, endpointA, remaining, encoded, pendingA, wireA, meaningA⟩
  · rcases done with ⟨returned, tailBytes, pendingA, finalA, validA⟩
    exact Or.inr ⟨returned, tailBytes, pendingA, finalA, by simpa only [inputLedgerA] using validA⟩

end Zlib.Deflate.Engine.Proofs
