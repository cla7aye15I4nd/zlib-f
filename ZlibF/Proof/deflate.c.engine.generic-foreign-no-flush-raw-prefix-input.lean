import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-joint-input-encoding»
import ZlibF.Proof.«deflate.c.engine.raw-prefix-ready»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The complete actual NO_FLUSH strategy preserves the initialized raw
encoding invariant while extending both accepted input and published bytes. -/
theorem default_foreign_deflate_slow_no_flush_ready_raw_prefix_input {h : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (encoding : RawPrefix h d input base published)
    (checksum : z.adler=(ZlibF.Spec.adler32 (inputPrefix input (origin+fillEnd d))).toUInt64) :
    ∃ used after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      RawPrefix after result extended base' (published ++ written) ∧
      z'.adler=(ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin+fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin+fillEnd result)=inputPrefix input (origin+fillEnd d)++actualInput.take used := by
  obtain ⟨before, completed, held, wire, meaning⟩ := encoding
  obtain ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
      remaining, encoded, run, stateA, buffersA, accountA, bytesA,
      agreesA, endpointA, baseA, pendingA, wireA, meaningA, _positionA,adlerA,inputLedgerA⟩ :=
    default_foreign_deflate_slow_no_flush_joint_input_encoding boundary frontier buffers positive pointer memory wrap publish inputValid snapshot held wire meaning checksum
  exact ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
    run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
    ⟨remaining, encoded, pendingA, wireA, meaningA⟩,adlerA,inputLedgerA⟩


end Zlib.Deflate.Engine.Proofs
