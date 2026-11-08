import ZlibF.Proof.«deflate.c.engine.nonfinal-stream-input»
import ZlibF.Proof.«deflate.c.engine.raw-prefix»

/-! # Complete nonfinal strategy preserves the initialized raw representation -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual nonzero non-FINISH strategy advances RawPrefix
and Adler for the same consumed original caller input, including EOF and
short-output returns. This is the representation used by actual default
histories. Public marker emission and entry guards are separate. -/
theorem deflate_slow_nonfinal_ready_raw_prefix_input {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) (nonfinal : flush ≠ Z_FINISH)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) flush h = .ok (rc, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      RawPrefix after result extended base' (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      ((rc = need_more ∧ z'.avail_out = 0) ∨
       (rc = block_done ∧ z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.sym_next = 0)) := by
  obtain ⟨before, completed, held, wire, meaning⟩ := encoding
  obtain ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
      remaining, encoded, run, stateA, endA, buffersA, accountA, bytesA,
      agreesA, endpointA, baseA, pendingA, wireA, meaningA, _positionA, checksumA, inputLedgerA, returnsA⟩ :=
    deflate_slow_nonfinal_ready_stream_input boundary frontier buffers positive pointer memory wrap publish inputValid
      flush nonzero nonfinal snapshot checksum held wire meaning
  exact ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
    run, stateA, endA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
    ⟨remaining, encoded, pendingA, wireA, meaningA⟩, checksumA, inputLedgerA, returnsA⟩

end Zlib.Deflate.Engine.Proofs
