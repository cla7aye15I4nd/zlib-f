import ZlibF.Proof.«deflate.c.engine.no-flush-stream-encoding»
import ZlibF.Proof.«deflate.c.engine.pending-buffered»
import ZlibF.Proof.«deflate.c.engine.buffered-initial»

/-! # An initialized raw encoding invariant for publication and caller replacement -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Independent raw nonfinal-block meaning of already published bytes
and the actual remaining pending bits. This is the raw data phase; pending
wrapper header/trailer bytes have their separate public phases. The input
history and private representation are supplied by BufferedBoundary. -/
def RawPrefix (h : Heap) (d : DeflateState) (input : Nat → UInt8) (base : Nat)
    (published : List UInt8) : Prop :=
  ∃ remaining encoded, PendingBits h d remaining ∧
    ZlibF.Spec.bytesToBits published ++ remaining = encoded ∧
    BlockPrefix [] 0 [] encoded (inputPrefix input base)

/-- Legal caller replacement keeps the exact private raw pending sequence
and its independent meaning. Earlier published bytes are ghost history,
so the caller may reuse or replace the former public output buffer. -/
theorem RawPrefix.rebuffer {h g : Heap} {r : ZStreamRef} {ds base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {published : List UInt8}
    (encoding : RawPrefix h d input base published) (good : DGood h r ds z d)
    (edit : Rebuffer h g r) : RawPrefix g d input base published := by
  obtain ⟨remaining, encoded, pending, wire, meaning⟩ := encoding
  exact ⟨remaining, encoded, rebuffer_pending_bits good edit pending, wire, meaning⟩

/-- Actual pending publication advances the raw byte history without
changing the completed blocks' meaning. Base and advanced cursors, zero
capacity and partial drains are admitted. The initialized buffered boundary
and next strategy readiness coexist on the same returned heap. -/
theorem flush_pending_raw_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (encoding : RawPrefix h d input base published) :
    ∃ after z' result written,
      flush_pending (some r) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input origin base xs config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 written.length ∧ Bytes after z.next_out written.length written ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧
      RawPrefix after result input base (published ++ written) := by
  obtain ⟨before, encoded, pending, wire, meaning⟩ := encoding
  obtain ⟨_pb, produced, after, z', result, written, remaining, _base,
      run, stateA, buffersA, accountA, _sizes, _storage, _amount, _left, _fields,
      readyA, bytesA, pendingA, wireA⟩ :=
    flush_pending_buffered_boundary boundary buffers pointer pending
  have length := public_bytes_length bytesA
  have wireAll : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded := by
    simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wireA wire ⊢
    rw [wireA, wire]
  refine ⟨after, z', result, written, run, stateA, buffersA, ?_, ?_, readyA,
    remaining, encoded, pendingA, wireAll, meaning⟩
  · rw [length]; exact accountA
  · rw [length]; exact bytesA

/-- Actual successful default-parameter initialization establishes the raw
encoding invariant with no prior bytes or blocks. The engine/content and
EOF invariants are conclusions of that same execution. The universal Init2
contract and any engine or encoding invariant are not assumptions. Wrapper
header creation and allocation-failure safety remain separate results. -/
theorem default_initialization_raw_prefix {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      BufferedBoundary after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      StreamReachable .deflate after r ∧ RawPrefix after sf input 0 [] := by
  obtain ⟨after, zf, sf, run, start, boundary, frontier, _initial, reachable⟩ :=
    default_initialization_end_frontier hf hu hg hz ha hv params alloc input
  have stateA := boundary.buffered frontier (fun _ => start.pendingOut)
  obtain ⟨_pb, _buf, trees, _ledger, _balance⟩ := boundary.symbols
  have held := pending_bits_base trees start.pendingOut
  have empty := pending_bits_empty held (by rw [start.pending]; rfl) (by rw [start.bits]; rfl)
  rw [empty] at held
  refine ⟨after, zf, sf, run, stateA, reachable, [], [], held, rfl, ?_⟩
  simpa only [inputPrefix, List.range_zero, List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0

/-- The complete actual NO_FLUSH strategy preserves the initialized raw
encoding invariant while extending both accepted input and published bytes. -/
theorem deflate_slow_no_flush_raw_prefix {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (output : 0 < z.avail_out.toNat) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (encoding : RawPrefix h d input base published) :
    ∃ used after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      RawPrefix after result extended base' (published ++ written) := by
  obtain ⟨before, completed, held, wire, meaning⟩ := encoding
  obtain ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
      remaining, encoded, run, stateA, endA, buffersA, accountA, bytesA,
      agreesA, endpointA, baseA, pendingA, wireA, meaningA, _positionA⟩ :=
    deflate_slow_no_flush_stream_encoding boundary frontier buffers positive pointer memory wrap output inputValid held wire meaning
  exact ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
    run, stateA, endA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
    remaining, encoded, pendingA, wireA, meaningA⟩

/-- The complete actual FINISH strategy either preserves the raw prefix
at an early output stop or completes a valid raw stream, with the exact
remaining pending bytes included. Both alternatives share one actual run. -/
theorem deflate_slow_finish_raw_prefix {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (output : 0 < z.avail_out.toNat) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base' ys ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      ((rc = need_more ∧ StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧
        EndFrontier after result ∧ RawPrefix after result extended base' (published ++ written)) ∨
       ((rc = finish_started ∨ rc = finish_done) ∧ ∃ tailBytes,
        Bytes after result.pending_out result.pending.toNat tailBytes ∧ result.bi_valid.toInt.toNat = 0 ∧
        ZlibF.Spec.Deflate.Valid (inputPrefix extended (origin + fillEnd d + used))
          (published ++ written ++ tailBytes))) := by
  obtain ⟨before, completed, held, wire, meaning⟩ := encoding
  obtain ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
      run, stateA, buffersA, accountA, bytesA, agreesA, casesA⟩ :=
    deflate_slow_finish_stream_encoding boundary frontier buffers positive pointer memory wrap output inputValid held wire meaning
  refine ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
    run, stateA, buffersA, accountA, bytesA, agreesA, ?_⟩
  rcases casesA with ⟨returned, remaining, encoded, strategyA, endA, pendingA, wireA, meaningA, _positionA⟩ | done
  · exact Or.inl ⟨returned, strategyA, endA, remaining, encoded, pendingA, wireA, meaningA⟩
  · exact Or.inr done

end Zlib.Deflate.Engine.Proofs
