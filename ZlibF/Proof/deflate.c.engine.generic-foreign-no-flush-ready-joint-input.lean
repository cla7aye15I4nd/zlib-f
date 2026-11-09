import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-data-joint-input»
import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual public deflate entry, last-flush store, BUSY header skip,
computed slow dispatch and return control retain independent raw encoding
on the exact same returned heap. Empty-input retry is included. This is the
accepted no-old-pending BUSY branch; duplicate/refusal, header creation and
old-pending branches remain separate public obligations. -/
theorem public_foreign_busy_no_flush_ready_joint_input {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pending : d.pending = 0) (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (resume : z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (encoding : RawPrefix h d input base published)
    (checksum : z.adler=(ZlibF.Spec.adler32 (inputPrefix input (origin+fillEnd d))).toUInt64) :
    ∃ used after z' result extended nextOrigin base' ys written,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result extended base' (published ++ written) ∧
      z'.adler=(ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin+fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin+fillEnd result)=inputPrefix input (origin+fillEnd d)++actualInput.take used := by
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  have encoding0 := encoding.last_flush boundary.good Z_NO_FLUSH
  have snapshot0 := caller_bytes_setD_depth (result := {d with last_flush := Z_NO_FLUSH}) boundary.good.live.hs rfl snapshot
  have ready : PublishReady { d with last_flush := Z_NO_FLUSH } :=
    ⟨pending, boundary.empty_cursor pending, boundary.bits⟩
  obtain ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
      run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
      statusA, lastA, encodingA,adlerA,inputLedgerA⟩ :=
    public_foreign_busy_no_flush_data_joint_input boundary0 buffers0 status level strategy pointer memory wrap ready inputValid snapshot0 encoding0 checksum
  have entry := public_busy_no_flush_resuming_entry boundary.good status pending
    (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at output; contradiction) inputValid lower upper resume
  exact ⟨used, after, z', result, extended, nextOrigin, base', ys, written,
    entry.trans run, stateA, buffersA, accountA, bytesA, agreesA, endpointA,
    baseA, statusA, lastA, encodingA,adlerA,inputLedgerA⟩


end Zlib.Deflate.Engine.Proofs
