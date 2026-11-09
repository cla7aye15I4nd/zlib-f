import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-finish-data-input»
import ZlibF.Proof.«deflate.c.engine.public-finish-ready-encoding»

/-! # Actual ready public FINISH calls retain exact input and stream meaning -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual positive-output BUSY FINISH entry, request store, strategy,
status and trailer execution retain encoding of exactly the original
consumed caller input. All complete strategy return alternatives are
included. Existing pending output is composed separately. -/
theorem public_foreign_busy_finish_ready_encoding_input {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published actualInput : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (pending : d.pending = 0) (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result written accepted,
      accepted = inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((∃ nextInput nextOrigin nextBase ys,
          BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧
          RawPrefix after result nextInput nextBase (published ++ written) ∧
          inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
       (result.wrap = 1 ∧ result.bi_valid.toInt = 0 ∧ ∃ tailBytes,
          Bytes after result.pending_out result.pending.toNat tailBytes ∧
          ZlibF.Spec.Deflate.Valid accepted (published ++ written ++ tailBytes)) ∨
       (result.wrap = -1 ∧ result.bi_valid.toInt = 0 ∧ ∃ tailBytes,
          Bytes after result.pending_out result.pending.toNat tailBytes ∧
          ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ published ++ written ++ tailBytes))) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ published ++ written)) := by
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
  have snapshot0 := caller_bytes_setD_depth (result := { d with last_flush := Z_FINISH }) boundary.good.live.hs rfl snapshot
  have encoding0 := encoding.last_flush boundary.good Z_FINISH
  have ready : PublishReady { d with last_flush := Z_FINISH } :=
    ⟨pending, boundary.empty_cursor pending, boundary.bits⟩
  have entry := public_busy_finish_entry boundary.good status pending
    (by rw [pointer]; intro impossible; cases impossible)
    (by intro zero; rw [zero] at output; contradiction) inputValid lower upper
  rw [entry]
  exact public_foreign_busy_finish_data_encoding_input (d := { d with last_flush := Z_FINISH }) boundary0 buffers0 status level strategy pointer memory wrap ready
    inputValid snapshot0 checksum encoding0

end Zlib.Deflate.Engine.Proofs
