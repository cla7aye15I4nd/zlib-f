import ZlibF.Proof.«deflate.c.engine.generic-foreign-sync-data-input»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-full-data-input»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-block-data-input»

/-! # Actual SYNC, FULL and BLOCK data paths retain exact consumed-input meaning -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual SYNC2, FULL3 and BLOCK5 data dispatch has one shared exact-input,
final-heap output, RawPrefix, matching Adler and byte-interval contract.
Every prepared output capacity is covered, including zero. -/
theorem public_foreign_busy_sync_full_block_data_raw_prefix_input_interval {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flag : flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK)
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
      ByteOutputInterval h after (.dstate_depth owner) oo written.length := by
  rcases flag with rfl|rfl|rfl
  · exact public_foreign_busy_sync_data_raw_prefix_input_interval (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid snapshot checksum encoding
  · exact public_foreign_busy_full_data_raw_prefix_input_interval (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid snapshot checksum encoding
  · exact public_foreign_busy_block_data_raw_prefix_input_interval (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid snapshot checksum encoding

end Zlib.Deflate.Engine.Proofs
