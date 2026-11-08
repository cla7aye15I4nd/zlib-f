import ZlibF.Proof.«deflate.c.engine.marker-raw-prefix»
import ZlibF.Proof.«deflate.c.engine.partial-sync-marker-checksum»
import ZlibF.Proof.«deflate.c.engine.full-marker-checksum»

/-! # The same actual marker execution preserves raw encoding and Adler -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The real PARTIAL/SYNC marker retains both cumulative raw encoding and
the accepted-input checksum on the same actual returned heap and stream. -/
theorem empty_partial_sync_publish_raw_prefix_adler {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (room : 8 ≤ buf.size) (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH)
    (encoding : RawPrefix h d input base published) :
    ∃ produced after z' result written,
      (do
        let _ ← (if flush == Z_PARTIAL_FLUSH then Zlib.Trees.«_tr_align» (some (.tab ds))
          else Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0)
        flush_pending (some r)) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ Bytes after z.next_out produced written ∧
      RawPrefix after result input base (published ++ written) ∧ ConfigFrame d result ∧
      result.status = d.status ∧ result.last_flush = d.last_flush ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧ z'.adler = z.adler := by
  obtain ⟨produced, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
      encodingA, configA, statusA, lastA, readyA⟩ :=
    empty_partial_sync_publish_raw_prefix boundary buffers trees pointer publish room flush flag encoding
  obtain ⟨_count, _other, _otherZ, _otherD, _written, _remaining, actual, stateOther, _buffers,
      _account, _sizes, _storage, _config, _status, _last, _ready, _bytes, _pending, _wire, adler⟩ :=
    empty_partial_sync_publish_adler boundary buffers trees pointer publish room flush flag
  have same := actual_run_stream_unique actual run stateOther.good.live.hz stateA.good.live.hz
  exact ⟨produced, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
    encodingA, configA, statusA, lastA, readyA, same ▸ adler⟩

/-- The real FULL marker and hash/position reset retain cumulative raw
meaning and Adler while rebasing the physical origin to the logical base.
Reset does not remove previously accepted input from the encoded history. -/
theorem empty_full_marker_publish_raw_prefix_adler {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (look : d.lookahead = 0) (available : d.match_available = 0)
    (encoding : RawPrefix h d input base published) :
    ∃ produced after z' result written,
      (do
        Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0
        let _ ← (do
          CLEAR_HASH (some (.tab ds))
          if (← rd (some (.tab ds)) (·.lookahead)) == 0 then
            wr (some (.tab ds)) (fun d => { d with strstart := 0, block_start := 0, insert := 0 }))
        flush_pending (some r)) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input base base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ Bytes after z.next_out produced written ∧
      RawPrefix after result input base (published ++ written) ∧ ConfigFrame d result ∧
      result.status = d.status ∧ result.last_flush = d.last_flush ∧ z'.adler = z.adler := by
  obtain ⟨produced, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
      encodingA, configA, statusA, lastA⟩ :=
    empty_full_marker_publish_raw_prefix boundary buffers trees pointer publish look available encoding
  obtain ⟨_count, _other, _otherZ, _otherD, _written, _remaining, actual, stateOther, _buffers,
      _account, _config, _status, _last, _bytes, _pending, _wire, adler⟩ :=
    empty_full_marker_publish_adler boundary buffers trees pointer publish look available
  have same := actual_run_stream_unique actual run stateOther.good.live.hz stateA.good.live.hz
  exact ⟨produced, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
    encodingA, configA, statusA, lastA, same ▸ adler⟩

end Zlib.Deflate.Engine.Proofs
