import ZlibF.Math.DeflateFlushMarkers
import ZlibF.Proof.«deflate.c.engine.partial-sync-publication»
import ZlibF.Proof.«deflate.c.engine.full-marker-publication»

/-! # Actual empty flush markers retain independently decoded continuation meaning -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt outBits natBits storedHeaderBits)
set_option autoImplicit false

/-- Actual PARTIAL/SYNC marker emission and publication preserve both the
initialized empty-block boundary and the independent later-block meaning.
The exact produced bytes and unconsumed PendingBits split the marker bits
without loss, even when the caller capacity is zero or short. Full public
encoded histories remain separate from this internal marker cutpoint. -/
theorem empty_partial_sync_publish_encoding {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (room : 8 ≤ buf.size) (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH) :
    ∃ produced after z' result before marker written remaining,
      (do
        let _ ← (if flush == Z_PARTIAL_FLUSH then Zlib.Trees.«_tr_align» (some (.tab ds))
          else Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0)
        flush_pending (some r)) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      ConfigFrame d result ∧ result.status = d.status ∧ result.last_flush = d.last_flush ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++ marker ∧
      ∀ (history decoded : List UInt8) (suffix rest : List Bool),
        (flush = Z_PARTIAL_FLUSH ∨ suffix.length % 8 = 0) →
        ZlibF.Spec.Blocks [] history suffix rest decoded →
        ZlibF.Spec.Blocks [] history (marker ++ suffix) rest decoded := by
  obtain ⟨produced, after, z', result, written, remaining, run, boundaryA, buffersA,
    accountA, sizesA, storageA, configA, statusA, lastA, readyA, bytesA, pendingA, outputA⟩ :=
    empty_partial_sync_publish boundary buffers trees pointer publish room flush flag
  refine ⟨produced, after, z', result, outBits buf d,
    (if flush == Z_PARTIAL_FLUSH then natBits 2 3 ++ (natBits 0 7 ++ []) else storedHeaderBits d 0 false),
    written, remaining, run, boundaryA, buffersA, accountA, sizesA, storageA,
    configA, statusA, lastA, readyA, pending_bits_base trees publish.2.1,
    bytesA, pendingA, outputA, ?_⟩
  intro history decoded suffix rest admissible next
  by_cases partialFlag : flush = Z_PARTIAL_FLUSH
  · subst flush
    simpa only [BEq.rfl, ite_true, List.append_nil] using
      Zlib.Trees.Proofs.Out.partial_marker_continuation next
  · have notPartial : (flush == Z_PARTIAL_FLUSH) = false := by simpa using partialFlag
    simp only [notPartial, Bool.false_eq_true, ite_false]
    exact Zlib.Trees.Proofs.Out.stored_header_zero_continuation d (admissible.resolve_left partialFlag) next

/-- The actual FULL marker, hash clear, position reset and publication
retain the independent empty stored-block meaning and every aligned later
block continuation. The returned content boundary records the real reset
origin; the encoded input history is unchanged by the empty marker. -/
theorem empty_full_marker_publish_encoding {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (look : d.lookahead = 0) (available : d.match_available = 0) :
    ∃ produced after z' result before written remaining,
      (do
        Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0
        let _ ← (do
          CLEAR_HASH (some (.tab ds))
          if (← rd (some (.tab ds)) (·.lookahead)) == 0 then
            wr (some (.tab ds)) (fun d => { d with strstart := 0, block_start := 0, insert := 0 }))
        flush_pending (some r)) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input base base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ConfigFrame d result ∧
      result.status = d.status ∧ result.last_flush = d.last_flush ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++ storedHeaderBits d 0 false ∧
      ∀ (history decoded : List UInt8) (suffix rest : List Bool), suffix.length % 8 = 0 →
        ZlibF.Spec.Blocks [] history suffix rest decoded →
        ZlibF.Spec.Blocks [] history (storedHeaderBits d 0 false ++ suffix) rest decoded := by
  obtain ⟨produced, after, z', result, written, remaining, run, boundaryA,
    buffersA, accountA, configA, statusA, lastA, bytesA, pendingA, outputA⟩ :=
    empty_full_marker_publish boundary buffers trees pointer publish look available
  exact ⟨produced, after, z', result, outBits buf d, written, remaining, run,
    boundaryA, buffersA, accountA, configA, statusA, lastA,
    pending_bits_base trees publish.2.1, bytesA, pendingA, outputA,
    fun _ _ _ _ aligned next => Zlib.Trees.Proofs.Out.stored_header_zero_continuation d aligned next⟩

end Zlib.Deflate.Engine.Proofs
