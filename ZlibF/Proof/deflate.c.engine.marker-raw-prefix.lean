import ZlibF.Math.DeflateMarkerPrefix
import ZlibF.Proof.«deflate.c.engine.marker-encoding»
import ZlibF.Proof.«deflate.c.engine.raw-prefix»
import ZlibF.Proof.«deflate.c.engine.flush-block-prefix»

/-! # Actual flush markers extend the initialized cumulative raw encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
open Zlib.Trees.Proofs.Out (TreesInvAt outBits natBits storedHeaderBits)
set_option autoImplicit false

/-- Actual PARTIAL/SYNC marker generation and publication preserve the
same cumulative RawPrefix. The stored marker's alignment is derived from
the existing encoded history and actual held-bit count. No parser or
unproved callee contract is assumed for this actual execution. -/
theorem empty_partial_sync_publish_raw_prefix {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
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
      (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨before, encoded, held, wire, meaning⟩ := encoding
  have initial := pending_bits_base trees publish.2.1
  have beforeEq : outBits buf d = before :=
    (pending_bits_zero_value publish.1 initial).trans (pending_bits_zero_value publish.1 held).symm
  have position : encoded.length % 8 = d.bi_valid.toInt.toNat % 8 := by
    have count := congrArg List.length wire
    have pendingLength := pending_bits_exact_length held
    rw [publish.1] at pendingLength
    simp only [List.length_append, encoded_bytes_length] at count
    simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add] at pendingLength
    omega
  obtain ⟨produced, after, z', result, written, remaining, run, stateA, buffersA, accountA,
      _sizes, _storage, configA, statusA, lastA, readyA, bytesA, pendingA, wireA⟩ :=
    empty_partial_sync_publish boundary buffers trees pointer publish room flush flag
  rw [beforeEq] at wireA
  let marker := if flush == Z_PARTIAL_FLUSH then natBits 2 3 ++ (natBits 0 7 ++ []) else storedHeaderBits d 0 false
  have markerPrefix : BlockPrefix [] (0 + encoded.length) (inputPrefix input base) marker (inputPrefix input base) := by
    rcases flag with partialFlag | sync
    · subst flush
      simpa only [marker, BEq.rfl, ite_true, List.append_nil, Nat.zero_add] using
        partial_marker_block_prefix encoded.length (inputPrefix input base)
    · subst flush
      simpa only [marker, show (Z_SYNC_FLUSH == Z_PARTIAL_FLUSH) = false from rfl,
        Bool.false_eq_true, ite_false, Nat.zero_add] using
        stored_header_zero_block_prefix d position (inputPrefix input base)
  have allWire : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded ++ marker := by
    calc
      _ = ZlibF.Spec.bytesToBits published ++ (ZlibF.Spec.bytesToBits written ++ remaining) := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc]
      _ = ZlibF.Spec.bytesToBits published ++ (before ++ marker) := by rw [wireA]
      _ = (ZlibF.Spec.bytesToBits published ++ before) ++ marker := (List.append_assoc _ _ _).symm
      _ = encoded ++ marker := by rw [wire]
  exact ⟨produced, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
    ⟨remaining, encoded ++ marker, pendingA, allWire, block_prefix_append meaning markerPrefix⟩,
    configA, statusA, lastA, readyA⟩

/-- Actual FULL marker emission, hash clearing, physical position reset
and pending publication preserve cumulative raw encoding. The initialized
content boundary rebases its origin to the global logical base; the empty
stored marker adds no accepted input. Every output capacity is included. -/
theorem empty_full_marker_publish_raw_prefix {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
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
      result.status = d.status ∧ result.last_flush = d.last_flush := by
  obtain ⟨before, encoded, held, wire, meaning⟩ := encoding
  have initial := pending_bits_base trees publish.2.1
  have beforeEq : outBits buf d = before :=
    (pending_bits_zero_value publish.1 initial).trans (pending_bits_zero_value publish.1 held).symm
  have position : encoded.length % 8 = d.bi_valid.toInt.toNat % 8 := by
    have count := congrArg List.length wire
    have pendingLength := pending_bits_exact_length held
    rw [publish.1] at pendingLength
    simp only [List.length_append, encoded_bytes_length] at count
    simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add] at pendingLength
    omega
  obtain ⟨produced, after, z', result, written, remaining, run, stateA, buffersA, accountA,
      configA, statusA, lastA, bytesA, pendingA, wireA⟩ :=
    empty_full_marker_publish boundary buffers trees pointer publish look available
  rw [beforeEq] at wireA
  have markerPrefix : BlockPrefix [] (0 + encoded.length) (inputPrefix input base)
      (storedHeaderBits d 0 false) (inputPrefix input base) := by
    simpa only [Nat.zero_add] using stored_header_zero_block_prefix d position (inputPrefix input base)
  have allWire : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded ++ storedHeaderBits d 0 false := by
    calc
      _ = ZlibF.Spec.bytesToBits published ++ (ZlibF.Spec.bytesToBits written ++ remaining) := by
        simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc]
      _ = ZlibF.Spec.bytesToBits published ++ (before ++ storedHeaderBits d 0 false) := by rw [wireA]
      _ = (ZlibF.Spec.bytesToBits published ++ before) ++ storedHeaderBits d 0 false := (List.append_assoc _ _ _).symm
      _ = encoded ++ storedHeaderBits d 0 false := by rw [wire]
  exact ⟨produced, after, z', result, written, run, stateA, buffersA, accountA, bytesA,
    ⟨remaining, encoded ++ storedHeaderBits d 0 false, pendingA, allWire, block_prefix_append meaning markerPrefix⟩,
    configA, statusA, lastA⟩

end Zlib.Deflate.Engine.Proofs
