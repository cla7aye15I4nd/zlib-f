import ZlibF.Proof.«deflate.c.engine.generic-foreign-full-marker»
import ZlibF.Proof.«deflate.c.engine.marker-raw-prefix»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
open Zlib.Trees.Proofs.Out (TreesInvAt outBits storedHeaderBits)
set_option autoImplicit false

/-- Actual FULL marker emission, hash clearing, physical position reset
and pending publication preserve cumulative raw encoding. The initialized
content boundary rebases its origin to the global logical base; the empty
stored marker adds no accepted input. Every output capacity is included. -/
theorem foreign_full_marker_joint_raw_prefix {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (publish : PublishReady d)
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
      result.status = d.status ∧ result.last_flush = d.last_flush ∧ z'.adler=z.adler ∧
      z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      (0<z'.avail_out.toNat → PublishReady result) ∧ fillEnd result=0 ∧ result.match_available=0 ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧ ByteSizes h after ∧ Shape h after ∧
      after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
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
      configA, statusA, lastA, bytesA, pendingA, wireA,adlerA,endpointA,availableA,
      inputA,outputA,readyA,sizesA,shapeA,allocA,nextA,frameA⟩ :=
    foreign_empty_full_marker_publish boundary buffers trees pointer publish look available
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
    configA, statusA, lastA,adlerA,inputA,outputA,readyA,endpointA,availableA,frameA,sizesA,shapeA,allocA,nextA⟩

end Zlib.Deflate.Engine.Proofs
