import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-buffered-boundary»
import ZlibF.Proof.«deflate.c.engine.header-pending-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Actual header pending publication appends precisely the copied header
bytes, including zero output and advanced cursors. Draining the header
establishes the initial empty raw encoding invariant on this same heap. -/
theorem flush_pending_foreign_header_encoding {h : Heap} {r : ZStreamRef} {ds owner oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (encoding : HeaderPending h d published) :
    ∃ after z' result written,
      flush_pending (some r) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input origin 0 [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 written.length ∧ Bytes after z.next_out written.length written ∧
      HeaderPending after result (published ++ written) ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧
      (result.pending = 0 → published ++ written = [120, 156] ∧ RawPrefix after result input 0 []) := by
  obtain ⟨beforeBytes, pending, headerEq, bits, start, look⟩ := encoding
  obtain ⟨_pb, produced, after, z', result, written, remaining, _base,
      run, stateA, buffersA, accountA, _sizes, _storage, _amount, _left, fields,
      readyA, bytesA, pendingA, wireA,_preciseA⟩ :=
    flush_pending_buffered_foreign_boundary boundary buffers pointer pending
  have bitsA : result.bi_valid.toInt.toNat = 0 := by rw [fields]; exact bits
  obtain ⟨remainingBytes, remainingData, remainingEq⟩ := pendingA
  have remainingBits : remaining = ZlibF.Spec.bytesToBits remainingBytes := by
    simpa only [bitsA, List.range_zero, List.map_nil, List.append_nil] using remainingEq
  rw [remainingBits] at wireA
  have byteEq : written ++ remainingBytes = beforeBytes := by
    apply encoded_bytes_injective
    simpa only [ZlibF.Spec.bytesToBits, List.flatMap_append] using wireA
  have wholeHeader : (published ++ written) ++ remainingBytes = [120, 156] := by
    rw [List.append_assoc, byteEq, headerEq]
  have remainingPending : PendingBits after result (ZlibF.Spec.bytesToBits remainingBytes) :=
    ⟨remainingBytes, remainingData, by simp only [bitsA, List.range_zero, List.map_nil, List.append_nil]⟩
  have phaseA : HeaderPending after result (published ++ written) :=
    ⟨remainingBytes, remainingPending, wholeHeader, bitsA, by rw [fields]; exact start, by rw [fields]; exact look⟩
  have length := public_bytes_length bytesA
  refine ⟨after, z', result, written, run, stateA, buffersA, ?_, ?_, phaseA, readyA, ?_⟩
  · rw [length]; exact accountA
  · rw [length]; exact bytesA
  · intro empty
    have remainingLength := public_bytes_length remainingData
    rw [empty] at remainingLength
    have remainingEmpty : remainingBytes = [] := by
      cases remainingBytes with
      | nil => rfl
      | cons byte tail => simp only [List.length_cons, UInt64.toNat_zero] at remainingLength; omega
    rw [remainingEmpty, List.append_nil] at wholeHeader
    refine ⟨wholeHeader, [], [], ?_, rfl, ?_⟩
    · simpa only [remainingEmpty, ZlibF.Spec.bytesToBits, List.flatMap_nil] using remainingPending
    · simpa only [inputPrefix, List.range_zero, List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0


end Zlib.Deflate.Engine.Proofs
