import ZlibF.Proof.«deflate.c.engine.header-encoding»
import ZlibF.Proof.«deflate.c.engine.public-first-no-flush-buffered»
import ZlibF.Math.DeflateByteEncoding

/-! # Exact wrapper-header bytes stay separate from raw block encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- A partially published initial wrapper header. No raw input has reached
the strategy. Pending header bytes are explicitly distinct from RawPrefix. -/
def HeaderPending (h : Heap) (d : DeflateState) (published : List UInt8) : Prop :=
  ∃ remaining, PendingBits h d (ZlibF.Spec.bytesToBits remaining) ∧
    published ++ remaining = [120, 156] ∧ d.bi_valid.toInt.toNat = 0 ∧
    d.strstart = 0 ∧ d.lookahead = 0

/-- Legal caller replacement keeps every private pending header bit. -/
theorem HeaderPending.rebuffer {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {published : List UInt8}
    (encoding : HeaderPending h d published) (good : DGood h r ds z d) (edit : Rebuffer h g r) :
    HeaderPending g d published := by
  obtain ⟨remaining, pending, wire, bits, start, look⟩ := encoding
  exact ⟨remaining, rebuffer_pending_bits good edit pending, wire, bits, start, look⟩

/-- Actual header pending publication appends precisely the copied header
bytes, including zero output and advanced cursors. Draining the header
establishes the initial empty raw encoding invariant on this same heap. -/
theorem flush_pending_header_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (encoding : HeaderPending h d published) :
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
      readyA, bytesA, pendingA, wireA⟩ :=
    flush_pending_buffered_boundary boundary buffers pointer pending
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

/-- The exact actual one-byte header heap contains 120 in caller output
and the sole remaining header byte 156 in private pending storage. -/
theorem header_one_output_encoding {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d) (room : 2 ≤ buf.size)
    (pointer : z.next_out = .ref (.blk ob) oo) (separate : ob ≠ pb)
    (outputRoom : oo + 1 ≤ output.size) :
    Bytes (headerOneHeap h r ds pb ob oo z d buf output) z.next_out 1 [120] ∧
      HeaderPending (headerOneHeap h r ds pb ob oo z d buf output) (headerOneState d pb) [120] := by
  have first : (zlibHeaderBytes buf)[0]? = some (120 : UInt8) := by
    simp [zlibHeaderBytes, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      show 0 < buf.size by omega]
  have second : (zlibHeaderBytes buf)[1]? = some (156 : UInt8) := by
    simp [zlibHeaderBytes, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      show 1 < buf.size by omega]
  have getOutput : (headerOneHeap h r ds pb ob oo z d buf output).bytes ob =
      some (copyRange output (zlibHeaderBytes buf) oo 0 1) := by
    simp [headerOneHeap, headerOneBytes]
  have getPending : (headerOneHeap h r ds pb ob oo z d buf output).bytes pb = some (zlibHeaderBytes buf) := by
    simp [headerOneHeap, headerOneBytes, upd_ne _ _ _ _ (Ne.symm separate)]
  have copied : (copyRange output (zlibHeaderBytes buf) oo 0 1)[oo]? = some (120 : UInt8) := by
    rw [getElem?_copyRange output (zlibHeaderBytes buf) oo 0 1 oo outputRoom]
    simp [getElem!_def, first]
  have outputSlice := array_one_slice (array := copyRange output (zlibHeaderBytes buf) oo 0 1)
    (offset := oo) (by rw [size_copyRange]; omega) copied
  have pendingSlice := array_one_slice (array := zlibHeaderBytes buf) (offset := 1)
    (by simp only [zlibHeaderBytes, Array.size_set!]; omega) second
  have held := pending_bits_slice (h := headerOneHeap h r ds pb ob oo z d buf output)
    (d := headerOneState d pb) (pb := pb) (off := 1) (by rfl) getPending
      (by change 2 ≤ (zlibHeaderBytes buf).size; simpa only [zlibHeaderBytes, Array.size_set!] using room)
  change PendingBits (headerOneHeap h r ds pb ob oo z d buf output) (headerOneState d pb)
    (ZlibF.Spec.bytesToBits ((zlibHeaderBytes buf).toList.drop 1 |>.take 1) ++
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat) at held
  rw [pendingSlice, initial.bits] at held
  have pending : PendingBits (headerOneHeap h r ds pb ob oo z d buf output) (headerOneState d pb)
      (ZlibF.Spec.bytesToBits [156]) := by
    simpa only [Int32.toInt_zero, Int.toNat_zero, Zlib.Trees.Proofs.Out.natBits, List.range_zero, List.map_nil, List.append_nil] using held
  refine ⟨Or.inr ⟨.blk ob, oo, copyRange output (zlibHeaderBytes buf) oo 0 1,
    pointer, getOutput, by rw [size_copyRange]; exact outputRoom, outputSlice.symm⟩,
    [156], pending, rfl, ?_, initial.start, initial.lookahead⟩
  change d.bi_valid.toInt.toNat = 0
  rw [initial.bits]
  rfl

end Zlib.Deflate.Engine.Proofs
