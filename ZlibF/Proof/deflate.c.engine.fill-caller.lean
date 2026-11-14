import ZlibF.Proof.«deflate.c.engine.fill-history»
import ZlibF.Spec.Public.Streams
import ZlibF.Spec.Functional.Checksums
import ZlibF.Spec.Functional.Api.Compress

/-! # Resumed fill from the public buffer and engine boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem read_stream_accounting (z : ZStream) (n : UInt32) (ref : BRef) (io : Nat) (checksum : UInt64)
    (pointer : z.next_in = .ref ref io) (bound : n.toNat ≤ z.avail_in.toNat) :
    StreamAccounting z (readStream z n ref io checksum) n.toNat 0 := by
  have sub : (z.avail_in - n).toNat = z.avail_in.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr bound)
  unfold StreamAccounting readStream
  refine ⟨bound, by omega, ?_, by simp, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [sub]
    omega
  · rw [pointer]
    rfl
  · cases z.next_out <;> simp [advance]

set_option maxHeartbeats 2000000 in
/-- A real resumed fill using public caller buffers. Input-array extent,
copy separation and private writability are derived rather than assumed.
The exact returned heap carries accounting, the extended input view,
matching history, chains, padding and the next insertion hash together.
The no-slide and insert=0 conditions identify this internal source path.
-/
theorem fill_window_resume_caller {h : Heap} {r : ZStreamRef} {ds w io top origin : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {wa : Array UInt8} {input : Nat → UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) (nonempty : z.avail_in ≠ 0)
    (history : LazyHistory input origin d) (deferred : DeferredByte d)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)) :
    ∃ used after z' result output extended,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ HeapChains after result top ∧
      StreamAccounting z z' used 0 ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some output ∧
      result.strstart = d.strstart ∧ result.lookahead.toNat = d.lookahead.toNat + used ∧
      result.insert = 0 ∧ result.wrap = 1 ∧ result.sym_next = d.sym_next ∧
      fillEnd result ≤ result.window_size.toNat ∧
      min (fillEnd result + 258) result.window_size.toNat ≤ result.high_water.toNat ∧
      (3 ≤ result.lookahead.toNat → InsHForm result.hash_shift result.hash_mask
        (bfn output) result.strstart.toNat result.ins_h) ∧
      LazyHistory extended origin result ∧ DeferredByte result ∧
      (∀ i, i < fillEnd result → bfn output i = extended (origin + i)) ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) := by
  obtain ⟨ia, data, inputBound⟩ := caller_input_array good buffers pointer
  have separate : BRef.blk w ≠ ref := caller_input_window_separate good buffers win pointer
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let dr := resumeReadState d n copied
  let result := resumedFillState d n copied
  let output := fillRange copied (paddingStart dr) (paddingCount dr) 0
  let after := resumedFillHeap h r ds w z d ref io ia wa
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let extended := extendInput input (origin + fillEnd d) ia io
  obtain ⟨run, goodA, chainsA, winA, bytesA, rangeA, paddingA, formA⟩ :=
    fill_window_resume_complete good chains win get range short noSlide insert wrap pointer data inputBound
      nonempty (Or.inl separate)
  obtain ⟨historyA, deferredA, viewA⟩ := resumed_fill_history (ref := ref)
    good win get range inputBound history deferred view
  have count : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have counts := resume_read_counts good win get range
  obtain ⟨key, high, fields⟩ := resumed_fill_record d n copied
  change result = _ at fields
  refine ⟨n.toNat, after, z', result, output, extended, run, goodA, chainsA,
    read_stream_accounting z n ref io _ pointer (by omega), winA, bytesA, ?_, ?_, ?_, ?_, ?_,
    rangeA, paddingA, formA, historyA, deferredA, viewA, ?_⟩
  · rw [fields]
  · rw [fields]
    exact counts.2.1
  · rw [fields]
    exact insert
  · rw [fields]
    exact wrap
  · rw [fields]
  · intro i hi
    simp only [extended, extendInput, hi, if_true]

end Zlib.Deflate.Engine.Proofs
