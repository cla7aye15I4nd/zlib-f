import ZlibF.Math.DeflateChecksum
import ZlibF.Proof.«deflate.c.engine.fill-counters»

/-! # Actual complete refill updates Adler over exactly the consumed caller bytes -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateChecksum
set_option autoImplicit false

/-- Even an empty actual input range has the exact empty byte slice. -/
theorem caller_input_empty_bytes {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (empty : z.avail_in = 0) :
    Bytes h z.next_in 0 [] := by
  obtain ⟨other, get, input, _output, _separate⟩ := buffers
  have same : other = z := Option.some.inj (get.symm.trans good.live.hz)
  subst other
  rcases input with null | ⟨⟨bytes, data⟩, _writable, _outside⟩
  · exact Or.inl ⟨null, rfl, rfl⟩
  · rw [empty] at data
    have nil : bytes = [] := by
      rcases data with null | ⟨_ref, _off, _array, _pointer, _get, _bound, value⟩
      · exact null.2.2
      · simpa only [UInt32.toNat_zero, List.take_zero] using value
    simpa only [UInt32.toNat_zero, nil] using data

/-- A real readStream result uses precisely the accounted input slice;
the independent checksum append identity includes single-byte reads. -/
theorem read_stream_adler_accounted {h : Heap} {z z' : ZStream} {used : Nat}
    {n : UInt32} {ref : BRef} {io : Nat} {ia : Array UInt8} {before : List UInt8}
    (stream : z' = readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat)))
    (account : StreamAccounting z z' used 0) (pointer : z.next_in = .ref ref io)
    (get : Space.get h ref = some ia) (bound : io + z.avail_in.toNat ≤ ia.size)
    (count : n.toNat ≤ z.avail_in.toNat) (checksum : z.adler = (ZlibF.Spec.adler32 before).toUInt64) :
    ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
      z'.adler = (ZlibF.Spec.adler32 (before ++ copied)).toUInt64 := by
  have expected := read_stream_accounting z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat)) pointer count
  rw [← stream] at expected
  have amount := (stream_accounting_counts_unique account expected).1
  subst used
  refine ⟨(ia.toList.drop io).take n.toNat,
    Or.inr ⟨ref, io, ia, pointer, get, by omega, rfl⟩, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop, Array.length_toList]
    omega
  · rw [stream]
    change adlerValue z.adler ((ia.toList.drop io).take n.toNat) = _
    rw [checksum, adler_value_append]

/-- The whole actual fill_window call, including sliding, arbitrary
pending insertion and padding, updates the checksum on exactly the caller
bytes it consumes. The checksum premise describes the previous accepted
input, not a callee contract. Its initialization and loop propagation are
separate obligations. -/
theorem fill_window_run_adler {h after : Heap} {r : ZStreamRef} {ds origin used : Nat}
    {z z' : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {before : List UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (checksum : z.adler = (ZlibF.Spec.adler32 before).toUInt64)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' used 0) :
    ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
      z'.adler = (ZlibF.Spec.adler32 (before ++ copied)).toUInt64 := by
  have unchanged : z' = z →
      ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
        z'.adler = (ZlibF.Spec.adler32 (before ++ copied)).toUInt64 := by
    intro same
    have counts := account.2.2.1
    rw [same] at counts
    have amount : used = 0 := by omega
    rw [amount]
    refine ⟨[], ?_, rfl, ?_⟩
    · by_cases empty : z.avail_in = 0
      · exact caller_input_empty_bytes boundary.good buffers empty
      · cases pointer : z.next_in with
        | null => exact Or.inl ⟨rfl, rfl, rfl⟩
        | ref ref io =>
          obtain ⟨array, get, bound⟩ := caller_input_array boundary.good buffers pointer
          exact Or.inr ⟨ref, io, array, rfl, get, by omega, by simp⟩
    · simpa only [same, List.append_nil] using checksum
  by_cases empty : z.avail_in = 0
  · apply unchanged
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
        slide_pending_boundary boundary taken
      have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
      let hs := slideHeap h ds w p q d wa pa' qa'
      have getS : hs.bytes w = some (slideWindow d wa) := by simp [hs, slideHeap]
      have other := (fill_window_empty_storage boundaryS.good env.win getS boundaryS.range empty
        geometry.2.2.2.2.2.2.2.2).1
      have expected := (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans other
      have goodA := padded_good boundaryS.good env.win getS boundaryS.range
      exact (actual_run_stream_unique expected run goodA.live.hz live).symm
    · obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
      have expected := (fill_window_empty_storage boundary.good win get boundary.range empty taken).1
      have goodA := padded_good boundary.good win get boundary.range
      exact (actual_run_stream_unique expected run goodA.live.hz live).symm
  · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases pointer : z.next_in with
      | null => exact False.elim (inputValid empty pointer)
      | ref ref io => exact ⟨ref, io, rfl⟩
    obtain ⟨ia, data, inputBound⟩ := caller_input_array boundary.good buffers pointer
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
        slide_pending_boundary boundary taken
      have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
      let hs := slideHeap h ds w p q d wa pa' qa'
      have separate := caller_input_window_separate boundary.good buffers env.win pointer
      have dataS : Space.get hs ref = some ia := by rw [slide_input_frame boundary.good separate]; exact data
      have getS : hs.bytes w = some (slideWindow d wa) := by simp [hs, slideHeap]
      obtain ⟨_other, _result, _bytes, readRun, goodA, _rest⟩ :=
        fill_window_pending_complete_storage boundaryS.good boundaryS.frontier boundaryS.insert_le
          env.win getS boundaryS.range short geometry.2.2.2.2.2.2.2.2 wrap pointer dataS inputBound empty separate
      have expected := (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans readRun
      have streams := actual_run_stream_unique expected run goodA.live.hz live
      apply read_stream_adler_accounted streams.symm account pointer data inputBound _ checksum
      rw [rbLen_nat]
      exact Nat.min_le_left _ _
    · obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
      have separate := caller_input_window_separate boundary.good buffers win pointer
      obtain ⟨_other, _result, _bytes, expected, goodA, _rest⟩ :=
        fill_window_pending_complete_storage boundary.good boundary.frontier boundary.insert_le win get boundary.range
          short taken wrap pointer data inputBound empty separate
      have streams := actual_run_stream_unique expected run goodA.live.hz live
      apply read_stream_adler_accounted streams.symm account pointer data inputBound _ checksum
      rw [rbLen_nat]
      exact Nat.min_le_left _ _

end Zlib.Deflate.Engine.Proofs
