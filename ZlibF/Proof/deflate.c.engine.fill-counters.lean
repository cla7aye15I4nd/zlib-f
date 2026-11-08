import ZlibF.Proof.«deflate.c.engine.counter-effects»
import ZlibF.Proof.«deflate.c.engine.fill-slide-pending»
import ZlibF.Proof.«deflate.c.engine.fill-caller-storage»
import ZlibF.Proof.«deflate.c.engine.fill-pending-complete»

/-! # Every actual refill branch has exact total counters -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual default refill branch retains exact public totals.
Sliding, deferred insertion and padding use the same real returned stream.
No input byte budget or zero-insert entry premise is imposed. -/
theorem fill_window_run_counter_effects {h after : Heap} {r : ZStreamRef} {ds origin used : Nat}
    {z z' : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' used 0) :
    z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out := by
  by_cases empty : z.avail_in = 0
  · by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
        slide_pending_boundary boundary taken
      have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
      let hs := slideHeap h ds w p q d wa pa' qa'
      have getS : hs.bytes w = some (slideWindow d wa) := by simp [hs, slideHeap]
      have other := (fill_window_empty_storage boundaryS.good env.win getS boundaryS.range empty
        geometry.2.2.2.2.2.2.2.2).1
      have expected := (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans other
      have goodA := padded_good boundaryS.good env.win getS boundaryS.range
      have streams := actual_run_stream_unique expected run goodA.live.hz live
      exact unchanged_stream_counter_effects_accounted streams.symm account
    · obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
      have expected := (fill_window_empty_storage boundary.good win get boundary.range empty taken).1
      have goodA := padded_good boundary.good win get boundary.range
      have streams := actual_run_stream_unique expected run goodA.live.hz live
      exact unchanged_stream_counter_effects_accounted streams.symm account
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
      obtain ⟨other, _result, _bytes, readRun, goodA, _rest⟩ :=
        fill_window_pending_complete_storage boundaryS.good boundaryS.frontier boundaryS.insert_le
          env.win getS boundaryS.range short geometry.2.2.2.2.2.2.2.2 wrap pointer dataS inputBound empty separate
      have expected := (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans readRun
      have streams := actual_run_stream_unique expected run goodA.live.hz live
      apply read_stream_counter_effects_accounted streams.symm account pointer
      rw [rbLen_nat]
      exact Nat.min_le_left _ _
    · obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
      have separate := caller_input_window_separate boundary.good buffers win pointer
      obtain ⟨other, _result, _bytes, expected, goodA, _rest⟩ :=
        fill_window_pending_complete_storage boundary.good boundary.frontier boundary.insert_le win get boundary.range
          short taken wrap pointer data inputBound empty separate
      have streams := actual_run_stream_unique expected run goodA.live.hz live
      apply read_stream_counter_effects_accounted streams.symm account pointer
      rw [rbLen_nat]
      exact Nat.min_le_left _ _

end Zlib.Deflate.Engine.Proofs
