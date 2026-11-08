import ZlibF.Proof.«deflate.c.engine.full-storage»

/-! # The complete empty-input refill frame -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Every actual empty-input refill has its complete object/allocation
frame, including the source window-slide branch before the early break. -/
theorem fill_window_empty_run_full_storage {h after : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs) (empty : z.avail_in = 0)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
  · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
      slide_pending_boundary boundary taken
    have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
    let hs := slideHeap h ds w p q d wa pa' qa'
    have getS : hs.bytes w = some (slideWindow d wa) := by simp [hs, slideHeap]
    have other := (fill_window_empty_storage boundaryS.good env.win getS boundaryS.range empty
      geometry.2.2.2.2.2.2.2.2).1
    have expected := (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans other
    have heaps := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
    rw [← heaps]
    obtain ⟨shapeS, frameS, _liveS, allocS, nextS⟩ :=
      slide_heap_full_storage boundary.good env.win env.prevp env.headp env.wbytes env.pwords env.hwords pa' qa'
    obtain ⟨shapeP, frameP, _liveP, allocP, nextP⟩ := padded_heap_full_storage boundaryS.good env.win getS
    have shape := shapeS.trans shapeP
    have frame := full_frame_trans_shape frameS frameP shapeS
    exact ⟨shape, frame, full_shape_live_change shape, allocP.trans allocS, nextP.trans nextS⟩
  · obtain ⟨w, wa, window, get, _view, _form⟩ := boundary.data
    have expected := (fill_window_empty_storage boundary.good window get boundary.range empty taken).1
    have heaps := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
    rw [← heaps]
    exact padded_heap_full_storage boundary.good window get

end Zlib.Deflate.Engine.Proofs
