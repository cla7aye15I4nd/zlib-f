import ZlibF.Proof.«deflate.c.gzip-init-success»
import ZlibF.Proof.«public-deflate-init»

namespace Zlib.Deflate.Proofs.DefaultGzipInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
open Zlib.Trees.Proofs.Out (TreesStatic)
open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees)
set_option autoImplicit false

def settings (level : Int32) : ZlibF.Spec.Api.DeflParams := ⟨level.toInt.toNat, .gzip, 15, 8, 0⟩

theorem result_owned (h : Heap) (r : ZStreamRef) (level : Int32)
    (a1 a2 a3 : Array CtData) (x : Nat) :
    DeflateOwned h.nextBlk (resultState h r level a1 a2 a3) x ↔
      h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
  simp only [DeflateOwned, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
    Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState,
    baseState]
  simp only [Ptr.ref.injEq, BRef.blk.injEq, WRef.blk.injEq, and_true]
  omega

/-- Actual successful default allocation establishes the exact public
initial relation, with old-object frame and the five-object ledger. -/
theorem success_initial {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    :
    ∃ after, allocate (some r) level (r.put h (preparedStream z)) = .ok (Z_OK, after) ∧
      DeflateInitial h after r (settings level) := by
  let zp := preparedStream z
  let hp := r.put h zp
  have shape := shape_put hz zp
  have hfP : Fresh hp := shape.fresh (by simp [hp]) hf
  have huP : Uniq hp := shape.uniq hu
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have globalsP : TreesStatic hp.static := by simpa [hp] using globals_trees hg
  have allP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
    intro j hj
    simpa [hp] using allok j hj
  obtain ⟨a1, a2, a3, qa, hrun, hG, hLive⟩ := allocate_success hfP huP hzP haP globalsP allP level hl0 hl9
  let after := successHeap hp r zp level a1 a2 a3 qa
  let zf := resultStream hp r zp level
  let sf := resultState hp r level a1 a2 a3
  have nb : hp.nextBlk = h.nextBlk := by simp [hp]
  have hGood : DGood after r h.nextBlk zf sf := by simpa only [nb] using hG
  have owned : ∀ x, DeflateOwned h.nextBlk sf x ↔ h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
    intro x
    simpa only [nb] using result_owned hp r level a1 a2 a3 x
  have hFrame : Frame h after (StreamRoot r) := frame_trans r (frame_put r zp hf)
    (success_frame r zp level a1 a2 a3 qa hfP)
  refine ⟨after, hrun, zf, sf, hGood, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hFrame, ?_, owned⟩
  · simpa [zf, resultStream, rkZ, stateStream] using haP.1
  · simpa [zf, resultStream, rkZ, stateStream] using haP.2
  · simp only [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, settings]
    omega
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, settings]
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, absWrap,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · intro x
    simp only [LiveChange, not_false_eq_true, and_true] at *
    change after.live x ↔ h.live x ∨ DeflateOwned h.nextBlk sf x
    rw [owned]
    have live := hLive x
    rw [shape.live] at live
    simpa only [nb] using live

end Zlib.Deflate.Proofs.DefaultGzipInit
