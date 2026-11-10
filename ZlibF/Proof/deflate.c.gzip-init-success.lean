import ZlibF.Proof.«deflate.c.gzip-init-frame»

namespace Zlib.Deflate.Proofs.DefaultGzipInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
open Zlib.Trees.Proofs.Out (TreesStatic)
set_option autoImplicit false

def resultState (h : Heap) (r : ZStreamRef) (level : Int32) (a1 a2 a3 : Array CtData) : DeflateState :=
  finalState h.nextBlk r level (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) (h.nextBlk + 4) a1 a2 a3

/-- All five successful requests establish DGood by actual execution,
including hash clearing. No callee or initialized-state invariant is assumed. -/
theorem allocate_success {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      allocate (some r) level h = .ok (Z_OK, successHeap h r z level a1 a2 a3 qa) ∧
      DGood (successHeap h r z level a1 a2 a3 qa) r h.nextBlk (resultStream h r z level)
        (resultState h r level a1 a2 a3) ∧
      (∀ x, (successHeap h r z level a1 a2 a3 qa).live x ↔
        h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5) := by
  let ph := publishedHeap h r z
  have ha0 : h.allocOk h.nalloc = true := by simpa using ha 0 (by decide)
  have ha4 : ∀ j, j < 4 → ph.allocOk (ph.nalloc + j) = true := by
    intro j hj
    simpa [ph, publishedHeap, stateHeap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha (j + 1) (by omega)
  have hfp := (shape_put hz (stateStream z h.nextBlk)).fresh (by simp) hf
  have hup := (shape_put hz (stateStream z h.nextBlk)).uniq hu
  have hfP : Fresh ph := fresh_stateHeap hfp _
  have huP : Uniq ph := uniq_stateHeap hup hfp _
  have hzP : r.get ph = some (stateStream z h.nextBlk) := by
    simp [ph, publishedHeap, ZStreamRef.get_put_same hz]
  have hdP : DefAlloc (stateStream z h.nextBlk) := hd
  have hsP : ph.dstates h.nextBlk = some (baseState r) := by simp [ph, publishedHeap, stateHeap]
  have hst : TreesStatic ph.static := by simpa [ph, publishedHeap, stateHeap] using hs
  obtain ⟨hlR, htR, hbR, huR, hfR⟩ := ready_storage level hfP huP hzP hsP
    (by simp [ph, publishedHeap, stateHeap]) hdP rfl hst ha4
  obtain ⟨a1, a2, a3, qa, s1, s2, s3, hqa, hreset, hG, hLive⟩ :=
    reset_construct level hlR htR hbR huR hfR hl0 hl9
  refine ⟨a1, a2, a3, qa, ?_, ?_, ?_⟩
  · rw [allocate_to_finish hf hz hd.1 ha0 level, finish_to_reset _ _ _ _ ha4, hreset]
    rfl
  · simpa only [successHeap, resultStream, resultState, finalState,
      ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using hG
  · intro x
    have hc := ready_live hz level ha4 x
    have hr := hLive x
    simpa only [successHeap, resultStream] using hr.trans hc

end Zlib.Deflate.Proofs.DefaultGzipInit
