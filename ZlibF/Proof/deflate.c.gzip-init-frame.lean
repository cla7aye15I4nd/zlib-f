import ZlibF.Proof.«deflate.c.gzip-init-storage»
import ZlibF.Proof.«deflate.c.init.frame»

namespace Zlib.Deflate.Proofs.DefaultGzipInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

def resultStream (h : Heap) (r : ZStreamRef) (z : ZStream) (level : Int32) : ZStream :=
  let ph := publishedHeap h r z
  rkZ (stateStream z h.nextBlk)
    (readyState r level ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3))

def successHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (level : Int32)
    (a1 a2 a3 : Array CtData) (qa : Array UInt16) : Heap :=
  let ph := publishedHeap h r z
  let rh := readyHeap ph h.nextBlk r level
  let dr := resetState h.nextBlk r level ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3) a1 a2 a3
  setD (setW (setD (r.put rh (resultStream h r z level)) h.nextBlk dr)
    (ph.nextBlk + 2) (clearHead qa 32768)) h.nextBlk (lmD dr)

/-- Every old object outside the caller stream is retained, even though
tree initialization and hash clearing write the newly allocated blocks. -/
theorem success_frame {h : Heap} (r : ZStreamRef) (z : ZStream) (level : Int32)
    (a1 a2 a3 : Array CtData) (qa : Array UInt16) (hf : Fresh h) :
    Frame h (successHeap h r z level a1 a2 a3 qa) (StreamRoot r) := by
  have next : (successHeap h r z level a1 a2 a3 qa).nextBlk = h.nextBlk + 5 := by
    simp only [successHeap, setD_nextBlk, setW, readyHeap, successfulBuffers,
      publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc]
  have count : (successHeap h r z level a1 a2 a3 qa).nalloc = h.nalloc + 5 := by
    simp only [successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
      publishedHeap, stateHeap, ZStreamRef.put_nalloc, Nat.add_assoc]
  refine frame_of_old (g := successHeap h r z level a1 a2 a3 qa) r hf ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try { simp [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW] }
  all_goals try omega
  intro x hx hn
  let ph := publishedHeap h r z
  let rd := readyState r level ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3)
  let dr := resetState h.nextBlk r level ph.nextBlk (ph.nextBlk + 1)
    (ph.nextBlk + 2) (ph.nextBlk + 3) a1 a2 a3
  have hp : h.nextBlk < ph.nextBlk := by simp [ph, publishedHeap, stateHeap]
  have hds : x ≠ h.nextBlk := by omega
  have hq : x ≠ ph.nextBlk + 2 := by omega
  have a : SlotSame h ph x :=
    (slot_put_except h r (stateStream z h.nextBlk) x hn).trans
      (slot_stateHeap_old _ (baseState r) x (by simpa using hx))
  have b := a.trans (slot_successfulBuffers_old ph x (by omega))
  have c := b.trans (slot_setD_except _ h.nextBlk rd x hds)
  have e := c.trans (slot_put_except _ r (resultStream h r z level) x hn)
  have f := e.trans (slot_setD_except _ h.nextBlk dr x hds)
  have g := f.trans (slot_setW_except _ (ph.nextBlk + 2) (clearHead qa 32768) x hq)
  exact g.trans (slot_setD_except _ h.nextBlk (lmD dr) x hds)

/-- Before reset, exactly the state and four successful requests are new. -/
theorem ready_live {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) (level : Int32)
    (ha : ∀ j, j < 4 → (publishedHeap h r z).allocOk ((publishedHeap h r z).nalloc + j) = true)
    (x : Nat) :
    (readyHeap (publishedHeap h r z) h.nextBlk r level).live x ↔
      h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
  let ph := publishedHeap h r z
  have he := (buffers_success ph ha).1
  have hp := (buffers_success ph ha).2
  have hs : (successfulBuffers ph).dstates h.nextBlk = some (baseState r) := by
    simp [successfulBuffers, ph, publishedHeap, stateHeap]
  have preserved := (shape_setD hs
    (readyState r level ph.nextBlk (ph.nextBlk + 1) (ph.nextBlk + 2) (ph.nextBlk + 3))).live x
  change (setD (successfulBuffers ph) h.nextBlk _).live x ↔ _
  rw [preserved, ← he, buffers_live, hp]
  have before : ph.live x ↔ h.live x ∨ x = h.nextBlk := by
    dsimp only [ph, publishedHeap]
    rw [stateHeap_live, (shape_put hz (stateStream z h.nextBlk)).live]
    simp
  rw [before]
  simp only [ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk]
  by_cases hl : h.live x <;> simp [hl, eq_comm] <;> omega

end Zlib.Deflate.Proofs.DefaultGzipInit
