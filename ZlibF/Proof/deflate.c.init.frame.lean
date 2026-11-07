import ZlibF.Proof.«deflate.c.init.success»

/-! # deflate.c: old-object frame for default initialization -/

namespace Zlib.Deflate.Proofs.DefaultInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem slot_put_except (h : Heap) (r : ZStreamRef) (z : ZStream) (x : Nat)
    (hn : ¬ StreamRoot r x) : SlotSame h (r.put h z) x := by
  cases r with
  | tab i =>
    have hi : x ≠ i := hn
    simp only [ZStreamRef.put]
    split <;> simp [SlotSame, upd_ne _ _ _ _ hi]
  | in_gzstate_strm i =>
    have hi : x ≠ i := hn
    simp only [ZStreamRef.put]
    split <;> simp [SlotSame, upd_ne _ _ _ _ hi]

theorem slot_setD_except (h : Heap) (ds : Nat) (d : DeflateState) (x : Nat) (hn : x ≠ ds) :
    SlotSame h (setD h ds d) x := by simp [SlotSame, setD, upd_ne _ _ _ _ hn]

theorem slot_setW_except (h : Heap) (q : Nat) (a : Array UInt16) (x : Nat) (hn : x ≠ q) :
    SlotSame h (setW h q a) x := by simp [SlotSame, setW, upd_ne _ _ _ _ hn]

theorem slot_stateHeap_old (h : Heap) (d : DeflateState) (x : Nat) (hx : x < h.nextBlk) :
    SlotSame h (stateHeap h d) x := by
  simp [SlotSame, stateHeap, upd_ne _ _ _ _ (show x ≠ h.nextBlk by omega)]

theorem slot_successfulBuffers_old (h : Heap) (x : Nat) (hx : x < h.nextBlk) :
    SlotSame h (successfulBuffers h) x := by
  have h0 : x ≠ h.nextBlk := by omega
  have h1 : x ≠ h.nextBlk + 1 := by omega
  have h2 : x ≠ h.nextBlk + 2 := by omega
  have h3 : x ≠ h.nextBlk + 3 := by omega
  simp [SlotSame, successfulBuffers, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1,
    upd_ne _ _ _ _ h2, upd_ne _ _ _ _ h3]

theorem frame_of_old {h g : Heap} (r : ZStreamRef) (hf : Fresh h)
    (hs : h.static = g.static) (ha : h.allocOk = g.allocOk) (hg : h.garbage = g.garbage)
    (hn : h.nextBlk ≤ g.nextBlk) (hc : h.nalloc ≤ g.nalloc)
    (hold : ∀ x, x < h.nextBlk → ¬ StreamRoot r x → SlotSame h g x) : Frame h g (StreamRoot r) := by
  exact ⟨hs, ha, hg, hn, hc, fun x hl hx => hold x (hf.lt hl) hx⟩

theorem SlotSame.live {h g : Heap} {x : Nat} (hs : SlotSame h g x) : g.live x ↔ h.live x := by
  rcases hs with ⟨a, b, c, d, e, f, k, _⟩
  simp only [Heap.live, a, b, c, d, e, f, k]

theorem frame_trans {h g j : Heap} (r : ZStreamRef)
    (a : Frame h g (StreamRoot r)) (b : Frame g j (StreamRoot r)) : Frame h j (StreamRoot r) := by
  rcases a with ⟨as_, aa, ag, an, ac, ao⟩
  rcases b with ⟨bs, ba, bg, bn, bc, bo⟩
  refine ⟨as_.trans bs, aa.trans ba, ag.trans bg, Nat.le_trans an bn, Nat.le_trans ac bc, ?_⟩
  intro x hl hn
  have first : SlotSame h g x := ao x hl hn
  exact first.trans (bo x (first.live.mpr hl) hn)

theorem frame_put {h : Heap} (r : ZStreamRef) (z : ZStream) (hf : Fresh h) :
    Frame h (r.put h z) (StreamRoot r) := by
  refine frame_of_old r hf (by simp) (by simp) (by simp) (by simp) (by simp) ?_
  exact fun x _ hn => slot_put_except h r z x hn

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

end Zlib.Deflate.Proofs.DefaultInit
