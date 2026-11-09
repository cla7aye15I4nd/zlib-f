import ZlibF.Proof.«uncompr.c.finish»

/-!
# Caller-frame composition on old allocations

Old objects outside a footprint retain their allocation presence. This permits
composition while the actual loop allocates its window. Real initialization
frames every original caller object, and the actual local cleanup has its exact
two-root footprint. Complete wrapper framing is a separate composition result.
-/

namespace Zlib.Uncompr.Proof.CallerFrame
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Finish

/-- A frame retains presence at an old allocation outside its footprint. -/
theorem frame_live_at {before after : Heap} {changed : Nat → Prop}
    (frame : Frame before after changed) (b : Nat) (live : before.live b) (outside : ¬ changed b) :
    after.live b ↔ before.live b := by
  obtain ⟨bytes, words, streams, headers, dstates, istates, gzstates, _ro⟩ := frame.2.2.2.2.2 b live outside
  simp only [Heap.live, bytes, words, streams, headers, dstates, istates, gzstates]

/-- Frames compose on the retained old domain. New allocations are admitted;
no global Shape equality is required. -/
theorem frame_trans_restrict {first second third : Heap} {leftChanged rightChanged changed : Nat → Prop}
    (left : Frame first second leftChanged) (right : Frame second third rightChanged)
    (exclude : ∀ b, first.live b → ¬ changed b → ¬ leftChanged b ∧ ¬ rightChanged b) :
    Frame first third changed := by
  have leftFrame := left
  obtain ⟨staticL, allocL, garbageL, nextL, countL, slotsL⟩ := left
  obtain ⟨staticR, allocR, garbageR, nextR, countR, slotsR⟩ := right
  refine ⟨staticL.trans staticR, allocL.trans allocR, garbageL.trans garbageR,
    Nat.le_trans nextL nextR, Nat.le_trans countL countR, ?_⟩
  intro b live outside
  obtain ⟨outsideL, outsideR⟩ := exclude b live outside
  have liveSecond := (frame_live_at leftFrame b live outsideL).mpr live
  obtain ⟨bL, wL, sL, hL, dL, iL, gL, rL⟩ := slotsL b live outsideL
  obtain ⟨bR, wR, sR, hR, dR, iR, gR, rR⟩ := slotsR b liveSecond outsideR
  exact ⟨bR.trans bL, wR.trans wL, sR.trans sL, hR.trans hL,
    dR.trans dL, iR.trans iL, gR.trans gL, rR.trans rL⟩

/-- Real successful wrapper initialization changes no original caller object. -/
theorem core_frame (h : Heap) (source dest : BPtr) (capacity : UInt64) (fresh : Fresh h) :
    Frame h (coreHeap h source dest capacity) (fun _ => False) := by
  rw [coreHeap_eq]
  refine ⟨rfl, rfl, rfl, by change h.nextBlk ≤ h.nextBlk + 3; omega,
    by change h.nalloc ≤ h.nalloc + 1; omega, ?_⟩
  intro b live _
  have below := fresh.lt live
  simp [show b ≠ h.nextBlk by omega, show b ≠ h.nextBlk + 1 by omega,
    show b ≠ h.nextBlk + 2 by omega]

/-- The actual final two automatic frees alter only their allocation roots. -/
theorem released_frame (h : Heap) (stream reserved : Nat) :
    Frame h (releasedHeap h stream reserved) (fun b => b = stream ∨ b = reserved) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ outside
  have streamNe : b ≠ stream := fun eq => outside (Or.inl eq)
  have reservedNe : b ≠ reserved := fun eq => outside (Or.inr eq)
  simp [releasedHeap, streamNe, reservedNe]

#print axioms frame_trans_restrict
#print axioms core_frame
#print axioms released_frame
end Zlib.Uncompr.Proof.CallerFrame
