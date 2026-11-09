import ZlibF.Proof.«uncompr.c.caller-frame»

/-!
# Caller-frame cleanup composition

The real old-owner equivalence excludes original caller roots from a later
window. Frames through the decoder, actual End and both local frees therefore
compose on a pure expected caller heap with the original allocation domain.
This is a support theorem; actual output and scalar Store mirrors still need
their whole-wrapper instantiation.
-/

namespace Zlib.Uncompr.Proof.FinalFrame
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.CallerFrame Zlib.Uncompr.Proof.Finish

theorem owner_outside_old (h : Heap) (source dest : BPtr) (capacity : UInt64) (state : InflateState)
    (fresh : Fresh h)
    (owners : ∀ b, (coreHeap h source dest capacity).live b →
      (InflateOwned (h.nextBlk + 2) state b ↔ InflateOwned (h.nextBlk + 2) (initializedState h) b)) :
    ∀ b, h.live b → ¬ InflateOwned (h.nextBlk + 2) state b := by
  intro b live owner
  have coreLive := (frame_live_at (core_frame h source dest capacity fresh) b live (by simp)).mpr live
  have initial := (owners b coreLive).mp owner
  have below := fresh.lt live
  rcases initial with stateRoot | windowRoot
  · omega
  · rw [initial_window_null] at windowRoot
    cases windowRoot

theorem cleanup_caller_frame
    (h caller expected written clean : Heap) (source dest : BPtr) (capacity : UInt64) (state : InflateState)
    (fresh : Fresh h) (shape : Shape h caller)
    (base : Frame caller expected (fun _ => False))
    (body : Frame expected written (fun b => StreamRoot (.tab h.nextBlk) b ∨
      InflateOwned (h.nextBlk + 2) (initializedState h) b))
    (endFrame : Frame written clean (fun b => StreamRoot (.tab h.nextBlk) b ∨ InflateOwned (h.nextBlk + 2) state b))
    (owners : ∀ b, (coreHeap h source dest capacity).live b →
      (InflateOwned (h.nextBlk + 2) state b ↔ InflateOwned (h.nextBlk + 2) (initializedState h) b)) :
    Frame caller (releasedHeap clean h.nextBlk (h.nextBlk + 1)) (fun _ => False) := by
  have old (b : Nat) (live : caller.live b) : h.live b := (shape.live b).mp live
  have initialOutside (b : Nat) (live : caller.live b) :
      ¬ (StreamRoot (.tab h.nextBlk) b ∨ InflateOwned (h.nextBlk + 2) (initializedState h) b) := by
    have below := fresh.lt (old b live)
    rintro (streamRoot | stateRoot | windowRoot)
    · change b = h.nextBlk at streamRoot
      omega
    · omega
    · rw [initial_window_null] at windowRoot
      cases windowRoot
  have currentOutside (b : Nat) (live : caller.live b) :
      ¬ (StreamRoot (.tab h.nextBlk) b ∨ InflateOwned (h.nextBlk + 2) state b) := by
    rintro (streamRoot | owner)
    · have below := fresh.lt (old b live)
      change b = h.nextBlk at streamRoot
      omega
    · exact owner_outside_old h source dest capacity state fresh owners b (old b live) owner
  have afterBody : Frame caller written (fun _ => False) := frame_trans_restrict base body (fun b live _ => ⟨by simp, initialOutside b live⟩)
  have afterEnd : Frame caller clean (fun _ => False) := frame_trans_restrict afterBody endFrame (fun b live _ => ⟨by simp, currentOutside b live⟩)
  apply frame_trans_restrict afterEnd (released_frame clean h.nextBlk (h.nextBlk + 1))
  intro b live _
  have below := fresh.lt (old b live)
  exact ⟨by simp, by omega⟩

#print axioms cleanup_caller_frame
end Zlib.Uncompr.Proof.FinalFrame
