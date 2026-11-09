import ZlibF.Proof.«uncompr.c.local-loop-iteration»
import ZlibF.Proof.«uncompr.c.loop-safe»
import ZlibF.Proof.«inflate.c.local-public-resources-origin»
import ZlibF.Proof.«inflate.c.local-public-resources-live»

namespace Zlib.Uncompr.Proof.LocalLoop
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

private theorem refilled_live (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop)
    (hz : h.streams b = some z) (x : Nat) : (refilledHeap h b z l).live x ↔ h.live x := by
  have shape := shape_put (r := .tab b) hz (refilledStream z l)
  have put : ZStreamRef.put h (.tab b) (refilledStream z l) = refilledHeap h b z l := by
    simp [ZStreamRef.put, hz, refilledHeap]
  rw [put] at shape
  exact shape.live x

/-- Observe the real public allocator on the same actual wrapper iteration.
Its four-byte local is freed. The only possible new live allocation is the
actual new window at old nextBlk+1, and every old owner remains an owner. -/
theorem loopBody_resources (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    LiveChange h after (fun x => InflateOwned zs state x ∧ ¬ h.live x) (fun _ => False) ∧
    (∀ x, h.live x → (InflateOwned zs state x ↔ InflateOwned zs s x)) ∧
    h.nextBlk + 1 ≤ after.nextBlk ∧
    (state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk (h.nextBlk + 1)) 0)) := by
  have filled := refilledLocalStateJ h cutoff b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  have actual := (loopBody_inflate_run h b z l next after invariant.good.live.hz run).1
  obtain ⟨rc, final, z', s', liveRun, good, _, _, ledger⟩ :=
    inflate_default_view_public_live filled allocator buffers Z_NO_FLUSH
  have same := Except.ok.inj (liveRun.symm.trans actual)
  cases same
  have stateEq : s' = state := Option.some.inj (good.good.live.hs.symm.trans current.live.hs)
  rw [stateEq] at ledger
  obtain ⟨rc2, heap2, z2, s2, originRun, finalJ, _, _, update, nextCount, allocCount, origin⟩ :=
    inflate_default_view_public_origins filled allocator buffers Z_NO_FLUSH
  have same2 := Except.ok.inj (originRun.symm.trans actual)
  cases same2
  have stateEq2 : s2 = state := Option.some.inj (finalJ.good.live.hs.symm.trans current.live.hs)
  rw [stateEq2] at origin
  have owners := public_owned_old_iff_of_origin (zs := zs) filled.good.fresh origin
  refine ⟨?_, ?_, ?_, origin⟩
  · intro x
    simpa only [refilled_live h b z l invariant.good.live.hz x] using ledger x
  · intro x live
    exact owners x ((refilled_live h b z l invariant.good.live.hz x).mpr live)
  · change after.nextBlk = h.nextBlk + 1 + _ at nextCount
    change h.nextBlk + 1 ≤ after.nextBlk
    omega

/-- The real window-origin rule preserves a stronger original-core age.
In particular, the wrapper reserved object at cutoff+1 stays unowned. -/
theorem loopBody_window_age (h after : Heap) (cutoff b zs firstWindow : Nat)
    (z stream : ZStream) (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state)
    (nextAge : firstWindow ≤ h.nextBlk)
    (windowAge : ∀ w, s.window = .ref (.blk w) 0 → firstWindow ≤ w) :
    firstWindow ≤ after.nextBlk ∧ ∀ w, state.window = .ref (.blk w) 0 → firstWindow ≤ w := by
  obtain ⟨_, _, next, origin⟩ := loopBody_resources h after cutoff b zs z stream s state l next
    invariant allocator ranges run current
  refine ⟨by omega, ?_⟩
  intro w window
  rcases origin with old | ⟨_, fresh⟩
  · exact windowAge w (old.symm.trans window)
  · have same : h.nextBlk + 1 = w := by cases fresh.symm.trans window; rfl
    omega

#print axioms loopBody_resources
#print axioms loopBody_window_age
end Zlib.Uncompr.Proof.LocalLoop
