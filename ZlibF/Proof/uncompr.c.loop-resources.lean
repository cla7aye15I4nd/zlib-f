import ZlibF.Proof.«uncompr.c.loop-safe»
import ZlibF.Proof.«inflate.c.owned-preserved»

/-!
# Allocation ledger of the actual uncompress core loop

All returning iterations preserve old decoder ownership and cancel their local
storage. The loop therefore has no abandoned window. Actual inflateEnd releases
exactly its decoder-owned graph at that boundary. The scalar-store wrapper tail
and initialization still need their composition proofs.
-/

namespace Zlib.Uncompr.Proof.Resources
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges

private theorem refilled_live (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop)
    (hz : h.streams b = some z) (x : Nat) : (refilledHeap h b z l).live x ↔ h.live x := by
  have shape := shape_put (r := .tab b) hz (refilledStream z l)
  have put : ZStreamRef.put h (.tab b) (refilledStream z l) = refilledHeap h b z l := by
    simp [ZStreamRef.put, hz, refilledHeap]
  rw [put] at shape
  exact shape.live x

/-- Every returning actual body step cancels its real local storage and preserves
ownership of old allocations. New live objects are precisely the new owned window. -/
theorem loopBody_resources (h after : Heap) (b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
    LiveChange h after (fun x => InflateOwned zs state x ∧ ¬ h.live x) (fun _ => False) ∧
    (∀ x, h.live x → (InflateOwned zs state x ↔ InflateOwned zs s x)) := by
  have filled := refilledDefaultStateJ h b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  have actual := (loopBody_inflate_run h b z l next after invariant.good.live.hz run).1
  have owned := inflate_default_view_public_owned_iff_of_live filled allocator buffers actual current
  obtain ⟨rc, final, z', s', liveRun, good, _, _, ledger⟩ :=
    inflate_default_view_public_live filled allocator buffers Z_NO_FLUSH
  have same := Except.ok.inj (liveRun.symm.trans actual)
  cases same
  have stateEq : s' = state := Option.some.inj (good.good.live.hs.symm.trans current.live.hs)
  rw [stateEq] at ledger
  constructor
  · intro x
    simpa only [refilled_live h b z l invariant.good.live.hz x] using ledger x
  · intro x live
    exact owned x ((refilled_live h b z l invariant.good.live.hz x).mpr live)

private theorem accumulate_liveChange {first second third : Heap} {ownedMid ownedFinal : Nat → Prop}
    (a : LiveChange first second (fun x => ownedMid x ∧ ¬ first.live x) (fun _ => False))
    (b : LiveChange second third (fun x => ownedFinal x ∧ ¬ second.live x) (fun _ => False))
    (kept : ∀ x, ownedMid x → ownedFinal x) :
    LiveChange first third (fun x => ownedFinal x ∧ ¬ first.live x) (fun _ => False) := by
  intro x
  constructor
  · intro live
    rcases (b x).mp live with ⟨mid, _⟩ | ⟨owner, new⟩
    · rcases (a x).mp mid with old | ⟨owner, new⟩
      · exact Or.inl old
      · exact Or.inr ⟨kept x owner, new⟩
    · refine Or.inr ⟨owner, ?_⟩
      intro old
      exact new ((a x).mpr (Or.inl ⟨old, by simp⟩))
  · rintro (⟨old, _⟩ | ⟨owner, new⟩)
    · exact (b x).mpr (Or.inl ⟨(a x).mpr (Or.inl ⟨old, by simp⟩), by simp⟩)
    · by_cases mid : second.live x
      · exact (b x).mpr (Or.inl ⟨mid, by simp⟩)
      · exact (b x).mpr (Or.inr ⟨owner, mid⟩)

/-- The exact allocation ledger composes over every real outer iteration.
A window allocated by an earlier call remains owned until inflateEnd releases it. -/
theorem loop_go_resources (steps : Nat) (h after : Heap) (b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
    LiveChange h after (fun x => InflateOwned zs state x ∧ ¬ h.live x) (fun _ => False) ∧
    (∀ x, h.live x → (InflateOwned zs state x ↔ InflateOwned zs s x)) := by
  induction steps generalizing h after z stream s state l next with
  | zero => simp [C.run, cdoWhile.go] at run
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, good1, allocator1,
      ranges1, nonnull1, _countIn, _countOut, _progress, _code⟩ :=
      loop_iteration_closed h b zs z s l invariant allocator ranges nonnull
    have first := loopBody_resources h heap1 b zs z stream1 s state1 l _
      invariant allocator ranges body good1.good
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have tailRun : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps
          { refilledLocals z l with err := rc }) heap1 = .ok (next, after) := by
        simpa [C.run, cdoWhile.go, body', loopCondition, ok] using run
      obtain ⟨rest, owners⟩ := ih heap1 after stream1 stream state1 state
        { refilledLocals z l with err := rc } next good1 allocator1 ranges1 nonnull1 tailRun current
      have kept (x : Nat) (owner : InflateOwned zs state1 x) : InflateOwned zs state x :=
        (owners x (good_inflate_owned_live good1.good owner)).mpr owner
      refine ⟨accumulate_liveChange first.1 rest kept, ?_⟩
      intro x live
      have midLive := (first.1 x).mpr (Or.inl ⟨live, by simp⟩)
      exact (owners x midLive).trans (first.2 x live)
    · have expected : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition (steps + 1) l) h =
          .ok ({ refilledLocals z l with err := rc }, heap1) := by
        simp [C.run, cdoWhile.go, body', loopCondition, ok]
      have same := Except.ok.inj (expected.symm.trans run)
      cases same
      have stateEq : state1 = state := Option.some.inj (good1.good.live.hs.symm.trans current.live.hs)
      simpa only [stateEq] using first

private theorem ownedBy_iff (zs : Nat) (s : InflateState) (x : Nat) :
    OwnedBy zs s x ↔ InflateOwned zs s x := by
  simp [OwnedBy, WinBlk, InflateOwned]

/-- At a real returning core boundary, actual inflateEnd releases every allocation
introduced by the loop and exactly the incoming decoder-owned allocations. Local
wrapper objects and caller storage remain live. Scalar stores in the wrapper tail
are a separate composition step. -/
theorem loop_return_cleanup (h after : Heap) (b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile (loopBody (some (.tab b))) loopCondition l) h = .ok (next, after))
    (current : DefaultStateJ after (.tab b) zs stream state) (finalAllocator : DefAlloc stream) :
    ∃ clean, C.run (Zlib.Inflate.inflateEnd (some (.tab b))) after = .ok (Z_OK, clean) ∧
      LiveChange h clean (fun _ => False) (InflateOwned zs s) := by
  obtain ⟨ledger, owned⟩ := loop_go_resources C.fuel h after b zs z stream s state l next
    invariant allocator ranges nonnull run current.good
  obtain ⟨clean, endRun, _heap, _uniq, _fresh, _get, allocations, _check⟩ :=
    inflateEnd_safe current.good finalAllocator.2
  have ownAll : after.Owns (fun x => after.live x) := fun _ => Iff.rfl
  have final := allocations (fun x => after.live x) ownAll
  refine ⟨clean, endRun, ?_⟩
  intro x
  rw [final x]
  dsimp only
  rw [ownedBy_iff]
  constructor
  · rintro ⟨live, unowned⟩
    rcases (ledger x).mp live with ⟨old, _⟩ | ⟨owner, _⟩
    · exact Or.inl ⟨old, fun owner => unowned ((owned x old).mpr owner)⟩
    · exact False.elim (unowned owner)
  · rintro (⟨old, unowned⟩ | impossible)
    · exact ⟨(ledger x).mpr (Or.inl ⟨old, by simp⟩), fun owner => unowned ((owned x old).mp owner)⟩
    · exact False.elim impossible

#print axioms loopBody_resources
#print axioms loop_go_resources
#print axioms loop_return_cleanup

end Zlib.Uncompr.Proof.Resources
