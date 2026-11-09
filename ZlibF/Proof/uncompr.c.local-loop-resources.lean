import ZlibF.Proof.«uncompr.c.local-loop-safe»
import ZlibF.Proof.«inflate.c.local-end»

namespace Zlib.Uncompr.Proof.LocalLoop
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

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
theorem loop_go_resources (steps : Nat) (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    LiveChange h after (fun x => InflateOwned zs state x ∧ ¬ h.live x) (fun _ => False) ∧
    (∀ x, h.live x → (InflateOwned zs state x ↔ InflateOwned zs s x)) := by
  induction steps generalizing h after z stream s state l next with
  | zero => simp [C.run, cdoWhile.go] at run
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, good1, allocator1,
      ranges1, nonnull1, _countIn, _countOut, _progress, _code⟩ :=
      loop_iteration_closed h cutoff b zs z s l invariant allocator ranges nonnull
    have first := loopBody_resources h heap1 cutoff b zs z stream1 s state1 l _
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
        (owners x (local_inflate_owned_live good1.good owner)).mpr owner
      refine ⟨accumulate_liveChange first.1 rest kept, ?_⟩
      intro x live
      have midLive := (first.1 x).mpr (Or.inl ⟨live, by simp⟩)
      exact (owners x midLive).trans (first.2.1 x live)
    · have expected : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition (steps + 1) l) h =
          .ok ({ refilledLocals z l with err := rc }, heap1) := by
        simp [C.run, cdoWhile.go, body', loopCondition, ok]
      have same := Except.ok.inj (expected.symm.trans run)
      cases same
      have stateEq : state1 = state := Option.some.inj (good1.good.live.hs.symm.trans current.live.hs)
      exact ⟨by simpa only [stateEq] using first.1, by simpa only [stateEq] using first.2.1⟩


#print axioms loop_go_resources
end Zlib.Uncompr.Proof.LocalLoop
