import ZlibF.Proof.«uncompr.c.local-buffer-coarse-frame»
import ZlibF.Proof.«uncompr.c.local-loop-resources»

namespace Zlib.Uncompr.Proof.LocalLoop
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.CallerFrame
set_option autoImplicit false

/-- The actual call advances within the same output allocation. -/
theorem loopBody_output_root (h after : Heap) (cutoff b zs : Nat)
    (z stream : ZStream) (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    ∀ x, ByteRoot stream.next_out x ↔ ByteRoot z.next_out x := by
  obtain ⟨rc, heap, stream2, state2, used, made, actual, checked, _, account, _⟩ :=
    loop_iteration_accounting h cutoff b zs z l s invariant allocator ranges.1 ranges.2.1 ranges.2.2
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have sameStream : stream2 = stream := Option.some.inj (checked.good.live.hz.symm.trans current.live.hz)
  subst stream2
  intro x
  rw [account.2.2.2.2.2.1]
  change ByteRoot (advance z.next_out made) x ↔ ByteRoot z.next_out x
  cases z.next_out with
  | null => rfl
  | ref ref off => cases ref <;> rfl

/-- The real output interval and private allocator footprint give a complete
ordinary frame for the actual body step. -/
theorem loopBody_frame (h after : Heap) (cutoff b zs : Nat)
    (z stream : ZStream) (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    Frame h after (fun x => (StreamRoot (.tab b) x ∨ InflateOwned zs s x) ∨ ByteRoot z.next_out x) := by
  have filled := refilledLocalStateJ h cutoff b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  have actual := (loopBody_inflate_run h b z l next after invariant.good.live.hz run).1
  obtain ⟨rc, heap, stream2, state2, used, made, run2, checked, _, _, _, _, account, _⟩ :=
    inflate_default_view_public_return_codes filled allocator buffers Z_NO_FLUSH
  have same := Except.ok.inj (run2.symm.trans actual)
  cases same
  have sameStream : stream2 = stream := Option.some.inj (checked.good.live.hz.symm.trans current.live.hz)
  subst stream2
  have exactFrame := inflate_default_view_public_frame_of_run filled allocator buffers actual current account
  have frame := LocalFrame.buffer_frame_object_frame exactFrame
  have refill : Frame h (refilledHeap h b z l) (StreamRoot (.tab b)) := by
    refine ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,?_⟩
    intro x live outside
    have ne : x ≠ b := outside
    simp [refilledHeap, ne]
  apply frame_trans_restrict refill frame
  intro x live outside
  refine ⟨fun root => outside (Or.inl (Or.inl root)), ?_⟩
  simpa only [refilledStream] using outside

/-- The actual entire outer loop has a frame in its original allocation
and output-root footprint, including windows allocated in earlier iterations. -/
theorem loop_go_frame (steps : Nat) (h after : Heap) (cutoff b zs : Nat)
    (z stream : ZStream) (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    Frame h after (fun x => (StreamRoot (.tab b) x ∨ InflateOwned zs s x) ∨ ByteRoot z.next_out x) := by
  induction steps generalizing h after z stream s state l next with
  | zero => simp [C.run,cdoWhile.go] at run
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, current1, allocator1,
      ranges1, nonnull1, _, _, _, _⟩ :=
      loop_iteration_closed h cutoff b zs z s l invariant allocator ranges nonnull
    have first := loopBody_frame h heap1 cutoff b zs z stream1 s state1 l _
      invariant allocator ranges body current1.good
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have tailRun : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps
          { refilledLocals z l with err := rc }) heap1 = .ok (next, after) := by
        simpa [C.run,cdoWhile.go,body',loopCondition,ok] using run
      have rest := ih heap1 after stream1 stream state1 state _ next current1 allocator1
        ranges1 nonnull1 tailRun current
      have owners := (loopBody_resources h heap1 cutoff b zs z stream1 s state1 l _
        invariant allocator ranges body current1.good).2.1
      have roots := loopBody_output_root h heap1 cutoff b zs z stream1 s state1 l _
        invariant allocator ranges body current1.good
      apply frame_trans_restrict first rest
      intro x live outside
      refine ⟨outside, ?_⟩
      rintro ((root | owned) | output)
      · exact outside (Or.inl (Or.inl root))
      · exact outside (Or.inl (Or.inr ((owners x live).mp owned)))
      · exact outside (Or.inr ((roots x).mp output))
    · have expected : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition (steps+1) l) h =
          .ok ({ refilledLocals z l with err := rc },heap1) := by
        simp [C.run,cdoWhile.go,body',loopCondition,ok]
      cases Except.ok.inj (expected.symm.trans run)
      exact first

#print axioms loopBody_output_root
#print axioms loopBody_frame
#print axioms loop_go_frame
end Zlib.Uncompr.Proof.LocalLoop
