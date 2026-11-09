import ZlibF.Proof.«uncompr.c.local-wrapper-shape-slots»

namespace Zlib.Uncompr.Proof.LocalWrapperShape
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.LocalLoop
set_option autoImplicit false

theorem owned_age {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : LocalStateJ h cutoff r zs z s) :
    ∀ x, InflateOwned zs s x → cutoff ≤ x := by
  intro x owner
  rcases owner with state | window
  · subst x; exact invariant.roots.state
  · exact invariant.roots.window x window

/-- Output contents may change, but every older allocation retains its
own table type through the actual refill and complete inflate call. -/
theorem loopBody_shape (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : LocalStateJ after cutoff (.tab b) zs stream state) : ShapeBelow h after cutoff := by
  obtain ⟨rc, final, z', s', used, made, actual, checked, _finalAllocator,
    account, _codes, _countIn, _countOut, _progress, _strict⟩ :=
    loop_iteration_accounting h cutoff b zs z l s invariant allocator ranges.1 ranges.2.1 ranges.2.2
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have streamEq : z' = stream := Option.some.inj (checked.good.live.hz.symm.trans current.good.live.hz)
  subst z'
  have filled := refilledLocalStateJ h cutoff b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  have decoderRun := (loopBody_inflate_run h b z l _ after invariant.good.live.hz actual).1
  have frame := inflate_default_view_public_frame_of_run filled allocator buffers decoderRun current.good account
  change BufferFrame (refilledHeap h b z l) after
    (fun x => StreamRoot (.tab b) x ∨ InflateOwned zs s x) [⟨z.next_out, made⟩] at frame
  have shape0 : Shape h (refilledHeap h b z l) := by
    have shape := shape_put (r := .tab b) invariant.good.live.hz (refilledStream z l)
    have put : ZStreamRef.put h (.tab b) (refilledStream z l) = refilledHeap h b z l := by
      have hz : h.streams b = some z := invariant.good.live.hz
      simp [ZStreamRef.put, hz, refilledHeap]
    rwa [put] at shape
  obtain ⟨dest, off, array, pointer, get⟩ : ∃ dest off array,
      z.next_out = .ref dest off ∧ Space.get (refilledHeap h b z l) dest = some array := by
    rcases ranges.2.1 with null | ⟨⟨ys, readable⟩, _⟩
    · exact False.elim (nonnull null)
    · rcases readable with null | ⟨dest, off, array, pointer, get, _⟩
      · exact False.elim (nonnull null.1)
      · exact ⟨dest, off, array, pointer, by rw [refill_get]; exact get⟩
  rw [pointer] at frame
  have age : ∀ x, (StreamRoot (.tab b) x ∨ InflateOwned zs s x) → cutoff ≤ x := by
    intro x root
    exact root.elim (invariant.roots.stream x) (owned_age invariant x)
  have ledger := (loopBody_resources h after cutoff b zs z stream s state l _
    invariant allocator ranges actual current.good).1
  have noNew : ∀ x, x < cutoff → after.live x → (refilledHeap h b z l).live x := by
    intro x below alive
    rcases (ledger x).mp alive with ⟨old, _⟩ | ⟨owner, _⟩
    · exact (shape0.live x).mpr old
    · have later := owned_age current x owner
      omega
  exact ShapeBelow.trans (fun x _ => shape0 x) (shapeBelow_of_bufferFrame get frame age noNew)

/-- Pointwise type preservation accumulates through the same actual loop.
No uniqueness of objects below the decoder's initialization cutoff is used. -/
theorem loop_go_shape (steps : Nat) (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : LocalStateJ after cutoff (.tab b) zs stream state) : ShapeBelow h after cutoff := by
  induction steps generalizing h after z stream s state l next with
  | zero => simp [C.run, cdoWhile.go] at run
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, good1, allocator1,
      ranges1, nonnull1, _countIn, _countOut, _progress, _code⟩ :=
      loop_iteration_closed h cutoff b zs z s l invariant allocator ranges nonnull
    have first := loopBody_shape h heap1 cutoff b zs z stream1 s state1 l _
      invariant allocator ranges nonnull body good1
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have tailRun : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps
          { refilledLocals z l with err := rc }) heap1 = .ok (next, after) := by
        simpa [C.run, cdoWhile.go, body', loopCondition, ok] using run
      exact first.trans (ih heap1 after stream1 stream state1 state
        { refilledLocals z l with err := rc } next good1 allocator1 ranges1 nonnull1 tailRun current)
    · have expected : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition (steps + 1) l) h =
          .ok ({ refilledLocals z l with err := rc }, heap1) := by
        simp [C.run, cdoWhile.go, body', loopCondition, ok]
      have same := Except.ok.inj (expected.symm.trans run)
      cases same
      exact first

#print axioms loopBody_shape
#print axioms loop_go_shape
end Zlib.Uncompr.Proof.LocalWrapperShape
