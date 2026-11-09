import ZlibF.Proof.«uncompr.c.local-loop-closed»

namespace Zlib.Uncompr.Proof.LocalLoop
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

/-- The whole actual fueled loop is safe and exits with a non-OK decoder code.
Its input/output counts are exact natural differences. The fuel bound is on
remaining caller bytes, independent of the compressed data's format. -/
theorem loop_go_safe (steps : Nat) (h : Heap) (cutoff b zs : Nat) (z : ZStream) (s : InflateState) (l : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (budget : remainingBudget z l < steps) :
    ∃ next after stream state used made,
      C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after) ∧
      LocalStateJ after cutoff (.tab b) zs stream state ∧ DefAlloc stream ∧
      RemainingBuffers after b stream next ∧ stream.next_out ≠ .null ∧
      next.err ≠ Z_OK ∧ PublicInflateCode next.err ∧
      remainingInput stream next + used = remainingInput z l ∧
      remainingOutput stream next + made = remainingOutput z l := by
  induction steps generalizing h z s l with
  | zero => omega
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, current, allocator1,
      ranges1, nonnull1, countIn, countOut, progress, code⟩ :=
      loop_iteration_closed h cutoff b zs z s l invariant allocator ranges nonnull
    let next := { refilledLocals z l with err := rc }
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have strict := progress ok
      have smaller : remainingBudget stream1 next < steps := by
        dsimp only [remainingBudget, remainingInput, remainingOutput, next] at *
        omega
      obtain ⟨final, after, stream, state, consumed, produced, run, finalJ,
        finalAllocator, finalRanges, finalNonnull, stopped, codes, inputs, outputs⟩ :=
        ih heap1 stream1 state1 next current allocator1 ranges1 nonnull1 smaller
      refine ⟨final, after, stream, state, used + consumed, made + produced,
        ?_, finalJ, finalAllocator, finalRanges, finalNonnull, stopped, codes, ?_, ?_⟩
      · have run' := run
        simp only [C.run] at run'
        simpa [C.run, cdoWhile.go, body', loopCondition, next, ok] using run'
      · dsimp only [remainingInput, next] at inputs ⊢
        omega
      · dsimp only [remainingOutput, next] at outputs ⊢
        omega
    · refine ⟨next, heap1, stream1, state1, used, made, ?_, current,
        allocator1, ranges1, nonnull1, ok, code, countIn, countOut⟩
      simp [C.run, cdoWhile.go, body', loopCondition, next, ok]

/-- The exact source core cdoWhile terminates without a fault on the actual platform
and leaves exact consumed/produced counts, the initialized representation and caller
ranges on one returned heap. This does not assert stream-format correctness. -/
theorem loop_safe (h : Heap) (cutoff b zs : Nat) (z : ZStream) (s : InflateState) (l : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (inputNull : z.next_in = .null → remainingInput z l = 0) :
    ∃ next after stream state used made,
      C.run (cdoWhile (loopBody (some (.tab b))) loopCondition l) h = .ok (next, after) ∧
      LocalStateJ after cutoff (.tab b) zs stream state ∧ DefAlloc stream ∧
      RemainingBuffers after b stream next ∧ stream.next_out ≠ .null ∧
      next.err ≠ Z_OK ∧ PublicInflateCode next.err ∧
      remainingInput stream next + used = remainingInput z l ∧
      remainingOutput stream next + made = remainingOutput z l := by
  exact loop_go_safe C.fuel h cutoff b zs z s l invariant allocator ranges nonnull
    (remainingBudget_lt_fuel h cutoff b zs z s l invariant ranges nonnull inputNull)


#print axioms loop_go_safe
#print axioms loop_safe
end Zlib.Uncompr.Proof.LocalLoop
