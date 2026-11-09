import ZlibF.Proof.«uncompr.c.local-post-ranges»
import ZlibF.Proof.«uncompr.c.local-loop-resources-step»

namespace Zlib.Uncompr.Proof.LocalLoop
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

/-- Mathematical transport of the full outer remaining ranges through an
observed same-heap output frame and exact byte accounting. It accepts a coarse
or exact output interval. This is not a callee-contract or execution theorem. -/
theorem remaining_ranges_of_account_frame (h after : Heap) (cutoff b zs : Nat)
    (z stream : ZStream) (s state : InflateState) (l : UncLoop) (rc : Int32)
    (used made frameCount : Nat)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s)
    (current : LocalStateJ after cutoff (.tab b) zs stream state)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (account : StreamAccounting (refilledStream z l) stream used made)
    (frame : BufferFrame (refilledHeap h b z l) after
      (fun x => StreamRoot (.tab b) x ∨ InflateOwned zs s x) [⟨z.next_out, frameCount⟩])
    (owned : ∀ x, (refilledHeap h b z l).live x → InflateOwned zs state x → InflateOwned zs s x) :
    RemainingBuffers after b stream { refilledLocals z l with err := rc } ∧
    stream.next_out ≠ .null ∧
    (refilledLocals z l).len.toNat + stream.avail_in.toNat + used =
      l.len.toNat + z.avail_in.toNat ∧
    (refilledLocals z l).left.toNat + stream.avail_out.toNat + made =
      l.left.toNat + z.avail_out.toNat := by
  obtain ⟨input, output, separate⟩ := ranges
  have filledJ := refilledLocalStateJ h cutoff b zs z l s invariant
  have input0 := callerRange_refill h b z l invariant.good.live.hz z.next_in
    (l.len.toNat + z.avail_in.toNat) (l.len.toNat + z.avail_in.toNat) false input (Nat.le_refl _)
  have output0 := callerRange_refill h b z l invariant.good.live.hz z.next_out
    (l.left.toNat + z.avail_out.toNat) (l.left.toNat + z.avail_out.toNat) true output (Nat.le_refl _)
  obtain ⟨dest, off, array, ptr, get⟩ : ∃ dest off array,
      z.next_out = .ref dest off ∧ Space.get (refilledHeap h b z l) dest = some array := by
    rcases output with null | ⟨⟨xs, readable⟩, _⟩
    · exact False.elim (nonnull null)
    · rcases readable with null | ⟨dest, off, array, ptr, get, _⟩
      · exact False.elim (nonnull null.1)
      · exact ⟨dest, off, array, ptr, by rw [refill_get]; exact get⟩
  have frame' := frame
  rw [ptr] at frame'
  have inputAfter := LocalPostRanges.callerRange_after_bufferFrame filledJ current input0 get frame' owned
  have outputAfter := LocalPostRanges.callerRange_after_bufferFrame filledJ current output0 get frame' owned
  have inCount : (refilledLocals z l).len.toNat + stream.avail_in.toNat + used =
      l.len.toNat + z.avail_in.toNat := by
    have refill := refill_input_count z l
    have count := account.2.2.1
    omega
  have outCount : (refilledLocals z l).left.toNat + stream.avail_out.toNat + made =
      l.left.toNat + z.avail_out.toNat := by
    have refill := refill_output_count z l
    have count := account.2.2.2.1
    omega
  have usedBound : used ≤ l.len.toNat + z.avail_in.toNat := by omega
  have madeBound : made ≤ l.left.toNat + z.avail_out.toNat := by omega
  have inCursor : stream.next_in = inputAdvance z.next_in used := by
    cases pointer : z.next_in <;>
      simpa only [refilledStream, advance, inputAdvance, pointer] using account.2.2.2.2.1
  have outCursor : stream.next_out = inputAdvance z.next_out made := by
    cases pointer : z.next_out <;>
      simpa only [refilledStream, advance, inputAdvance, pointer] using account.2.2.2.2.2.1
  have inRemain : (refilledLocals z l).len.toNat + stream.avail_in.toNat =
      (l.len.toNat + z.avail_in.toNat) - used := by omega
  have outRemain : (refilledLocals z l).left.toNat + stream.avail_out.toNat =
      (l.left.toNat + z.avail_out.toNat) - made := by omega
  have remaining : RemainingBuffers after b stream { refilledLocals z l with err := rc } := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [inCursor, inRemain] using callerRange_advance inputAfter usedBound
    · simpa only [outCursor, outRemain] using callerRange_advance outputAfter madeBound
    · have first := inputAdvance_separate z.next_in z.next_out _ _ used usedBound separate
      have second := separate_advance_output (inputAdvance z.next_in used) z.next_out _ _ made madeBound first
      simpa only [inCursor, outCursor, inRemain, outRemain] using second
  have finalNonnull : stream.next_out ≠ .null := by
    rw [outCursor]
    cases ptr : z.next_out <;> simp [inputAdvance] at nonnull ⊢
    exact False.elim (nonnull ptr)
  exact ⟨remaining, finalNonnull, inCount, outCount⟩

#print axioms remaining_ranges_of_account_frame
end Zlib.Uncompr.Proof.LocalLoop
