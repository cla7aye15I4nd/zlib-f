import ZlibF.Proof.«uncompr.c.local-refill-post»

namespace Zlib.Uncompr.Proof.LocalLoop
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

private theorem callerRange_fits {h : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (range : CallerRange h r p n write)
    (nonnull : p ≠ .null) : n < 2 ^ 63 := by
  rcases range with null | ⟨⟨xs, readable⟩, _⟩
  · exact False.elim (nonnull null)
  · rcases readable with null | ⟨ref, off, array, ptr, get, room, _⟩
    · exact False.elim (nonnull null.1)
    · have bound := platform ref array get
      unfold ZlibF.PlatformMemory.byteObjectLimit at bound
      omega

/-- The actual remaining ranges fit the outer loop's fixed fuel. The null input
binding denotes zero remaining input, as ensured by the wrapper's argument checks. -/
theorem remainingBudget_lt_fuel (h : Heap) (cutoff b zs : Nat) (z : ZStream) (s : InflateState) (l : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (ranges : RemainingBuffers h b z l)
    (nonnull : z.next_out ≠ .null) (inputNull : z.next_in = .null → remainingInput z l = 0) :
    remainingBudget z l < C.fuel := by
  have input : remainingInput z l < 2 ^ 63 := by
    by_cases null : z.next_in = .null
    · rw [inputNull null]
      decide
    · exact callerRange_fits invariant.platform ranges.1 null
  have output : remainingOutput z l < 2 ^ 63 :=
    callerRange_fits invariant.platform ranges.2.1 nonnull
  have budget := two_object_loop_budget (remainingInput z l) (remainingOutput z l) input output
  unfold remainingBudget
  omega


#print axioms remainingBudget_lt_fuel
end Zlib.Uncompr.Proof.LocalLoop
