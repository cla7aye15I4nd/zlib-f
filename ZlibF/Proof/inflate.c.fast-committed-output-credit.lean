import ZlibF.Proof.«inflate.c.fast-committed-restore-callee-loaded-v3»
import ZlibF.Proof.«inflate.c.output-credit-append»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false

theorem FastPassiveFrame.adler_credit
    {z zNext : ZStream} {s sNext : InflateState}
    {credited : List UInt8}
    (frame : FastPassiveFrame z zNext s sNext)
    (credit : AdlerCredit z s credited) :
    AdlerCredit zNext sNext credited := by
  rcases frame with ⟨check, wrap, flags, _, _, adler, _, _, _⟩
  rcases credit with ⟨wrap0, flags0, check0, adler0⟩
  exact ⟨wrap.trans wrap0, flags.trans flags0,
    check.trans check0, adler.trans (adler0.trans check.symm)⟩

theorem loaded_output_delta
    {slow loaded : IL} {made : Nat}
    (count : slow.left.toNat ≤ slow.out_.toNat)
    (out : loaded.out_ = slow.out_)
    (left : loaded.left.toNat + made = slow.left.toNat) :
    (loaded.out_ - loaded.left).toNat =
      (slow.out_ - slow.left).toNat + made := by
  have slowLe : slow.left ≤ slow.out_ :=
    UInt32.le_iff_toNat_le.mpr count
  have loadedLe : loaded.left ≤ loaded.out_ :=
    UInt32.le_iff_toNat_le.mpr (by rw [out]; omega)
  rw [UInt32.toNat_sub_of_le _ _ loadedLe,
    UInt32.toNat_sub_of_le _ _ slowLe, out]
  omega

/-- The observed accepted fast segment extends the actual checksum ledger.
Each branch uses the exact source-backed frame and physical new slice;
BAD remains a separate actual event. -/
theorem OutputSegment.append_credit
    {ctx : FastLoopContext} {p : Parameters ctx}
    {h loopHeap loadedHeap : Heap} {result : Zlib.Inffast.L}
    {z zNext : ZStream} {s loadedState : InflateState}
    {slow loaded : IL} {prior current : List UInt8}
    {credited made : Nat} {array : Array UInt8}
    (segment : OutputSegment p loopHeap result array made current)
    (ledger : OutputCredit h z s slow prior current credited)
    (frame : BufferFrame h loadedHeap
      (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
      [⟨slow.put, made⟩])
    (passive : FastPassiveFrame z zNext s loadedState)
    (slowCount : slow.left.toNat ≤ slow.out_.toNat)
    (loadedOut : loaded.out_ = slow.out_)
    (loadedLeft : loaded.left.toNat + made = slow.left.toNat)
    (loadedPut : loaded.put = inputAdvance slow.put made)
    (put : slow.put = .ref ctx.dest ctx.oo)
    (get : Space.get loadedHeap ctx.dest = some array)
    (bound : ctx.oo + made ≤ array.size) :
    (∃ tracked : Tracked p loopHeap result,
      WordSource tracked.toObservation ∧
      ∃ more, tracked.history = current ++ more ∧
        OutputCredit loadedHeap zNext loadedState loaded
          prior (current ++ more) credited) ∨
    (∃ ended : Ended p loopHeap result,
      WordSource ended.toObservation ∧
      ∃ more, ended.history = current ++ more ∧
        OutputCredit loadedHeap zNext loadedState loaded
          prior (current ++ more) credited) ∨
    (result.broke = true ∧ ∃ i,
      DefaultStateJ loopHeap ctx.r ctx.zs
        {ctx.z with msg := .ref (.str i) 0} {ctx.s with mode := BAD}) := by
  have credit := FastPassiveFrame.adler_credit passive ledger.checksum
  have delta := loaded_output_delta slowCount loadedOut loadedLeft
  rcases segment with ⟨tracked, word, more, length, bytes, history⟩ |
      ⟨ended, word, more, length, bytes, history⟩ | bad
  · have physical : ∃ ref off arr,
        slow.put = .ref ref off ∧
        loaded.put = .ref ref (off + more.length) ∧
        Space.get loadedHeap ref = some arr ∧
        off + more.length ≤ arr.size ∧
        ZlibF.Math.LZ77Copy.writtenBytes arr
          (off + more.length) more.length = more := by
      refine ⟨ctx.dest, ctx.oo, array, put, ?_, get, ?_, ?_⟩
      · rw [loadedPut, put, length]; rfl
      · simpa only [length] using bound
      · simpa only [length] using bytes
    have applied := OutputCredit.append_observed ledger
      (by simpa only [length] using frame) credit
      (by simpa only [length] using delta) physical
    exact Or.inl ⟨tracked, word, more, history, applied⟩
  · have physical : ∃ ref off arr,
        slow.put = .ref ref off ∧
        loaded.put = .ref ref (off + more.length) ∧
        Space.get loadedHeap ref = some arr ∧
        off + more.length ≤ arr.size ∧
        ZlibF.Math.LZ77Copy.writtenBytes arr
          (off + more.length) more.length = more := by
      refine ⟨ctx.dest, ctx.oo, array, put, ?_, get, ?_, ?_⟩
      · rw [loadedPut, put, length]; rfl
      · simpa only [length] using bound
      · simpa only [length] using bytes
    have applied := OutputCredit.append_observed ledger
      (by simpa only [length] using frame) credit
      (by simpa only [length] using delta) physical
    exact Or.inr (Or.inl ⟨ended, word, more, history, applied⟩)
  · exact Or.inr (Or.inr bad)

#print axioms FastPassiveFrame.adler_credit
#print axioms loaded_output_delta
#print axioms OutputSegment.append_credit
end Zlib.Inflate.Proofs.FastCommittedLoop
