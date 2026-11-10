import ZlibF.Proof.«inflate.c.header-actual-tables-classifier»
import ZlibF.Proof.«inflate.c.constructor-rejection-certificates»

namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inftrees
open Zlib.Inflate.Proofs Zlib.Inftrees.Proofs Zlib.Inftrees.Spec
open Zlib.Inftrees.Proofs.ConstructorRejects
set_option autoImplicit false

/-- Actual rejection provenance implies rejection of an original decoded
payload alphabet. The second constructor reads the unchanged original lens
array and counts after the real successful LENS call; no parser relation,
acceptable alphabet or callee contract is assumed. -/
theorem RejectedConstructorTrace.alphabets_unacceptable
    {h : Heap} {zs : Nat} {s state : InflateState}
    (trace : RejectedConstructorTrace h zs s state) :
    (¬ Acceptable .litLen (lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)) ∨
    (¬ Acceptable .dist (lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) := by
  rcases trace with first | second
  · obtain ⟨next, root, work, codes, _stateEq, call⟩ := first
    obtain ⟨pre, after, actual, _frame, _codesGet⟩ := call
    have sourceGet : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_lens zs) = some s.lens := by
      simpa only [clLensPre] using
        WRef.get_istate_lens (setI_istates_same h zs (clLensPre zs s))
    have rejected := lens_failure_not_acceptable pre sourceGet actual rfl
    exact Or.inl (by simpa only [lensList, lensOf, Nat.zero_add] using rejected)
  · obtain ⟨nextL, bitsL, workL, codesL, middle, offset, nextD, bitsD, workD, codesD,
      middleEq, _next, _stateEq, _lengthCall, distanceCall⟩ := second
    obtain ⟨pre, after, actual, _frame, _codesGet⟩ := distanceCall
    have sourceGet : Space.get (setI (setI h zs middle) zs (clDistPre middle))
        (WRef.istate_lens zs) = some middle.lens := by
      simpa only [clDistPre] using WRef.get_istate_lens
        (setI_istates_same (setI h zs middle) zs (clDistPre middle))
    have rejected := dists_failure_not_acceptable pre sourceGet actual rfl
    exact Or.inr (by simpa only [middleEq, clLensResult, clLensPre, lensList, lensOf] using rejected)

/-- The automatic actual tables classifier's rejected output carries the
same source-alphabet certificate; actual rejection needs no future oracle. -/
theorem TablesRejected.alphabets_unacceptable
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    (rejected : TablesRejected c h r zs z s l) :
    (¬ Acceptable .litLen (lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)) ∨
    (¬ Acceptable .dist (lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :=
  rejected.calls.alphabets_unacceptable

/-- Independent payload alphabet acceptance contradicts a real pair
constructor rejection on that same original decoded lens array. -/
theorem RejectedConstructorTrace.contradicts_alphabets
    {h : Heap} {zs : Nat} {s state : InflateState}
    (trace : RejectedConstructorTrace h zs s state)
    (lengths : Acceptable .litLen (lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat))
    (distances : Acceptable .dist (lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    False := by
  rcases trace.alphabets_unacceptable with rejected | rejected
  · exact rejected lengths
  · exact rejected distances

#print axioms RejectedConstructorTrace.alphabets_unacceptable
#print axioms TablesRejected.alphabets_unacceptable
#print axioms RejectedConstructorTrace.contradicts_alphabets
end Zlib.Inflate.Proofs.ActualHeader
