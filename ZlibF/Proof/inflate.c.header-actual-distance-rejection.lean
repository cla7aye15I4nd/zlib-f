import ZlibF.Proof.«inflate.c.header-actual-table-rejection»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inftrees
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The actual DISTS failure after a real successful LENS prefix. Source
pointer/count facts come from that prefix, never from an installed oracle. -/
theorem invalid_distance_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL} {offset : Nat}
    (E : Env c h r zs z s) (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    (next : s.next = .ref (.istate_codes zs) offset) (room : offset ≤ 852)
    (invalid : ¬ Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    ∃ resultNext root work codes i,
      PayloadStable.CallTrace (setI h zs (clDistPre s)) DISTS (.istate_lens zs) s.nlen.toNat s.ndist (.istate_codes zs) offset 6
        (.istate_work zs) 0 (-1, resultNext, root) codes ∧
      runX (clAfterLens c 0) l h = .ok ((.ok (), {l with ret := -1}),
        tcBadHeap (setI h zs (clDistResult s resultNext root work codes)) r zs z (clDistResult s resultNext root work codes) i) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (clDistPre s)).istates zs = some (clDistPre s) := setI_istates_same ..
  have lens : Space.get (setI h zs (clDistPre s)) (WRef.istate_lens zs) = some s.lens := by simpa [clDistPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (clDistPre s)) (WRef.istate_work zs) = some s.work := by simpa [clDistPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (clDistPre s)) (CodeRef.istate_codes zs) = some s.codes := by simpa [clDistPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (clDistPre s)) DISTS (.istate_lens zs) s.nlen.toNat s.ndist (.istate_codes zs) offset 6 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inr rfl), lens, work, codes, by simp, by simp, by omega, by omega,
      by simp [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES]; omega,
      lengths, (by intro impossible; cases impossible), (by intro impossible; cases impossible), fun _ => by omega⟩
  have invalid0 : ¬ Acceptable (Zlib.Inftrees.Spec.kindOf DISTS) (Zlib.Inftrees.Spec.lensList pre.la s.nlen.toNat s.ndist.toNat) := by
    simpa [Zlib.Inftrees.Spec.kindOf, Zlib.Inftrees.Spec.lensList, Zlib.Inftrees.Proofs.lensOf, pre, CODES, DISTS, LENS] using invalid
  obtain ⟨resultNext, root, after, run, frame⟩ := invalid_constructor_actual pre invalid0
  have retainedFrame := frame
  obtain ⟨wa, ca, heap, _waSize, _caSize, _workFrame, _codeFrame, _result⟩ := frame
  have get : Space.get after (CodeRef.istate_codes zs) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, clDistPre]
  have actual : runX (clAfterLens c 0) l h = runX (clAfterDist c (-1)) {l with ret := -1}
      (setI h zs (clDistResult s resultNext root wa ca)) := by
    unfold clAfterLens clAfterDist
    rw [E.st]
    have call := run
    change inflate_table DISTS _ _ _ _ _ _ = _ at call
    rw [heap, put_work_codes stored] at call
    have add := Ptr.add_nat_ok (off := 0) (n := s.nlen.toNat) lens (by omega : 0 + s.nlen.toNat ≤ s.lens.size)
    unfold OkOn at add
    simp only [Nat.zero_add, clDistPre, next, setI_setI] at add call
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, E.hs, clDistPre, lensP, workP,
      next, add, call, runX_modify, setI_setI, clDistResult]
  have stateGet : (setI h zs (clDistResult s resultNext root wa ca)).istates zs = some (clDistResult s resultNext root wa ca) := setI_istates_same ..
  have streamGet : r.get (setI h zs (clDistResult s resultNext root wa ca)) = some z := by rw [ZStreamRef.get_setI]; exact E.hz
  obtain ⟨i, _literal, bad⟩ := clAfterDist_error (l := {l with ret := -1}) E.strm E.st streamGet stateGet (by decide : (-1 : Int32) ≠ 0)
  exact ⟨resultNext, root, wa, ca, i, ⟨pre, after, run, retainedFrame, get⟩, actual.trans bad⟩

#print axioms invalid_distance_source
end Zlib.Inflate.Proofs.ActualHeader
