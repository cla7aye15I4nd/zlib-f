import ZlibF.Proof.«inflate.c.header-actual-table-classifier»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inftrees
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Constructor rejection follows from the actual input alphabet. The
returned Result is the real translated call's complete storage frame. -/
theorem invalid_constructor_actual
    {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {count : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat}
    (pre : Zlib.Inftrees.Proofs.CallPre h type rl ol count rc oc bits rw ow)
    (invalid : ¬ Acceptable (Zlib.Inftrees.Spec.kindOf type) (Zlib.Inftrees.Spec.lensList pre.la ol count.toNat)) :
    ∃ next root after,
      C.run (inflate_table type (.ref rl ol) count (.ref rc oc) bits (.ref rw ow)) h = .ok ((-1, next, root), after) ∧
      Zlib.Inftrees.Spec.Result h rw rc ow oc (Zlib.Inftrees.Spec.capOf type) count.toNat pre.wa pre.ca (.ref rc oc) bits (-1, next, root) after := by
  obtain ⟨result, after, run, frame, _tables⟩ := Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  obtain ⟨result0, after0, run0, rejected, _valid, _space⟩ := Zlib.Inftrees.Proofs.inflate_table_correct_ret
    h type rl ol count rc oc bits rw ow pre.la pre.wa pre.ca pre.hty pre.hgl pre.hgw pre.hgc pre.hro pre.hne pre.hla pre.hwa pre.hca pre.hf15 pre.hcodes pre.hlens pre.hdists
  rw [run] at run0
  cases run0
  have negative := rejected.mpr invalid
  obtain ⟨ret, next, root⟩ := result
  change ret = -1 at negative
  subst ret
  exact ⟨next, root, after, run, frame⟩

/-- A nonacceptable actual literal alphabet takes the true LENS failure
branch. No successful callee return or after-state is an input. -/
theorem invalid_lens_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    (E : Env c h r zs z s) (wf : s.WellFormed) (count : s.nlen.toNat ≤ 286)
    (lengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (invalid : ¬ Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)) :
    ∃ next root work codes i,
      PayloadStable.CallTrace (setI h zs (clLensPre zs s)) LENS (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9
        (.istate_work zs) 0 (-1, next, root) codes ∧
      runX (clTables c) l h = .ok ((.ok (), {l with ret := -1}),
        tcBadHeap (setI h zs (clLensResult zs s next root work codes)) r zs z (clLensResult zs s next root work codes) i) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (clLensPre zs s)).istates zs = some (clLensPre zs s) := setI_istates_same ..
  have lens : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_lens zs) = some s.lens := by simpa [clLensPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_work zs) = some s.work := by simpa [clLensPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (clLensPre zs s)) (CodeRef.istate_codes zs) = some s.codes := by simpa [clLensPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (clLensPre zs s)) LENS (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inl rfl), lens, work, codes, by simp, by simp, by omega, by omega,
      by simp [Zlib.Inftrees.Spec.capOf, LENS, CODES]; omega,
      by simpa using lengths, (by intro impossible; cases impossible), fun _ => by omega, (by intro impossible; cases impossible)⟩
  have invalid0 : ¬ Acceptable (Zlib.Inftrees.Spec.kindOf LENS) (Zlib.Inftrees.Spec.lensList pre.la 0 s.nlen.toNat) := by
    simpa [Zlib.Inftrees.Spec.kindOf, Zlib.Inftrees.Spec.lensList, Zlib.Inftrees.Proofs.lensOf, pre, CODES, LENS] using invalid
  obtain ⟨next, root, after, run, frame⟩ := invalid_constructor_actual pre invalid0
  have retainedFrame := frame
  obtain ⟨wa, ca, heap, _waSize, _caSize, _workFrame, _codeFrame, _result⟩ := frame
  have get : Space.get after (CodeRef.istate_codes zs) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, clLensPre]
  have actual : runX (clTables c) l h = runX (clAfterLens c (-1)) {l with ret := -1}
      (setI h zs (clLensResult zs s next root wa ca)) := by
    unfold clTables clAfterLens
    rw [E.st]
    have call := run
    change inflate_table LENS _ _ _ _ _ _ = _ at call
    simp only [clLensPre] at call
    rw [heap, put_work_codes stored] at call
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, E.hs, clLensPre, lensP, workP, codesP, call, runX_modify, setI_setI, clLensResult]
  have stateGet : (setI h zs (clLensResult zs s next root wa ca)).istates zs = some (clLensResult zs s next root wa ca) := setI_istates_same ..
  have streamGet : r.get (setI h zs (clLensResult zs s next root wa ca)) = some z := by rw [ZStreamRef.get_setI]; exact E.hz
  obtain ⟨i, _literal, bad⟩ := clAfterLens_error (l := {l with ret := -1}) E.strm E.st streamGet stateGet (by decide : (-1 : Int32) ≠ 0)
  exact ⟨next, root, wa, ca, i, ⟨pre, after, run, retainedFrame, get⟩, actual.trans bad⟩

#print axioms invalid_constructor_actual
#print axioms invalid_lens_source
end Zlib.Inflate.Proofs.ActualHeader
