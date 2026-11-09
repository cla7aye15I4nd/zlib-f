import ZlibF.Proof.«inftrees.c.code-length-contents»
import ZlibF.Proof.«inflate.c.main.table5»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
open Zlib.Inftrees (inflate_table)
set_option autoImplicit false

/-- The literal LENLENS prefix through the constructor's result stores. -/
def llInstall (c : Ctx) : X Int32 := do
  wrS c.st fun s => { s with next := codesP c.st, distcode := codesP c.st, lencode := codesP c.st, lenbits := 7 }
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table CODES (lensP c.st) 19 s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  return r

private theorem install_bind_assoc {α β γ : Type} (x : X α) (f : α → X β) (g : β → X γ) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  apply ExceptT.ext
  apply StateT.ext
  intro l
  funext h
  change runX ((x >>= f) >>= g) l h = runX (x >>= fun a => f a >>= g) l h
  simp only [runX_bind]
  cases run : runX x l h with
  | error fault => simp only [run]
  | ok pair =>
    obtain ⟨⟨value, regs⟩, after⟩ := pair
    cases value <;> simp only [run, runX_bind]

private theorem install_pure_bind {α β : Type} (value : α) (next : α → X β) :
    ((pure value : X α) >>= next) = next value := rfl

/-- The source cut retains both the failure and success continuations. -/
theorem llTail_install_eq (c : Ctx) : llTail c = (do
    let ret ← llInstall c
    if ret != 0 then
      badMode c "invalid code lengths set"
      return
    wrS c.st fun s => { s with «have» := 0, mode := CODELENS }
    inflate_CODELENS c) := by
  simp only [llTail, llInstall, install_bind_assoc, install_pure_bind]

/-- The actual constructor prefix installs the full empty/nonempty content
classification, not just the meaning of ordinary accepted queries. Every
constructor result is retained; success is a conclusion branch. -/
theorem llInstall_code_length_contents {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (lengths : Good3 s.lens 19) :
    ∃ (ret : Int32) (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∀ index, 19 ≤ index → work[index]? = s.work[index]?) ∧
      (∀ index, 128 ≤ index → codes[index]? = s.codes[index]?) ∧
      runX (llInstall c) l h = .ok ((.ok ret, { l with ret := ret }),
        setI h zs { llPre zs s with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 → Zlib.Inftrees.Proofs.CodeLengthContents codes 0 root.toNat
        (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) 19)) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (llPre zs s)).istates zs = some (llPre zs s) := by simp
  have lens : Space.get (setI h zs (llPre zs s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [llPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (llPre zs s)) (WRef.istate_work zs) = some s.work := by
    simpa [llPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (llPre zs s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [llPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (llPre zs s)) CODES
      (.istate_lens zs) 0 19 (.istate_codes zs) 0 7 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inl rfl, lens, work, codes, by simp, by simp,
      by simp; omega, by simp; omega,
      by simp [Zlib.Inftrees.Spec.capOf, CODES]; omega,
      (by intro k inside; have := lengths.all k (by simpa using inside); simpa using (by omega : (s.lens.getD k 0).toNat ≤ 15)),
      (by intro _; exact ⟨by decide, fun k inside => by simpa using lengths.all k (by simpa using inside), by decide⟩),
      (by intro impossible; cases impossible), (by intro impossible; cases impossible)⟩
  obtain ⟨result, after, run, frame, contents⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_establishes_code_length_contents pre
  obtain ⟨ret, next, root⟩ := result
  obtain ⟨work, codes, heap, workSize', codeSize', workFrame, codeFrame, _result⟩ := frame
  change work.size = s.work.size at workSize'
  change codes.size = s.codes.size at codeSize'
  have heapEq : after = setI h zs (llBadSt zs s work codes) := by
    rw [heap, put_work_codes stored]
    simp [setI_setI, llBadSt, llPre]
  refine ⟨ret, next, root, work, codes, by omega, by omega,
    fun index lower => workFrame index (Or.inr (by simpa using lower)),
    fun index lower => codeFrame index (Or.inr (by simpa [Zlib.Inftrees.Spec.capOf, CODES] using lower)), ?_, ?_⟩
  · unfold llInstall
    rw [hc]
    have call : inflate_table CODES (.ref (WRef.istate_lens zs) 0) 19
        (.ref (CodeRef.istate_codes zs) 0) 7 (.ref (WRef.istate_work zs) 0)
        (setI h zs (llPre zs s)) = .ok ((ret, next, root), after) := run
    simp [llPre] at call
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, lensP, workP, codesP,
      call, heapEq, runX_modify, runX_pure, llBadSt, llPre, setI_setI]
  · intro success
    obtain ⟨array, get, semantic⟩ := contents success
    have actual : Space.get after (CodeRef.istate_codes zs) = some codes := by
      rw [heapEq]
      simp [Space.get, setI, llBadSt, llPre]
    rw [actual] at get
    cases Option.some.inj get
    exact semantic

/-- The same successful real prefix enters CODELENS with its precise
installed contents. No table-contract hypothesis is supplied by a caller. -/
theorem llTail_code_length_contents_continuation {c : Ctx} {l : IL} {h : Heap}
    {zs : Nat} {s : InflateState} (hc : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (wf : s.WellFormed) (lengths : Good3 s.lens 19) :
    ∃ (ret : Int32) (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      runX (llInstall c) l h = .ok ((.ok ret, { l with ret := ret }),
        setI h zs { llPre zs s with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 →
        Zlib.Inftrees.Proofs.CodeLengthContents codes 0 root.toNat
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) 19) ∧
        runX (llTail c) l h = runX (inflate_CODELENS c) { l with ret := 0 }
          (setI h zs { llPre zs s with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS })) := by
  obtain ⟨ret, next, root, work, codes, _workSize, _codeSize, _workFrame, _codeFrame,
    run, contents⟩ := llInstall_code_length_contents hc hs wf lengths
  refine ⟨ret, next, root, work, codes, run, ?_⟩
  intro success
  refine ⟨contents success, ?_⟩
  rw [llTail_install_eq, runX_bind, run, success]
  simp [hc, runX_bind, runX_lift, wrI_eq, setI_setI]

#print axioms llTail_code_length_contents_continuation
#print axioms llTail_install_eq
#print axioms llInstall_code_length_contents
end Zlib.Inflate.Proofs
