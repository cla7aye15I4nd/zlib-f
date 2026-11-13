import ZlibF.Proof.«infback.c.safety-table-read»
import ZlibF.Proof.«inftrees.c.read-extent»
import ZlibF.Proof.«inftrees.c.decode.prefix-safe»

/-!
# infback.c: `case TABLE` on the loop invariant, the literal/length and distance tables

After the decoded code lengths (`have = nlen + ndist`, each at most 15): `inflate_table(LENS)` on
`lens[0 .. nlen)` builds the literal/length table at `codes[0 ..]`, `inflate_table(DISTS)` on
`lens[nlen .. nlen + ndist)` the distance table right after it, and the second call keeps the
first table (`inflate_table_dists_preserves_lens`). Either call may refuse the lengths (`BAD`).
On success the mode is `LEN` with both tables installed (`TablesOk`), ready for `back_LEN`.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
open Zlib.Inftrees (inflate_table)
set_option autoImplicit false

/-- The state before the literal/length table call. -/
def lnPre (i : Nat) (s : InflateState) : InflateState :=
  { s with next := .ref (.istate_codes i) 0, lencode := .ref (.istate_codes i) 0, lenbits := 9 }

/-- The state after the literal/length table call. -/
def lnSt (i : Nat) (s : InflateState) (nx : CodePtr) (lb : UInt32) (wa : Array UInt16) (ca : Array Code) :
    InflateState :=
  { lnPre i s with next := nx, lenbits := lb, work := wa, codes := ca }

/-- The state before the distance table call. -/
def dsPre (s : InflateState) : InflateState := { s with distcode := s.next, distbits := 6 }

/-- The state after the distance table call. -/
def dsSt (s : InflateState) (nx : CodePtr) (db : UInt32) (wa : Array UInt16) (ca : Array Code) : InflateState :=
  { dsPre s with next := nx, distbits := db, work := wa, codes := ca }

set_option maxRecDepth 100000 in
/-- **The distance table call and the switch to `LEN`, on the invariant.** -/
theorem tabLensTail1_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (mode : s.mode = TABLE) (wf : s.WellFormed)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    {used : Nat} (next : s.next = .ref (.istate_codes i) used) (room : used ≤ 852)
    (lenc : s.lencode = .ref (.istate_codes i) 0)
    (lensSafe : Zlib.Inffast.Spec.LenTableSafe s.codes 0 s.lenbits.toNat)
    (lensExtent : Zlib.Inftrees.Spec.TableReadExtent LENS s.codes 0 s.lenbits.toNat used)
    {B : Nat} (lt : baseM pr l log < B) :
    (∃ res l' h', runX (tabLensTail1 c 0) l h = .ok ((res, l'), h') ∧ TRound c pr h0 B res l' h') ∨
    (∃ h1 s1, runX (tabLensTail1 c 0) l h = runX (back_LEN c) { l with ret := 0 } h1 ∧
      PInv c pr h0 h1 { l with ret := 0 } log ∧ h1.istates i = some s1 ∧ s1.mode = LEN ∧ TablesOk i s1) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h i (dsPre s)).istates i = some (dsPre s) := by simp [setI]
  have lens : Space.get (setI h i (dsPre s)) (WRef.istate_lens i) = some s.lens := by
    simpa [dsPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h i (dsPre s)) (WRef.istate_work i) = some s.work := by
    simpa [dsPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h i (dsPre s)) (CodeRef.istate_codes i) = some s.codes := by
    simpa [dsPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h i (dsPre s)) DISTS
      (.istate_lens i) s.nlen.toNat s.ndist (.istate_codes i) used 6 (.istate_work i) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inr rfl), lens, work, codes, by simp, by simp,
      by omega, by omega, by simp [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES]; omega,
      lengths, (by intro impossible; cases impossible),
      (by intro impossible; cases impossible), fun _ => by omega⟩
  obtain ⟨result, after, run, frame, tables⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  obtain ⟨preservedResult, preservedAfter, array, preservedRun, _, getArray, safeLens, _, _, _⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_dists_preserves_lens pre (by omega) lensSafe lensExtent
  rw [run] at preservedRun
  cases preservedRun
  obtain ⟨ret, nx, db⟩ := result
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, _⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes i) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, dsPre]
  rw [actualGet] at getArray
  have sameArray : ca = array := Option.some.inj getArray
  subst array
  let sE := dsSt s nx db wa ca
  have hsE : (setI h i sE).istates i = some sE := by simp [setI]
  have wfE : sE.WellFormed := ⟨lensSize, by rw [← workSize]; exact waSize, by rw [← codeSize]; exact caSize⟩
  have IE : PInv c pr h0 (setI h i sE) { l with ret := ret } log :=
    (I.setState hs sE rfl rfl rfl wfE (modeOk_of (Or.inr (Or.inl mode)))).withRet ret
  have runE : runX (tabLensTail1 c 0) l h = runX (tabLensTail2 c ret) { l with ret := ret } (setI h i sE) := by
    unfold tabLensTail1
    rw [I.cst]
    have actual := run
    change inflate_table DISTS _ _ _ _ _ _ = _ at actual
    rw [heap, put_work_codes stored] at actual
    have add := Ptr.add_nat_ok (off := 0) (n := s.nlen.toNat) lens (by omega : 0 + s.nlen.toNat ≤ s.lens.size)
    unfold OkOn at add
    simp only [Nat.zero_add, dsPre, next, setI_setI] at add actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, dsPre, lensP, workP, codesP,
      next, add, actual, runX_modify, setI_setI, sE, dsSt]
  by_cases r0 : ret = 0
  · subst r0
    right
    obtain ⟨table, used2, get, _, _, _, _, _, safe⟩ := tables rfl
    rw [actualGet] at get
    cases get
    let sF := { sE with mode := LEN }
    have tablesOk : TablesOk i sF :=
      ⟨Or.inl ⟨0, lenc, safeLens⟩, Or.inl ⟨used, next, safe rfl⟩⟩
    have IF := IE.setState hsE sF rfl rfl rfl wfE ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), fun _ => tablesOk⟩
    rw [setI_setI] at IF
    refine ⟨setI h i sF, sF, ?_, IF, by simp [setI], rfl, tablesOk⟩
    rw [runE]
    unfold tabLensTail2
    rw [I.cst]
    simp [runX_bind, runX_lift, setMode, wrI_eq, hsE, setI_setI]
    rfl
  · left
    obtain ⟨hb, runB, T⟩ := TRound.bad IE "invalid distances set" lit_distances (B := B) (by exact lt)
    refine ⟨.ok (), { l with ret := ret }, hb, ?_, T⟩
    rw [runE]
    unfold tabLensTail2
    have r0' : (ret != 0) = true := by simpa using r0
    simp only [r0', ↓reduceIte, runX_bind, runX_lift_ok runB]
    rfl

set_option maxRecDepth 100000 in
/-- **The literal/length and distance tables and the switch to `LEN`, on the invariant.** -/
theorem tabLens_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (st : TabSt s)
    (full : s.«have».toNat = s.nlen.toNat + s.ndist.toNat) (rl : RL s) {B : Nat} (lt : baseM pr l log < B) :
    (∃ res l' h', runX (tabLens c) l h = .ok ((res, l'), h') ∧ TRound c pr h0 B res l' h') ∨
    (∃ h1 s1, runX (tabLens c) l h = runX (back_LEN c) { l with ret := 0 } h1 ∧
      PInv c pr h0 h1 { l with ret := 0 } log ∧ h1.istates i = some s1 ∧ s1.mode = LEN ∧ TablesOk i s1) := by
  obtain ⟨z0, s0, valid0, -, -⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid0.2.1.symm.trans hs)
  subst e0
  have wf := valid0.2.2.2.2.2.1
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have nl := st.nlen
  have nd := st.ndist
  have lengths : ∀ k, k < s0.nlen.toNat → (s0.lens.getD k 0).toNat ≤ 15 := fun k hk => rl k (by omega)
  have stored : (setI h i (lnPre i s0)).istates i = some (lnPre i s0) := by simp [setI]
  have lens : Space.get (setI h i (lnPre i s0)) (WRef.istate_lens i) = some s0.lens := by
    simpa [lnPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h i (lnPre i s0)) (WRef.istate_work i) = some s0.work := by
    simpa [lnPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h i (lnPre i s0)) (CodeRef.istate_codes i) = some s0.codes := by
    simpa [lnPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h i (lnPre i s0)) LENS
      (.istate_lens i) 0 s0.nlen (.istate_codes i) 0 9 (.istate_work i) 0 :=
    ⟨s0.lens, s0.work, s0.codes, Or.inr (Or.inl rfl), lens, work, codes, by simp, by simp,
      by omega, by omega, by simp [Zlib.Inftrees.Spec.capOf, LENS, CODES]; omega,
      by simpa using lengths, (by intro impossible; cases impossible),
      fun _ => by omega, (by intro impossible; cases impossible)⟩
  obtain ⟨result, after, run, frame, tables⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  obtain ⟨ret, nx, lb⟩ := result
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, _⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes i) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, lnPre]
  let sQ := lnSt i s0 nx lb wa ca
  have hsQ : (setI h i sQ).istates i = some sQ := by simp [setI]
  have wfQ : sQ.WellFormed := ⟨lensSize, by rw [← workSize]; exact waSize, by rw [← codeSize]; exact caSize⟩
  have IQ : PInv c pr h0 (setI h i sQ) { l with ret := ret } log :=
    (I.setState hs sQ rfl rfl rfl wfQ (modeOk_of (Or.inr (Or.inl st.mode)))).withRet ret
  have runQ : runX (tabLens c) l h = runX (tabLensTail1 c ret) { l with ret := ret } (setI h i sQ) := by
    unfold tabLens
    rw [I.cst]
    have actual := run
    change inflate_table LENS _ _ _ _ _ _ = _ at actual
    simp only [lnPre] at actual
    rw [heap, put_work_codes stored] at actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, lnPre, lensP, workP, codesP,
      actual, runX_modify, setI_setI, sQ, lnSt]
  by_cases r0 : ret = 0
  · subst r0
    obtain ⟨array, used, get, pointer, bound, extent, _, safe, _⟩ := tables rfl
    rw [actualGet] at get
    cases get
    have used852 : used ≤ 852 := by simpa [Zlib.Inftrees.Spec.capOf, LENS, CODES] using bound
    have nextQ : sQ.next = .ref (.istate_codes i) used := by
      show nx = _; simpa using pointer
    rcases tabLensTail1_p c pr IQ hsQ st.mode wfQ nl nd (fun k hk => rl (s0.nlen.toNat + k) (by have e : sQ.ndist = s0.ndist := rfl; rw [e] at hk; omega))
        nextQ used852 rfl (safe rfl) extent (B := B) (by exact lt) with
      ⟨res, l', h', run', T⟩ | ⟨h1, s1, run1, I1, hs1, mode1, tab1⟩
    · left
      exact ⟨res, l', h', by rw [runQ]; exact run', T⟩
    · right
      exact ⟨h1, s1, by rw [runQ, run1], I1, hs1, mode1, tab1⟩
  · left
    obtain ⟨hb, runB, T⟩ := TRound.bad IQ "invalid literal/lengths set" lit_literal_lengths (B := B) (by exact lt)
    refine ⟨.ok (), { l with ret := ret }, hb, ?_, T⟩
    rw [runQ]
    unfold tabLensTail1
    have r0' : (ret != 0) = true := by simpa using r0
    simp only [r0', ↓reduceIte, runX_bind, runX_lift_ok runB]
    rfl

end Zlib.Infback.Safety
