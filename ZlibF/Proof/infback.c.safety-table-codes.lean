import ZlibF.Proof.«infback.c.safety-table-cl»
import ZlibF.Proof.«inftrees.c.content.codes»
import ZlibF.Proof.«inflate.c.main.table5»

/-!
# infback.c: `case TABLE` on the loop invariant, the code-length table

`inflate_table(CODES, lens, 19, &next, &lenbits, work)` on the state's own arrays, with the 19
code-length code lengths at most 7 (`inflate_table_codes_decoder_safe`). The call writes only
`work` and `codes`. On failure the round ends with `BAD`; on success the decoding loop starts
with `have = 0` and a code-length table that `lookup1_p` can read (`RdTab`).
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
open Zlib.Inftrees (inflate_table)
set_option autoImplicit false

/-- The code-length table of the decoding loop: the state's own `codes` from 0. -/
def RdTab (i : Nat) (s : InflateState) : Prop :=
  s.lencode = .ref (.istate_codes i) 0 ∧ Zlib.Inftrees.Spec.CodeLengthTableSafe s.codes 0 s.lenbits.toNat

/-- The state after the code-length table call. -/
def cdSt (i : Nat) (s : InflateState) (wa : Array UInt16) (ca : Array Code) (nx : CodePtr) (lb : UInt32) :
    InflateState :=
  { s with next := nx, lencode := .ref (.istate_codes i) 0, lenbits := lb, work := wa, codes := ca }

/-- **The code-length table call of `case TABLE` on the invariant.** -/
theorem tabB_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (st : TabSt s)
    (lens7 : ∀ k, k < 19 → (s.lens.getD k 0).toNat ≤ 7) {B : Nat} (lt : baseM pr l log < B) :
    (∃ res l' h', runX (tabB c) l h = .ok ((res, l'), h') ∧ TRound c pr h0 B res l' h') ∨
    (∃ h1 s1, runX (tabB c) l h = runX (do tabRead c; tabC c) { l with ret := 0 } h1 ∧
      PInv c pr h0 h1 { l with ret := 0 } log ∧ h1.istates i = some s1 ∧ TabSt s1 ∧ s1.«have» = 0 ∧
      RdTab i s1 ∧ s1.lens = s.lens) := by
  obtain ⟨z, s0, valid, -, -⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  subst e0
  obtain ⟨hl, hw, hcs⟩ := valid.2.2.2.2.2.1
  let sP : InflateState := { s0 with next := .ref (.istate_codes i) 0, lencode := .ref (.istate_codes i) 0, lenbits := 7 }
  have hsP : (setI h i sP).istates i = some sP := by simp [setI]
  have hgl : Space.get (setI h i sP) (WRef.istate_lens i) = some s0.lens := by
    simpa [sP] using WRef.get_istate_lens hsP
  have hgw : Space.get (setI h i sP) (WRef.istate_work i) = some s0.work := by
    simpa [sP] using WRef.get_istate_work hsP
  have hgc : Space.get (setI h i sP) (CodeRef.istate_codes i) = some s0.codes := by
    simpa [sP] using CodeRef.get_istate_codes hsP
  have hf15 : ∀ k, k < (19 : UInt32).toNat → (s0.lens.getD (0 + k) 0).toNat ≤ 15 := by
    intro k hk
    have := lens7 k (by simpa using hk)
    simpa using (by omega : (s0.lens.getD k 0).toNat ≤ 15)
  have hcodes : CODES = CODES → (19 : UInt32).toNat ≤ 19 ∧
      (∀ k, k < (19 : UInt32).toNat → (s0.lens.getD (0 + k) 0).toNat ≤ 7) ∧ 7 ≤ (7 : UInt32).toNat := by
    intro _
    refine ⟨by decide, fun k hk => ?_, by decide⟩
    simpa using lens7 k (by simpa using hk)
  have hcap : 0 + Zlib.Inftrees.Spec.capOf CODES ≤ s0.codes.size := by
    simp [Zlib.Inftrees.Spec.capOf, CODES]; omega
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h i sP) CODES
      (.istate_lens i) 0 19 (.istate_codes i) 0 7 (.istate_work i) 0 :=
    ⟨s0.lens, s0.work, s0.codes, Or.inl rfl, hgl, hgw, hgc, by simp, by simp, by simp; omega, by simp; omega,
      hcap, hf15, hcodes, fun e => absurd e (by decide), fun e => absurd e (by decide)⟩
  obtain ⟨rr, h3, hrun, hres, decoded⟩ := Zlib.Inftrees.Proofs.inflate_table_codes_decoder_safe pre
  obtain ⟨ret, nx, lb⟩ := rr
  obtain ⟨wa', ca', hh3, hwa, hca, -, -, -⟩ := hres
  have hh3' : h3 = setI h i { sP with work := wa', codes := ca' } := by
    rw [hh3, put_work_codes hsP, setI_setI]
  have hrun2 : inflate_table CODES (.ref (WRef.istate_lens i) 0) 19 (.ref (CodeRef.istate_codes i) 0) 7
      (.ref (WRef.istate_work i) 0) (setI h i sP) = .ok ((ret, nx, lb), setI h i { sP with work := wa', codes := ca' }) := by
    rw [← hh3']; exact hrun
  let sQ := cdSt i s0 wa' ca' nx lb
  have hsQ : (setI h i sQ).istates i = some sQ := by simp [setI]
  have wfQ : sQ.WellFormed := ⟨hl, by rw [← hw]; exact hwa, by rw [← hcs]; exact hca⟩
  have IQ : PInv c pr h0 (setI h i sQ) { l with ret := ret } log :=
    (I.setState hs sQ rfl rfl rfl wfQ (modeOk_of (Or.inr (Or.inl st.mode)))).withRet ret
  have runQ : runX (tabB c) l h = runX (tabBTail c ret) { l with ret := ret } (setI h i sQ) := by
    unfold tabB
    rw [I.cst]
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, lensP, workP, codesP, runX_modify, hrun2, sP]
    rfl
  by_cases r0 : ret = 0
  · subst r0
    right
    let sR := { sQ with «have» := 0 }
    have hsR : (setI h i sR).istates i = some sR := by simp [setI]
    have IR := IQ.setState hsQ sR rfl rfl rfl ⟨wfQ.1, wfQ.2.1, wfQ.2.2⟩ (modeOk_of (Or.inr (Or.inl st.mode)))
    rw [setI_setI] at IR
    obtain ⟨ca, get, safe⟩ := decoded rfl
    have getQ : Space.get (setI h i { sP with work := wa', codes := ca' }) (CodeRef.istate_codes i) = some ca' := by
      simp [Space.get, setI]
    rw [hh3', getQ] at get
    cases get
    refine ⟨setI h i sR, sR, ?_, IR, hsR, ⟨st.mode, st.nlen, st.ndist, st.ncode⟩, rfl, ⟨rfl, safe⟩, rfl⟩
    rw [runQ]
    unfold tabBTail
    rw [I.cst]
    simp [runX_bind, runX_lift, wrI_eq, hsQ, setI_setI]
    rfl
  · left
    obtain ⟨hb, runB, T⟩ := TRound.bad IQ "invalid code lengths set" lit_code_lengths (B := B) (by exact lt)
    refine ⟨.ok (), { l with ret := ret }, hb, ?_, T⟩
    rw [runQ]
    unfold tabBTail
    have r0' : (ret != 0) = true := by simpa using r0
    simp only [r0', ↓reduceIte, runX_bind, runX_lift_ok runB]
    rfl

end Zlib.Infback.Safety
