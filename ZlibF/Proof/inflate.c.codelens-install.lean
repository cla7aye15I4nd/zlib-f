import ZlibF.Proof.«inflate.c.main.table5»
import ZlibF.Proof.«inftrees.c.content.codes»

/-!
# inflate.c: install the constructed code-length table at CODELENS

This strengthens the existing execution result with the table property
produced by the actual constructor. It retains all original outcomes and
frames, including malformed code-length alphabets.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inftrees
set_option autoImplicit false

/-- `case LENLENS:` after its length-reading loops.
The real CODES constructor establishes the lookup predicate on the exact
array installed before the actual CODELENS continuation. No constructor
contract or table property is supplied by the caller. -/
theorem llTail_run_table_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (hwf : s.WellFormed) (hG : Good3 s.lens 19) :
    ∃ (ret : Int32) (wa' : Array UInt16) (ca' : Array Code), wa'.size = 288 ∧ ca'.size = 1444 ∧
      (∀ x, 19 ≤ x → wa'[x]? = s.work[x]?) ∧ (∀ x, 128 ≤ x → ca'[x]? = s.codes[x]?) ∧
      (ret = 0 ∨ ret = -1) ∧
      (ret = -1 ↔ ¬ ZlibF.Spec.Acceptable .codeLength (Zlib.Inftrees.Spec.lensList s.lens 0 19)) ∧
      (ret = 0 → ∃ u lb, u ≤ 128 ∧ Zlib.Inftrees.Spec.CodeLengthTableSafe ca' 0 lb.toNat ∧ runX (llTail c) l h = runX (inflate_CODELENS c) { l with ret := 0 }
        (setI h zs (llOkSt zs s u lb wa' ca'))) ∧
      (ret = -1 → ∃ i, strTable[i]? = some "invalid code lengths set" ∧
        runX (llTail c) l h = .ok ((.ok (), { l with ret := -1 }),
          tcBadHeap (setI h zs (llBadSt zs s wa' ca')) r zs z (llBadSt zs s wa' ca') i)) := by
  obtain ⟨hl, hw, hcs⟩ := hwf
  have hs2 : (setI h zs (llPre zs s)).istates zs = some (llPre zs s) := by simp
  have hgl : Space.get (setI h zs (llPre zs s)) (WRef.istate_lens zs) = some s.lens := by simpa [llPre] using WRef.get_istate_lens hs2
  have hgw : Space.get (setI h zs (llPre zs s)) (WRef.istate_work zs) = some s.work := by simpa [llPre] using WRef.get_istate_work hs2
  have hgc : Space.get (setI h zs (llPre zs s)) (CodeRef.istate_codes zs) = some s.codes := by simpa [llPre] using CodeRef.get_istate_codes hs2
  have hf7 := hG.all
  have hf15 : ∀ k, k < (19 : UInt32).toNat → (s.lens.getD (0 + k) 0).toNat ≤ 15 := by
    intro k hk
    have := hf7 k (by simpa using hk)
    simpa using (by omega : (s.lens.getD k 0).toNat ≤ 15)
  have hcodes : CODES = CODES → (19 : UInt32).toNat ≤ 19 ∧ (∀ k, k < (19 : UInt32).toNat → (s.lens.getD (0 + k) 0).toNat ≤ 7) ∧
      7 ≤ (7 : UInt32).toNat := by
    intro _
    refine ⟨by decide, fun k hk => ?_, by decide⟩
    simpa using hf7 k (by simpa using hk)
  have hcap : 0 + Zlib.Inftrees.Spec.capOf CODES ≤ s.codes.size := by
    simp [Zlib.Inftrees.Spec.capOf, CODES]; omega
  have hne : WRef.istate_work zs ≠ WRef.istate_lens zs := by simp
  have hl19 : 0 + (19 : UInt32).toNat ≤ s.lens.size := by simp; omega
  have hw19 : 0 + (19 : UInt32).toNat ≤ s.work.size := by simp; omega
  have hty : CODES = CODES ∨ CODES = LENS ∨ CODES = DISTS := Or.inl rfl
  have hlens : CODES = LENS → (19 : UInt32).toNat ≤ 288 := fun e => absurd e (by decide)
  have hdists : CODES = DISTS → (19 : UInt32).toNat ≤ 32 := fun e => absurd e (by decide)
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (llPre zs s)) CODES
      (.istate_lens zs) 0 19 (.istate_codes zs) 0 7 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, hty, hgl, hgw, hgc, by simp, hne, hl19, hw19,
      hcap, hf15, hcodes, hlens, hdists⟩
  obtain ⟨rr, h3, hrun, hres, decoded⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_codes_decoder_safe pre
  obtain ⟨rr', h3', hrun', hacc1, hacc0, hacc2⟩ := Zlib.Inftrees.Proofs.inflate_table_correct_ret (setI h zs (llPre zs s)) CODES
    (WRef.istate_lens zs) 0 19 (CodeRef.istate_codes zs) 0 7 (WRef.istate_work zs) 0 s.lens s.work s.codes hty hgl hgw hgc
    (by simp) hne hl19 hw19 hcap hf15 hcodes hlens hdists
  rw [hrun] at hrun'
  cases hrun'
  obtain ⟨ret, nx, lb⟩ := rr
  obtain ⟨wa', ca', hh3, hwa, hca, hfw, hfc, hout⟩ := hres
  have hh3' : h3 = setI h zs (llBadSt zs s wa' ca') := by
    rw [hh3, put_work_codes hs2]
    simp [setI_setI, llBadSt, llPre]
  have codeSafe : ret = 0 → Zlib.Inftrees.Spec.CodeLengthTableSafe ca' 0 lb.toNat := by
    intro ok
    obtain ⟨table, get, safe⟩ := decoded ok
    have actualGet : Space.get h3 (CodeRef.istate_codes zs) = some ca' := by
      rw [hh3']
      simp [Space.get, setI, llBadSt]
    rw [actualGet] at get
    cases get
    exact safe
  have hk : Zlib.Inftrees.Spec.kindOf CODES = ZlibF.Spec.CodeKind.codeLength := by simp [Zlib.Inftrees.Spec.kindOf]
  rw [hk] at hacc1 hacc0 hacc2
  have hrun2 : inflate_table CODES (.ref (WRef.istate_lens zs) 0) 19 (.ref (CodeRef.istate_codes zs) 0) 7
      (.ref (WRef.istate_work zs) 0) (setI h zs (llPre zs s)) = .ok ((ret, nx, lb), h3) := hrun
  have hret : ret = 0 ∨ ret = -1 := by
    rcases hout with ⟨h0, _⟩ | ⟨h1 | h1, _⟩
    · exact Or.inl h0
    · exact absurd rfl (hacc2 h1).2
    · exact Or.inr h1
  refine ⟨ret, wa', ca', by rw [hwa]; exact hw, by rw [hca]; exact hcs, fun x hx => hfw x (Or.inr (by simpa using hx)),
    fun x hx => hfc x (Or.inr (by simpa [Zlib.Inftrees.Spec.capOf, CODES] using hx)), hret, hacc1, ?_, ?_⟩
  · intro h0
    rcases hout with ⟨_, u, hu, hnx⟩ | ⟨h1 | h1, _⟩
    · refine ⟨u, lb, by simpa [Zlib.Inftrees.Spec.capOf, CODES] using hu, codeSafe h0, ?_⟩
      unfold llTail
      rw [hc]
      have hrun3 := hrun2
      simp [llPre] at hrun3
      simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, lensP, workP, codesP, hrun3, hh3', h0, runX_modify, setMode]
      subst hnx
      simp [llBadSt, llOkSt, llPre]
    · rw [h0] at h1; cases h1
    · rw [h0] at h1; cases h1
  · intro hm
    rcases hout with ⟨h0, _⟩ | ⟨_, hnx, hlb⟩
    · rw [hm] at h0; cases h0
    · have hs3 : (setI h zs (llBadSt zs s wa' ca')).istates zs = some (llBadSt zs s wa' ca') := by simp
      have hz3 : r.get (setI h zs (llBadSt zs s wa' ca')) = some z := by simpa using hz
      obtain ⟨i, hi, hbm⟩ := tcBadMode_run (c := c) "invalid code lengths set" lit_code_lengths hr hc hz3 hs3
      refine ⟨i, hi, ?_⟩
      have hbm2 := hbm
      simp [llBadSt, llPre, tcBadHeap] at hbm2
      have hrun3 := hrun2
      simp [llPre] at hrun3
      unfold llTail
      rw [hc]
      subst hnx hlb
      have hnx' : (llBadSt zs s wa' ca').next = .ref (.istate_codes zs) 0 := by simp [llBadSt, llPre]
      have hlb' : (llBadSt zs s wa' ca').lenbits = 7 := by simp [llBadSt, llPre]
      have hetaB : ({ llBadSt zs s wa' ca' with next := .ref (.istate_codes zs) 0, lenbits := 7 } : InflateState) =
          llBadSt zs s wa' ca' := eta_next_lenbits _ _ _ hnx' hlb'
      simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, lensP, workP, codesP, hrun3, hh3', hm, runX_modify, runX_pure, hetaB]
      rw [hbm]

end Zlib.Inflate.Proofs
