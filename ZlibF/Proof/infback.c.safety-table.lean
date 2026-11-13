import ZlibF.Proof.«infback.c.safety-table-lens»

/-!
# infback.c: `case TABLE` on the loop invariant

`TABLE_pre_p` composes the pieces of `case TABLE`: the header (`tabHead_p`), the code-length
code lengths (`tabLoop1_p`, `tabLoop2_p`), the code-length table (`tabB_p`), the decoded lengths
(`tabRead_p`), the two checks of `tabC` and the two tables (`tabLens_p`). The round ends there
(`BAD`, or `Z_BUF_ERROR` from `in`) with a smaller measure, or the mode is `LEN` with the tables
installed and the input part of the measure not larger: the fall-through into `case LEN`.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- What `case TABLE` leaves when it does not fall through into `case LEN`. -/
def TabOut (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 : Heap) (B : Nat) (m : X Unit) (l : IL) (h : Heap) : Prop :=
  (∃ res l' h', runX m l h = .ok ((res, l'), h') ∧ TRound c pr h0 B res l' h') ∨
  (∃ l1 h1 log1 s1, runX m l h = runX (back_LEN c) l1 h1 ∧ PInv c pr h0 h1 l1 log1 ∧
    h1.istates i = some s1 ∧ s1.mode = LEN ∧ TablesOk i s1 ∧ baseM pr l1 log1 + 2 ≤ B)

/-- `TabOut` through a first step that ends in `TRound` or continues. -/
theorem TabOut.bind {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 : Heap} {B : Nat} {m : X Unit} {k : Unit → X Unit} {l : IL} {h : Heap}
    {res : Except Ex Unit} {l1 : IL} {h1 : Heap} (run : runX m l h = .ok ((res, l1), h1))
    (stop : ∀ e, res = .error e → TRound c pr h0 B res l1 h1)
    (go : res = .ok () → TabOut c pr h0 B (k ()) l1 h1) : TabOut c pr h0 B (m >>= k) l h := by
  cases res with
  | error e =>
    left
    exact ⟨.error e, l1, h1, by rw [runX_bind, run], stop e rfl⟩
  | ok u =>
    cases u
    rcases go rfl with ⟨res2, l2, h2, run2, T⟩ | ⟨l2, h2, log2, s2, run2, I2, hs2, m2, t2, b2⟩
    · left; exact ⟨res2, l2, h2, by rw [runX_bind, run]; exact run2, T⟩
    · right; exact ⟨l2, h2, log2, s2, by rw [runX_bind, run]; exact run2, I2, hs2, m2, t2, b2⟩

/-- **The checks of `tabC` and the tables, on the invariant.** -/
theorem tabC_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s)
    (st : s.mode = BAD ∨ (RdSt i s ∧ s.«have».toNat = s.nlen.toNat + s.ndist.toNat))
    {B : Nat} (lt : baseM pr l log + 2 ≤ B) : TabOut c pr h0 B (tabC c) l h := by
  have rdm : rdS (some (.tab i)) (·.mode) h = .ok (s.mode, h) := by
    have := rdS_ok I.cst hs (·.mode); rwa [I.cst] at this
  rcases st with bad | ⟨rd, full⟩
  · left
    refine ⟨.ok (), l, h, ?_, log, I, Or.inl ⟨rfl, ?_⟩⟩
    · unfold tabC
      simp only [I.cst, runX_bind, runX_lift_ok rdm, bad, beq_self_eq_true, ↓reduceIte]
      rfl
    · rw [backMeasure_of pr hs, bad, modeRank_BAD]; omega
  · have nb : (s.mode == BAD) = false := by rw [rd.tab.mode]; decide
    obtain ⟨z, s0, valid, -, -⟩ := I.valid
    have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
    subst e0
    have wf := valid.2.2.2.2.2.1
    have read : OkOn h (Ptr.index (Ptr.ref (WRef.istate_lens i) 0) (256 : Int))
        (s0.lens[0 + 256]'(by rw [wf.1]; omega)) :=
      Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens hs) (by rw [wf.1]; omega)
    by_cases z256 : (s0.lens[0 + 256]'(by rw [wf.1]; omega) == (0 : UInt16)) = true
    · left
      obtain ⟨hb, runB, T⟩ := TRound.bad I "invalid code -- missing end-of-block" lit_missing_eob (B := B) (by omega)
      refine ⟨.ok (), l, hb, ?_, T⟩
      unfold tabC
      simp only [I.cst, runX_bind, runX_lift_ok rdm, nb, Bool.false_eq_true, ↓reduceIte, lensP,
        runX_lift_ok read, z256, runX_lift_ok runB]
      rfl
    · have z' : (s0.lens[0 + 256]'(by rw [wf.1]; omega) == (0 : UInt16)) = false := by simpa using z256
      rcases tabLens_p c pr I hs rd.tab full rd.rl (B := B) (by omega) with
        ⟨res, l', h', run', T⟩ | ⟨h1, s1, run1, I1, hs1, mode1, tab1⟩
      · left
        refine ⟨res, l', h', ?_, T⟩
        unfold tabC
        simp only [I.cst, runX_bind, runX_lift_ok rdm, nb, Bool.false_eq_true, ↓reduceIte, lensP,
          runX_lift_ok read, z']
        exact run'
      · right
        refine ⟨{ l with ret := 0 }, h1, log, s1, ?_, I1, hs1, mode1, tab1, by
          show baseM pr l log + 2 ≤ B; omega⟩
        unfold tabC
        simp only [I.cst, runX_bind, runX_lift_ok rdm, nb, Bool.false_eq_true, ↓reduceIte, lensP,
          runX_lift_ok read, z']
        exact run1

/-- **`case TABLE` up to the fall-through into `case LEN`, on the invariant.** -/
theorem TABLE_pre_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (mode : s.mode = TABLE) :
    TabOut c pr h0 (baseM pr l log + 2) (back_TABLE c) l h := by
  rcases tabHead_p c pr I hs mode with ⟨res, l', h', run', T⟩ | ⟨l1, h1, log1, s1, run1, I1, hs1, st1, have1, b1⟩
  · left
    exact ⟨res, l', h', run', T⟩
  · have go : TabOut c pr h0 (baseM pr l log + 2) (tabA c) l1 h1 := by
      have hv : s1.«have».toNat ≤ s1.ncode.toNat := by rw [have1]; exact Nat.zero_le _
      have cl : CLInv s1 := by intro k _ ⟨j, hj, _⟩; rw [have1] at hj; exact absurd hj (by simp)
      obtain ⟨res2, l2, h2, log2, run2, I2, ok2, err2⟩ := tabLoop1_p c pr I1 hs1 st1 hv cl
      unfold tabA
      refine TabOut.bind run2 (fun e x => ?_) (fun x => ?_)
      · obtain ⟨rfl, ret⟩ := err2 e x
        subst x
        exact TRound.leave I2 _ ret
      · obtain ⟨b2, s2, hs2, st2, full2, cl2⟩ := ok2 x
        obtain ⟨h3, run3, I3, s3, hs3, st3, full3, cl3⟩ :=
          tabLoop2_p c pr I2 hs2 st2 (by have := st2.ncode; omega) cl2
        refine TabOut.bind run3 (fun e x => by cases x) (fun _ => ?_)
        rcases tabB_p c pr I3 hs3 st3 (cl3.all full3) (B := baseM pr l log + 2) (by omega) with
          ⟨res4, l4, h4, run4, T4⟩ | ⟨h4, s4, run4, I4, hs4, st4, have4, rd4, -⟩
        · left; exact ⟨res4, l4, h4, run4, T4⟩
        · have rd : RdSt i s4 :=
            ⟨st4, rd4, by rw [have4]; exact Nat.zero_le _, fun k hk => by rw [have4] at hk; exact absurd hk (by simp)⟩
          obtain ⟨res5, l5, h5, log5, run5, I5, ok5, err5⟩ := tabRead_p c pr I4 hs4 rd
          have pre : runX (tabB c) l2 h3 = runX (tabRead c >>= fun _ => tabC c) { l2 with ret := 0 } h4 := run4
          have tr : TabOut c pr h0 (baseM pr l log + 2) (tabRead c >>= fun _ => tabC c) { l2 with ret := 0 } h4 :=
            TabOut.bind run5
              (fun e x => by
                obtain ⟨rfl, ret⟩ := err5 e x
                subst x
                exact TRound.leave I5 _ ret)
              (fun x => by
                obtain ⟨b5, s5, hs5, st5⟩ := ok5 x
                have bb : baseM pr { l2 with ret := 0 } log2 = baseM pr l2 log2 := rfl
                exact tabC_p c pr I5 hs5 st5 (by omega))
          rcases tr with ⟨res6, l6, h6, run6, T6⟩ | ⟨l6, h6, log6, s6, run6, I6, hs6, m6, t6, b6⟩
          · left; exact ⟨res6, l6, h6, by rw [pre, run6], T6⟩
          · right; exact ⟨l6, h6, log6, s6, by rw [pre, run6], I6, hs6, m6, t6, b6⟩
    rcases go with ⟨res, l', h', run', T⟩ | ⟨l2, h2, log2, s2, run2, I2, hs2, m2, t2, b2⟩
    · left; exact ⟨res, l', h', by rw [run1, run'], T⟩
    · right; exact ⟨l2, h2, log2, s2, by rw [run1, run2], I2, hs2, m2, t2, b2⟩

end Zlib.Infback.Safety
