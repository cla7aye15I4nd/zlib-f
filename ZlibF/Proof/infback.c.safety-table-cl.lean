import ZlibF.Proof.«infback.c.safety-table-head»

/-!
# infback.c: `case TABLE` on the loop invariant, the code-length code lengths

The two loops that fill `lens[order[0 .. 18]]`: `ncode` lengths of 3 bits from the stream
(`NEEDBITS(3)` may call `in`), then zeros. Each store is inside `lens` (`order[k] < 19`). The
loops are measured by `ncode - have` and `19 - have`. Afterwards the 19 code-length code lengths
are at most 7 (`CLInv`, with `order` onto `0 .. 18`).
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- The code-length code lengths written so far are at most 7. -/
def CLInv (s : InflateState) : Prop :=
  ∀ k, k < 19 → (∃ j, j < s.«have».toNat ∧ orderNat j = k) → (s.lens.getD k 0).toNat ≤ 7

/-- `bound s - have` of the state record, the measure of a loop over `have`. -/
def tabGap (i : Nat) (bound : InflateState → Nat) (h : Heap) : Nat :=
  match h.istates i with
  | some s => bound s - s.«have».toNat
  | none => 0

theorem tabGap_of {i : Nat} {bound : InflateState → Nat} {h : Heap} {s : InflateState} (hs : h.istates i = some s) :
    tabGap i bound h = bound s - s.«have».toNat := by
  simp [tabGap, hs]

/-- One code-length code length after `NEEDBITS(3)`. -/
def tl1Rest (c : BCtx) : X Unit := do
  let s ← ldInflateState c.st
  wrS c.st fun s => { s with «have» := s.«have» + 1 }
  let o ← orderAt s.«have»
  let b ← BITS 3
  Ptr.store (← (lensP c.st).add (o.toNat : Int)) b.toUInt16
  DROPBITS 3

theorem tl1Body_eq (c : BCtx) : tl1Body c = (do NEEDBITS c 3; tl1Rest c) := rfl

theorem v3_le {l : IL} : ((l.hold.toUInt32 &&& ((1 : UInt32) <<< 3 - 1)).toUInt16).toNat ≤ 7 := by
  rw [UInt32.toNat_toUInt16, BITS_toNat l 3 (by decide)]
  have := Nat.mod_lt l.hold.toNat (show 0 < 2 ^ (3 : UInt32).toNat by decide)
  have e : 2 ^ (3 : UInt32).toNat = 8 := rfl
  omega

/-- The state after `lens[order[have++]] = v`. -/
def clSet (s : InflateState) (v : UInt16) : InflateState :=
  { s with «have» := s.«have» + 1, lens := s.lens.set! (orderNat s.«have».toNat) v }

/-- `lens[order[have++]]` on the state record: inside `lens`. -/
theorem lens_store {i : Nat} {h : Heap} {s : InflateState} (hs : h.istates i = some s)
    (hlt : s.«have».toNat < 19) (size : s.lens.size = 320) (v : UInt16) :
    OkOn (setI h i { s with «have» := s.«have» + 1 })
      (Ptr.add (Ptr.ref (WRef.istate_lens i) 0) ((order[s.«have».toNat]!).toNat : Int))
      (Ptr.ref (WRef.istate_lens i) (0 + orderNat s.«have».toNat)) ∧
    Ptr.store (Ptr.ref (WRef.istate_lens i) (0 + orderNat s.«have».toNat)) v
      (setI h i { s with «have» := s.«have» + 1 }) =
      .ok ((), setI h i (clSet s v)) := by
  have stA : (setI h i { s with «have» := s.«have» + 1 }).istates i = some { s with «have» := s.«have» + 1 } := by
    simp [setI]
  have getL := WRef.get_istate_lens stA
  have olt : orderNat s.«have».toNat < 19 := Zlib.Inflate.Proofs.order_lt _ hlt
  refine ⟨Ptr.add_nat_ok getL (by show 0 + orderNat s.«have».toNat ≤ s.lens.size; omega), ?_⟩
  have st := Ptr.store_ok (off := 0 + orderNat s.«have».toNat) (v := v) getL rfl
    (by show 0 + orderNat s.«have».toNat < s.lens.size; omega)
  rw [WRef.put_istate_lens stA] at st
  rw [st]
  simp only [Nat.zero_add, setI, upd_upd, clSet]

theorem tl1Rest_run (c : BCtx) {i : Nat} (hc : c.st = some (.tab i)) {h : Heap} {s : InflateState}
    (hs : h.istates i = some s) (hlt : s.«have».toNat < 19) (size : s.lens.size = 320) (l : IL) :
    runX (tl1Rest c) l h = .ok ((.ok (), { l with hold := l.hold >>> (3 : UInt32).toUInt64, bits := l.bits - 3 }),
      setI h i (clSet s (l.hold.toUInt32 &&& ((1 : UInt32) <<< 3 - 1)).toUInt16)) := by
  obtain ⟨add, st⟩ := lens_store hs hlt size ((l.hold.toUInt32 &&& ((1 : UInt32) <<< 3 - 1)).toUInt16)
  unfold tl1Rest
  rw [hc]
  have ld : ldInflateState (some (.tab i)) h = .ok (s, h) := ldInflateState_tab hs
  have wA : wrS (some (.tab i)) (fun s => { s with «have» := s.«have» + 1 }) h =
      .ok ((), setI h i { s with «have» := s.«have» + 1 }) := wrS_tab hs _
  have ord := orderAt_run (setI h i { s with «have» := s.«have» + 1 }) s.«have» hlt
  simp only [runX_bind, runX_lift_ok ld, runX_lift_ok wA, runX_lift_ok ord, BITS_run _ _ 3 (by decide), lensP,
    runX_lift_ok add, runX_lift_ok st, DROPBITS_run _ _ 3 (by decide)]

theorem tl2Body_run (c : BCtx) {i : Nat} (hc : c.st = some (.tab i)) {h : Heap} {s : InflateState}
    (hs : h.istates i = some s) (hlt : s.«have».toNat < 19) (size : s.lens.size = 320) (l : IL) :
    runX (tl2Body c) l h = .ok ((.ok (), l), setI h i (clSet s 0)) := by
  obtain ⟨add, st⟩ := lens_store hs hlt size 0
  unfold tl2Body
  rw [hc]
  have ld : ldInflateState (some (.tab i)) h = .ok (s, h) := ldInflateState_tab hs
  have wA : wrS (some (.tab i)) (fun s => { s with «have» := s.«have» + 1 }) h =
      .ok ((), setI h i { s with «have» := s.«have» + 1 }) := wrS_tab hs _
  have ord := orderAt_run (setI h i { s with «have» := s.«have» + 1 }) s.«have» hlt
  simp only [runX_bind, runX_lift_ok ld, runX_lift_ok wA, runX_lift_ok ord, lensP, runX_lift_ok add,
    runX_lift_ok st]

theorem clSet_have {s : InflateState} (lt : s.«have».toNat < 19) (v : UInt16) :
    (clSet s v).«have».toNat = s.«have».toNat + 1 := by
  show (s.«have» + 1).toNat = _
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_one]
  omega

theorem clSet_wf {s : InflateState} (wf : s.WellFormed) (v : UInt16) : (clSet s v).WellFormed :=
  ⟨by simp [clSet, wf.1], wf.2.1, wf.2.2⟩

theorem clSet_inv {s : InflateState} (cl : CLInv s) (lt : s.«have».toNat < 19) (size : s.lens.size = 320)
    {v : UInt16} (hv : v.toNat ≤ 7) :
    CLInv (clSet s v) := by
  intro k hk ⟨j, hj, hjk⟩
  rw [clSet_have lt] at hj
  show ((s.lens.set! (orderNat s.«have».toNat) v).getD k 0).toNat ≤ 7
  rw [Zlib.Inftrees.Proofs.getD_set!]
  split
  · exact hv
  · next ne =>
    rcases Nat.lt_or_ge j s.«have».toNat with x | x
    · exact cl k hk ⟨j, x, hjk⟩
    · have e : j = s.«have».toNat := by omega
      subst e
      exfalso
      apply ne
      refine ⟨hjk, ?_⟩
      have := Zlib.Inflate.Proofs.order_lt _ lt
      rw [size]; omega

theorem clSet_tab {s : InflateState} (st : TabSt s) (v : UInt16) : TabSt (clSet s v) :=
  ⟨st.mode, st.nlen, st.ndist, st.ncode⟩

/-- **The code-length code lengths read from the stream, on the invariant.** -/
theorem tabLoop1_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (st : TabSt s) (hv : s.«have».toNat ≤ s.ncode.toNat)
    (cl : CLInv s) :
    ∃ res l' h' log', runX (tabLoop1 c) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → baseM pr l' log' ≤ baseM pr l log ∧ ∃ s', h'.istates i = some s' ∧ TabSt s' ∧
        s'.«have».toNat = s'.ncode.toNat ∧ CLInv s') ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  have key := xwhileBrk_wf (cond := tl1Cond c) (body := (do tl1Body c; pure false : X Bool))
    (fun l1 h1 => ∃ log1 s1, PInv c pr h0 h1 l1 log1 ∧ h1.istates i = some s1 ∧ TabSt s1 ∧
      s1.«have».toNat ≤ s1.ncode.toNat ∧ CLInv s1 ∧ baseM pr l1 log1 ≤ baseM pr l log)
    (fun res l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧
      (res = .ok () → baseM pr l1 log1 ≤ baseM pr l log ∧ ∃ s1, h1.istates i = some s1 ∧ TabSt s1 ∧
        s1.«have».toNat = s1.ncode.toNat ∧ CLInv s1) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l1.ret = Z_BUF_ERROR))
    (fun _ h1 => tabGap i (fun s => s.ncode.toNat) h1)
    (fun l1 h1 hI => by
      obtain ⟨log1, s1, I1, hs1, st1, hv1, cl1, b1⟩ := hI
      have ld1 : ldInflateState c.st h1 = .ok (s1, h1) := by rw [I1.cst]; exact ldInflateState_tab hs1
      have hcond : runX (tl1Cond c) l1 h1 = .ok ((.ok (decide (s1.«have» < s1.ncode)), l1), h1) := by
        unfold tl1Cond; rw [runX_bind, runX_lift_ok ld1]; rfl
      refine ⟨l1, h1, _, hcond, fun hT => ?_, fun hF => ?_⟩
      · have lt : s1.«have».toNat < s1.ncode.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hT)
        obtain ⟨res2, l2, h2, log2, run2, I2, okc, errc, ist2, meas2⟩ := NEEDBITS_p c pr 3 (by decide) I1
        have b2 := baseM_le meas2
        cases res2 with
        | error e =>
          obtain ⟨rfl, ret⟩ := errc e rfl
          refine ⟨.error Ex.leave, l2, h2, ?_, log2, I2, fun x => (nomatch x), fun e x => ?_⟩
          · rw [runX_bind, tl1Body_eq, runX_bind, run2]
          · injection x with x; subst x; exact ⟨rfl, ret⟩
        | ok u =>
          cases u
          obtain ⟨b3, -, -, -⟩ := okc rfl
          have hs2 : h2.istates i = some s1 := ist2.trans hs1
          obtain ⟨z2, s2, valid2, -, -⟩ := I2.valid
          have e2 : s2 = s1 := Option.some.inj (valid2.2.1.symm.trans hs2)
          subst e2
          have wf := valid2.2.2.2.2.2.1
          have hl19 : s2.«have».toNat < 19 := by have := st1.ncode; omega
          have rest := tl1Rest_run c I2.cst hs2 hl19 wf.1 l2
          have v3 := v3_le (l := l2)
          generalize hV : (l2.hold.toUInt32 &&& ((1 : UInt32) <<< 3 - 1)).toUInt16 = V at rest v3
          have hsF : (setI h2 i (clSet s2 V)).istates i = some (clSet s2 V) := by simp [setI]
          have IF := I2.setState hs2 (clSet s2 V) rfl rfl rfl
            (clSet_wf wf _) (modeOk_of (Or.inr (Or.inl st1.mode)))
          have b3' : (3 : UInt32).toNat ≤ l2.bits.toNat := b3
          obtain ⟨B3, -, hbit3⟩ := DROPBITS_inv (bitInv_of IF) 3 b3' (by decide)
          have IG := IF.regs (l' := { l2 with hold := l2.hold >>> (3 : UInt32).toUInt64, bits := l2.bits - 3 })
            rfl rfl rfl rfl (by have := I2.bits.1; show (l2.bits - 3).toNat ≤ 39; rw [hbit3]; omega) B3.hold_lt
          refine ⟨.ok false, _, _, ?_, ⟨log2, _, IG, hsF, clSet_tab st1 _, ?_, clSet_inv cl1 hl19 wf.1 v3, ?_⟩,
            ?_⟩
          · rw [runX_bind, tl1Body_eq, runX_bind, run2]
            simp only []
            rw [rest]
            rfl
          · rw [clSet_have hl19]; show s2.«have».toNat + 1 ≤ s2.ncode.toNat; omega
          · unfold baseM at b1 b2 ⊢
            show 4 * ((l2.bits - 3).toNat + 8 * l2.have_.toNat + _) ≤ _
            rw [hbit3]
            omega
          · show tabGap i (fun s => s.ncode.toNat) (setI h2 i (clSet s2 V)) < tabGap i (fun s => s.ncode.toNat) h1
            rw [tabGap_of hsF, tabGap_of hs1, clSet_have hl19]
            show s2.ncode.toNat - (s2.«have».toNat + 1) < s2.ncode.toNat - s2.«have».toNat
            omega
      · have ge : ¬ s1.«have» < s1.ncode := fun x => by simp [x] at hF
        have ge' : s1.ncode.toNat ≤ s1.«have».toNat := Nat.le_of_not_lt (mt UInt32.lt_iff_toNat_lt.mpr ge)
        exact ⟨log1, I1, fun _ => ⟨b1, s1, hs1, st1, by omega, cl1⟩, fun e x => (nomatch x)⟩)
    (l := l) (h := h) ⟨log, s, I, hs, st, hv, cl, Nat.le_refl _⟩
    (by rw [tabGap_of hs]; have := st.ncode; unfold fuel; omega)
  obtain ⟨res, l', h', hr, log', I', okc, errc⟩ := key
  exact ⟨res, l', h', log', by unfold tabLoop1 xwhile; exact hr, I', okc, errc⟩

/-- **The code-length code lengths not sent, set to 0, on the invariant.** No call-back runs. -/
theorem tabLoop2_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (st : TabSt s) (hv : s.«have».toNat ≤ 19) (cl : CLInv s) :
    ∃ h', runX (tabLoop2 c) l h = .ok ((.ok (), l), h') ∧ PInv c pr h0 h' l log ∧
      ∃ s', h'.istates i = some s' ∧ TabSt s' ∧ s'.«have».toNat = 19 ∧ CLInv s' := by
  have key := xwhileBrk_wf (cond := tl2Cond c) (body := (do tl2Body c; pure false : X Bool))
    (fun l1 h1 => l1 = l ∧ ∃ s1, PInv c pr h0 h1 l log ∧ h1.istates i = some s1 ∧ TabSt s1 ∧
      s1.«have».toNat ≤ 19 ∧ CLInv s1)
    (fun res l1 h1 => res = .ok () ∧ l1 = l ∧ PInv c pr h0 h1 l log ∧ ∃ s1, h1.istates i = some s1 ∧ TabSt s1 ∧
      s1.«have».toNat = 19 ∧ CLInv s1)
    (fun _ h1 => tabGap i (fun _ => 19) h1)
    (fun l1 h1 hI => by
      obtain ⟨rfl, s1, I1, hs1, st1, hv1, cl1⟩ := hI
      have ld1 : ldInflateState c.st h1 = .ok (s1, h1) := by rw [I1.cst]; exact ldInflateState_tab hs1
      have hcond : runX (tl2Cond c) l1 h1 = .ok ((.ok (decide (s1.«have» < 19)), l1), h1) := by
        unfold tl2Cond; rw [runX_bind, runX_lift_ok ld1]; rfl
      refine ⟨l1, h1, _, hcond, fun hT => ?_, fun hF => ?_⟩
      · have lt : s1.«have».toNat < 19 := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hT)
        obtain ⟨z1, s2, valid1, -, -⟩ := I1.valid
        have e2 : s2 = s1 := Option.some.inj (valid1.2.1.symm.trans hs1)
        subst e2
        have wf := valid1.2.2.2.2.2.1
        have run := tl2Body_run c I1.cst hs1 lt wf.1 l1
        have IF := I1.setState hs1 (clSet s2 0) rfl rfl rfl (clSet_wf wf _) (modeOk_of (Or.inr (Or.inl st1.mode)))
        have hsF : (setI h1 i (clSet s2 0)).istates i = some (clSet s2 0) := by simp [setI]
        refine ⟨.ok false, l1, _, ?_, ⟨rfl, _, IF, hsF, clSet_tab st1 _, ?_, clSet_inv cl1 lt wf.1 (v := 0) (by decide)⟩,
          ?_⟩
        · rw [runX_bind, run]; rfl
        · rw [clSet_have lt]; omega
        · show tabGap i (fun _ => 19) (setI h1 i (clSet s2 0)) < tabGap i (fun _ => 19) h1
          rw [tabGap_of hsF, tabGap_of hs1, clSet_have lt]
          omega
      · have ge : ¬ s1.«have» < 19 := fun x => by simp [x] at hF
        have ge' : 19 ≤ s1.«have».toNat := Nat.le_of_not_lt (fun x => ge (UInt32.lt_iff_toNat_lt.mpr x))
        exact ⟨rfl, rfl, I1, s1, hs1, st1, by omega, cl1⟩)
    (l := l) (h := h) ⟨rfl, s, I, hs, st, hv, cl⟩
    (by rw [tabGap_of hs]; unfold fuel; omega)
  obtain ⟨res, l', h', hr, rfl, rfl, I', rest⟩ := key
  exact ⟨h', by unfold tabLoop2 xwhile; exact hr, I', rest⟩

/-- After the two loops, the 19 code-length code lengths are at most 7. -/
theorem CLInv.all {s : InflateState} (cl : CLInv s) (full : s.«have».toNat = 19) :
    ∀ k, k < 19 → (s.lens.getD k 0).toNat ≤ 7 := by
  intro k hk
  obtain ⟨j, hj, e⟩ := Zlib.Inflate.Proofs.order_surj k hk
  exact cl k hk ⟨j, by omega, e⟩

end Zlib.Infback.Safety
