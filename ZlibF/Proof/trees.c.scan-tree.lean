import ZlibF.Proof.«trees.c.build.frame»
import ZlibF.Proof.«trees.c.runs»

/-! # trees.c: actual code-length scanning

The run model and the frequency-by-iteration argument follow the reference
EmitScanTree proof. Executions use this translation's arrays and source order.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

abbrev SCLocals := Int32 × Int32 × Int32 × Int32 × Int32 × Int32 × Int32

/-- The frequency-writing branch of the actual scan body. -/
def scCounts (s : DeflateStatePtr) (curlen prevlen count min_count : Int32) : M Unit := do
  let blt ← pBltree s
  if count.toInt < min_count.toInt then
    setFc blt curlen.toInt ((← getFc blt curlen.toInt) + i2us count)
  else if curlen != 0 then
    if curlen != prevlen then setFc blt curlen.toInt ((← getFc blt curlen.toInt) + 1)
    setFc blt REP_3_6.toInt ((← getFc blt REP_3_6.toInt) + 1)
  else if count.toInt ≤ 10 then
    setFc blt REPZ_3_10.toInt ((← getFc blt REPZ_3_10.toInt) + 1)
  else
    setFc blt REPZ_11_138.toInt ((← getFc blt REPZ_11_138.toInt) + 1)

/-- The local-variable tail of the actual scan. -/
def scTail (n curlen nextlen : Int32) : SCLocals :=
  let (mx, mn) : Int32 × Int32 :=
    if nextlen == 0 then (138, 3) else if curlen == nextlen then (6, 3) else (7, 4)
  (n, curlen, nextlen, 0, mx, mn, 0)

/-- The actual loop body, retaining its early continue. -/
def scBody (s : DeflateStatePtr) (tree : CtDataPtr) : SCLocals → M SCLocals :=
  fun (n, prevlen, nextlen, count, max_count, min_count, _) => do
    let curlen := nextlen
    let nextlen := u16i (← getDl tree (← iadd n 1).toInt)
    let count ← iadd count 1
    if count.toInt < max_count.toInt ∧ curlen == nextlen then
      return (n, prevlen, nextlen, count, max_count, min_count, 0)
    scCounts s curlen prevlen count min_count
    return scTail n curlen nextlen

def scLoop (s : DeflateStatePtr) (tree : CtDataPtr) (mc : Int32) (r : SCLocals) : M SCLocals :=
  cfor (fun (n, _) => pure (decide (n.toInt ≤ mc.toInt)))
    (fun (n, rest) => do pure (← iadd n 1, rest)) (scBody s tree) r

/-- Naming fragments does not change the actual function. -/
theorem scan_tree_eq (s : DeflateStatePtr) (tree : CtDataPtr) (mc : Int32) :
    scan_tree s tree mc = (do
      let nextlen0 := u16i (← getDl tree 0)
      let (mx0, mn0) : Int32 × Int32 := if nextlen0 == 0 then (138, 3) else (7, 4)
      setDl tree (← iadd mc 1).toInt 0xffff
      let _ ← scLoop s tree mc (0, -1, nextlen0, 0, mx0, mn0, 0)
      pure ()) := by
  unfold scan_tree scLoop scBody scCounts scTail
  simp only [M_bind_assoc, merge_ite_bind]

/-- Array effects of a finished run. This data model leaves 16-bit frequency
addition wrapping, exactly as the actual stores do. -/
def scFreqUpdate (B : Array CtData) (cur : Nat) (prev : Int) (cnt mn : Nat) : Array CtData :=
  if cnt < mn then Out.addFc B cur (UInt16.ofNat cnt)
  else if cur ≠ 0 then
    Out.addFc (if (cur : Int) ≠ prev then Out.addFc B cur 1 else B) 16 1
  else if cnt ≤ 10 then Out.addFc B 17 1
  else Out.addFc B 18 1

theorem scFreqUpdate_size (B : Array CtData) (cur : Nat) (prev : Int) (cnt mn : Nat) :
    (scFreqUpdate B cur prev cnt mn).size = B.size := by
  unfold scFreqUpdate
  split
  · simp
  · split
    · split <;> simp
    · split <;> simp

theorem scFreqUpdate_dl (B : Array CtData) (cur : Nat) (prev : Int) (cnt mn k : Nat) :
    (scFreqUpdate B cur prev cnt mn)[k]!.dl = B[k]!.dl := by
  unfold scFreqUpdate
  split
  · exact Out.addFc_dl _ _ _ _
  · split
    · rw [Out.addFc_dl]; split <;> simp [Out.addFc_dl]
    · split <;> exact Out.addFc_dl _ _ _ _

theorem scFreqUpdate_fc (B : Array CtData) (cur : Nat) (prev : Int) (cnt mn k : Nat)
    (hcur : cur ≤ 15) (hB : 19 ≤ B.size) :
    (scFreqUpdate B cur prev cnt mn)[k]!.fc =
      B[k]!.fc + UInt16.ofNat (Out.runFreq (some (cur, prev, cnt, mn)) k) := by
  by_cases hs : cnt < mn
  · simp only [scFreqUpdate, Out.runFreq, ite_eq_left hs]
    rw [Out.addFc_fc _ _ _ (by omega)]
    split <;> simp_all
  · by_cases hz : cur ≠ 0
    · simp only [scFreqUpdate, Out.runFreq, ite_eq_right hs, ite_eq_left hz]
      by_cases hp : (cur : Int) ≠ prev
      · rw [ite_eq_left hp, Out.addFc_fc _ _ _ (by simp; omega), Out.addFc_fc _ _ _ (by omega)]
        by_cases hk : k = cur <;> by_cases hk16 : k = 16 <;>
          simp_all [UInt16.add_assoc]
      · rw [ite_eq_right hp, Out.addFc_fc _ _ _ (by omega)]
        by_cases hk16 : k = 16 <;> simp_all
    · simp only [scFreqUpdate, Out.runFreq, ite_eq_right hs, ite_eq_right hz]
      by_cases hc : cnt ≤ 10
      · rw [ite_eq_left hc, Out.addFc_fc _ _ _ (by omega)]
        split <;> simp_all
      · rw [ite_eq_right hc, Out.addFc_fc _ _ _ (by omega)]
        split <;> simp_all

/-- A single actual frequency read/add/store has its exact array effect. -/
theorem ws_scAdd {h0 : Heap} {id : Nat} {d : DeflateState} (i : Int) (v : UInt16)
    (hi0 : 0 ≤ i) (hiB : i < d.bl_tree.size) :
    WS h0 id (do
      setFc (.ref (.dstate_bl_tree id) 0) i ((← getFc (.ref (.dstate_bl_tree id) 0) i) + v)) d
      (fun _ e => e = { d with bl_tree := Out.addFc d.bl_tree i.toNat v }) := by
  refine WS.bind' (ws_getFc .bl i hi0 hiB) fun f e ⟨hf, he⟩ => ?_
  subst e; subst f
  refine WS.mono (ws_setFc .bl i _ hi0 hiB) ?_
  intro _ e he
  exact he

/-- All finished-run frequency branches execute with exact array effects.
Only bounds on real scalar values and array storage are assumed. -/
theorem ws_scCounts {h0 : Heap} {id : Nat} {d : DeflateState}
    (cur prev count minc : Int32) (c cnt mn : Nat) (p : Int)
    (hc : cur.toInt = c) (hp : prev.toInt = p) (hcnt : count.toInt = cnt) (hmn : minc.toInt = mn)
    (hc15 : c ≤ 15) (hcnt16 : cnt < 65536) (hB : 19 ≤ d.bl_tree.size) :
    WS h0 id (scCounts (Sp id) cur prev count minc) d
      (fun _ e => e = { d with bl_tree := scFreqUpdate d.bl_tree c p cnt mn }) := by
  have hcur0 : ((cur != 0) = true) ↔ c ≠ 0 := by
    simp only [bne_iff_ne, ne_eq, ← Int32.toInt_inj, hc]
    change ¬ (c : Int) = 0 ↔ c ≠ 0
    omega
  have hcurprev : ((cur != prev) = true) ↔ (c : Int) ≠ p := by
    simp only [bne_iff_ne, ne_eq, ← Int32.toInt_inj, hc, hp]
  have hcast : i2us count = UInt16.ofNat cnt := by
    apply UInt16.toNat_inj.mp
    simp only [i2us, hcnt, UInt16.toNat_ofNat']
    omega
  have hsmall : count.toInt < minc.toInt ↔ cnt < mn := by omega
  have hten : count.toInt ≤ 10 ↔ cnt ≤ 10 := by omega
  unfold scCounts pBltree
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' ws_sid fun i e ⟨hi, he⟩ => ?_
  subst i; subst e
  simp only [hsmall, hten, hc, hcur0, hcurprev, hcast]
  unfold scFreqUpdate
  split
  · rename_i hs
    refine WS.mono (ws_scAdd (c : Int) (UInt16.ofNat cnt) (by omega) (by omega)) ?_
    intro _ e he; simpa [hs] using he
  · rename_i hs
    split
    · rename_i hz
      split
      · rename_i hp
        refine WS.bind' (ws_getFc .bl (c : Int) (by omega) (by change (c : Int) < d.bl_tree.size; omega))
          fun f e ⟨hf, he⟩ => ?_
        subst e; subst f
        refine WS.bind' (ws_setFc .bl (c : Int) _ (by omega) (by change (c : Int) < d.bl_tree.size; omega))
          fun _ e he => ?_
        subst e
        refine WS.mono (ws_scAdd REP_3_6.toInt 1 (by decide +kernel)
          (by change (16 : Int) < (Out.addFc d.bl_tree c 1).size; simp; omega)) ?_
        intro _ e he; simpa [hs, hz, hp, REP_3_6, Out.addFc, TK.setArr, TK.arr] using he
      · rename_i hp
        refine WS.mono (ws_scAdd REP_3_6.toInt 1 (by decide +kernel) (by change (16 : Int) < d.bl_tree.size; omega)) ?_
        intro _ e he; simpa [hs, hz, hp, REP_3_6, Out.addFc, TK.setArr, TK.arr] using he
    · rename_i hz
      split
      · rename_i ht
        refine WS.mono (ws_scAdd REPZ_3_10.toInt 1 (by decide +kernel) (by change (17 : Int) < d.bl_tree.size; omega)) ?_
        intro _ e he; simpa [hs, hz, ht, REPZ_3_10, REPZ_11_138] using he
      · rename_i ht
        refine WS.mono (ws_scAdd REPZ_11_138.toInt 1 (by decide +kernel) (by change (18 : Int) < d.bl_tree.size; omega)) ?_
        intro _ e he; simpa [hs, hz, ht, REPZ_3_10, REPZ_11_138] using he

/-- Correspondence between the actual seven scalar locals and the pure run
state. The final unused scalar has no semantic constraint. -/
def SCCorr (r : SCLocals) (n : Nat) (s : Out.RunSt) : Prop :=
  r.1.toInt = n ∧ r.2.1.toInt = s.prev ∧ r.2.2.1.toInt = s.next ∧
  r.2.2.2.1.toInt = s.cnt ∧ r.2.2.2.2.1.toInt = s.mx ∧ r.2.2.2.2.2.1.toInt = s.mn

/-- A pure run changes the frequency array only when it finishes a group. -/
def scStepTree (B : Array CtData) (L : Nat → Nat) (n : Nat) (s : Out.RunSt) : Array CtData :=
  if s.cnt + 1 < s.mx ∧ s.next = L (n + 1) then B
  else scFreqUpdate B s.next s.prev (s.cnt + 1) s.mn

theorem scStepTree_size (B : Array CtData) (L : Nat → Nat) (n : Nat) (s : Out.RunSt) :
    (scStepTree B L n s).size = B.size := by
  unfold scStepTree
  split
  · rfl
  · exact scFreqUpdate_size _ _ _ _ _

theorem scStepTree_dl (B : Array CtData) (L : Nat → Nat) (n k : Nat) (s : Out.RunSt) :
    (scStepTree B L n s)[k]!.dl = B[k]!.dl := by
  unfold scStepTree
  split
  · rfl
  · exact scFreqUpdate_dl _ _ _ _ _ _

theorem scStepTree_fc (B : Array CtData) (L : Nat → Nat) (n k : Nat) (s : Out.RunSt)
    (hcur : s.next ≤ 15) (hB : 19 ≤ B.size) :
    (scStepTree B L n s)[k]!.fc = B[k]!.fc + UInt16.ofNat (Out.runFreq (Out.runStep L n s).2 k) := by
  unfold scStepTree Out.runStep
  by_cases ha : s.cnt + 1 < s.mx ∧ s.next = L (n + 1)
  · simp only [ite_eq_left ha, Out.runFreq, show UInt16.ofNat 0 = 0 from rfl, UInt16.add_zero]
  · simp only [ite_eq_right ha]
    exact scFreqUpdate_fc _ _ _ _ _ _ hcur hB

/-- Scalar tail assignment agrees with the model's finished-run state. -/
theorem scTail_corr (n cur nx : Int32) (N C X : Nat)
    (hn : n.toInt = N) (hc : cur.toInt = C) (hx : nx.toInt = X) :
    SCCorr (scTail n cur nx) N
      (if X = 0 then ⟨C, X, 0, 138, 3⟩ else if C = X then ⟨C, X, 0, 6, 3⟩ else ⟨C, X, 0, 7, 4⟩) := by
  have hz : ((nx == 0) = true) ↔ X = 0 := by
    simp only [beq_iff_eq, ← Int32.toInt_inj, hx]
    change (X : Int) = 0 ↔ X = 0
    omega
  have he : ((cur == nx) = true) ↔ C = X := by
    simp only [beq_iff_eq, ← Int32.toInt_inj, hc, hx, Int.natCast_inj]
  simp only [scTail, hz, he]
  split
  · exact ⟨hn, hc, hx, rfl, rfl, rfl⟩
  · split <;> exact ⟨hn, hc, hx, rfl, rfl, rfl⟩

/-- One actual scan body agrees with runStep, including the early continue
and every frequency branch. No loop or callee behavior is assumed. -/
theorem ws_scBody {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (L : Nat → Nat) (n : Nat) (s : Out.RunSt) (r : SCLocals)
    (hcorr : SCCorr r n s) (hi : Out.RunInv s) (hn : n ≤ 285)
    (hread : n + 1 < (tk.arr d).size)
    (hl : (tk.arr d)[n + 1]!.dl.toNat = L (n + 1))
    (hcur : s.next ≤ 15) (hB : 19 ≤ d.bl_tree.size) :
    WS h0 id (scBody (Sp id) (.ref (tk.ref id) 0) r) d (fun r' e =>
      SCCorr r' n (Out.runStep L n s).1 ∧
      e = { d with bl_tree := scStepTree d.bl_tree L n s }) := by
  rcases r with ⟨ni, pi, ci, ki, mi, mni, unused⟩
  obtain ⟨hnc, hpc, hcc, hkc, hmc, hmnc⟩ := hcorr
  dsimp only at hnc hpc hcc hkc hmc hmnc
  have hmx : s.mx ≤ 138 := by
    by_cases hz : s.next = 0
    · exact (hi.2.1 hz).1 ▸ Nat.le_refl _
    · rcases hi.2.2.1 hz with ⟨h, rest⟩ | ⟨h, rest⟩ <;> omega
  have hc0 : 0 ≤ s.cnt := Nat.zero_le _
  have hcnt := hi.1
  have hone : (1 : Int32).toInt = 1 := rfl
  unfold scBody
  refine WS.bind' (ws_iadd ni 1 (by omega) (by omega)) fun ni1 e ⟨hn1, he⟩ => ?_
  subst e
  have hn1N : ni1.toInt.toNat = n + 1 := by omega
  refine WS.bind' (ws_getDl tk ni1.toInt (by omega) (by omega)) fun len e ⟨hlen, he⟩ => ?_
  subst e; subst len
  have hnx : (u16i (tk.arr d)[ni1.toInt.toNat]!.dl).toInt = L (n + 1) := by
    rw [Out.u16i_toInt, hn1N, hl]
  refine WS.bind' (ws_iadd ki 1 (by omega) (by omega)) fun ki1 e ⟨hk1, he⟩ => ?_
  subst e
  have hk1N : ki1.toInt = (s.cnt + 1 : Nat) := by omega
  have hsame : ((ci == u16i (tk.arr d)[ni1.toInt.toNat]!.dl) = true) ↔ s.next = L (n + 1) := by
    simp only [beq_iff_eq, ← Int32.toInt_inj, hcc, hnx, Int.natCast_inj]
  have hcond : (ki1.toInt < mi.toInt ∧ (ci == u16i (tk.arr d)[ni1.toInt.toNat]!.dl) = true) ↔
      s.cnt + 1 < s.mx ∧ s.next = L (n + 1) := by
    rw [hsame, hk1N, hmc]
    omega
  simp only [hcond]
  by_cases ha : s.cnt + 1 < s.mx ∧ s.next = L (n + 1)
  · simp only [ha]
    refine WS.pure' ⟨?_, ?_⟩
    · simp only [Out.runStep, ite_eq_left ha, SCCorr]
      exact ⟨hnc, hpc, hnx, hk1N, hmc, hmnc⟩
    · unfold scStepTree
      rw [ite_eq_left ha]
  · simp only [ha, ite_false]
    refine WS.bind' (ws_scCounts ci pi ki1 mni s.next (s.cnt + 1) s.mn s.prev
      hcc hpc hk1N hmnc hcur (by omega) hB) fun _ e he => ?_
    refine WS.pure' ⟨?_, ?_⟩
    · simp only [Out.runStep, ite_eq_right ha]
      exact scTail_corr _ _ _ _ _ _ hnc hcc hnx
    · simpa only [scStepTree, ite_eq_right ha] using he

/-- Frequency state after exactly n iterations. Every length and all record
fields except the bit-length tree are retained. -/
def SCFreqState (d : DeflateState) (L : Nat → Nat) (n : Nat) (e : DeflateState) : Prop :=
  ∃ B : Array CtData, e = { d with bl_tree := B } ∧ B.size = d.bl_tree.size ∧
    (∀ k : Nat, B[k]!.dl = d.bl_tree[k]!.dl) ∧
    ∀ k : Nat, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat (Out.scanFreqUpTo L n k)

theorem scFreqState_init (d : DeflateState) (L : Nat → Nat) : SCFreqState d L 0 d := by
  refine ⟨d.bl_tree, rfl, rfl, fun _ => rfl, ?_⟩
  intro k
  change d.bl_tree[k]!.fc = d.bl_tree[k]!.fc + 0
  exact (UInt16.add_zero _).symm

theorem tk_arr_bl (tk : TK) (d : DeflateState) (B : Array CtData) (hne : tk ≠ .bl) :
    tk.arr { d with bl_tree := B } = tk.arr d := by
  cases tk
  · rfl
  · rfl
  · exact False.elim (hne rfl)

/-- Actual n++ after a body with unchanged loop index. -/
theorem ws_scIncrement {h0 : Heap} {id : Nat} {d : DeflateState}
    (r : SCLocals) (n : Nat) (s : Out.RunSt) (hc : SCCorr r n s) (hn : n ≤ 285) :
    WS h0 id (do let (ni, rest) := r; pure (← iadd ni 1, rest)) d
      (fun r' e => SCCorr r' (n + 1) s ∧ e = d) := by
  rcases r with ⟨ni, rest⟩
  obtain ⟨hni, hrest⟩ := hc
  dsimp only at hni hrest
  have hone : (1 : Int32).toInt = 1 := rfl
  refine WS.bind' (ws_iadd ni 1 (by omega) (by omega)) fun ni1 e ⟨hni1, he⟩ => ?_
  subst e
  exact WS.pure' ⟨⟨by dsimp only; omega, hrest⟩, rfl⟩

/-- One whole actual iteration, including n++, preserves the exact frequency
history. The next length read follows from the unchanged source alphabet. -/
theorem ws_scIteration {h0 : Heap} {id : Nat} {base e : DeflateState}
    (tk : TK) (hne : tk ≠ .bl) (L : Nat → Nat) (n mc : Nat) (r : SCLocals)
    (hn : n ≤ mc) (hmc : mc ≤ 285) (hT : mc + 1 < (tk.arr base).size)
    (hB : 19 ≤ base.bl_tree.size)
    (hread : ∀ i ≤ mc + 1, (tk.arr base)[i]!.dl.toNat = L i)
    (h16 : ∀ i, L i < 65536) (h15 : ∀ i ≤ mc, L i ≤ 15)
    (hcorr : SCCorr r n (Out.runAt L n)) (hfreq : SCFreqState base L n e) :
    WS h0 id (do
      let (ni, rest) ← scBody (Sp id) (.ref (tk.ref id) 0) r
      pure (← iadd ni 1, rest)) e
      (fun r' e' => SCCorr r' (n + 1) (Out.runAt L (n + 1)) ∧ SCFreqState base L (n + 1) e') := by
  obtain ⟨B, rfl, hBs, hdl, hfc⟩ := hfreq
  have hcur : (Out.runAt L n).next ≤ 15 := by rw [Out.runAt_next]; exact h15 n hn
  have hB' : 19 ≤ B.size := by omega
  refine WS.bind' (ws_scBody tk L n (Out.runAt L n) r hcorr (Out.runInv_runAt L h16 n)
    (by omega) (by rw [tk_arr_bl tk base B hne]; omega)
    (by rw [tk_arr_bl tk base B hne]; exact hread (n + 1) (by omega)) hcur hB')
    fun r' e' ⟨hcorr', he'⟩ => ?_
  subst e'
  refine WS.mono (ws_scIncrement r' n (Out.runStep L n (Out.runAt L n)).1 hcorr' (by omega)) ?_
  intro r'' e'' ⟨hcorr'', he''⟩
  subst e''
  refine ⟨hcorr'', scStepTree B L n (Out.runAt L n), rfl, ?_, ?_, ?_⟩
  · exact (scStepTree_size _ _ _ _).trans hBs
  · intro k
    exact (scStepTree_dl _ _ _ _ _).trans (hdl k)
  · intro k
    rw [scStepTree_fc B L n k _ hcur hB', hfc k]
    simp only [Out.scanFreqUpTo, UInt16.ofNat_add, UInt16.add_assoc]

/-- Complete actual loop: every iteration and its increment execute, the
measure decreases, and the accumulated frequencies equal the run model. -/
theorem ws_scLoop {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hne : tk ≠ .bl) (L : Nat → Nat) (mc : Int32) (M : Nat) (r : SCLocals)
    (hmc : mc.toInt = M) (hM : M ≤ 285) (hT : M + 1 < (tk.arr d).size)
    (hB : 19 ≤ d.bl_tree.size)
    (hread : ∀ i ≤ M + 1, (tk.arr d)[i]!.dl.toNat = L i)
    (h16 : ∀ i, L i < 65536) (h15 : ∀ i ≤ M, L i ≤ 15)
    (hstart : SCCorr r 0 (Out.runAt L 0)) :
    WS h0 id (scLoop (Sp id) (.ref (tk.ref id) 0) mc r) d
      (fun r' e => SCCorr r' (M + 1) (Out.runAt L (M + 1)) ∧ SCFreqState d L (M + 1) e) := by
  let Inv : SCLocals → DeflateState → Prop := fun r' e =>
    ∃ n : Nat, n ≤ M + 1 ∧ SCCorr r' n (Out.runAt L n) ∧ SCFreqState d L n e
  unfold scLoop
  refine WS.cfor2 Inv (fun r' _ => M + 1 - r'.1.toInt.toNat) _ ?_
    ⟨0, by omega, hstart, scFreqState_init d L⟩ (by simp only [fuel]; omega)
  intro r' e hi
  obtain ⟨n, hn, hcorr, hfreq⟩ := hi
  have hni := hcorr.1
  refine WS.pure' ?_
  by_cases hlt : n ≤ M
  · refine Or.inr ⟨by simp only [decide_eq_true_eq]; omega, ?_⟩
    refine WS.mono (ws_scIteration tk hne L n M r' hlt hM hT hB hread h16 h15 hcorr hfreq) ?_
    intro r'' e' ⟨hc, hf⟩
    exact ⟨⟨n + 1, by omega, hc, hf⟩, by have := hc.1; omega⟩
  · refine Or.inl ⟨by simp only [decide_eq_false_iff_not]; omega, ?_⟩
    have hnM : n = M + 1 := by omega
    exact ⟨by simpa only [hnM] using hcorr, by simpa only [hnM] using hfreq⟩

theorem bl_tree_setArr (tk : TK) (d : DeflateState) (T : Array CtData) (hne : tk ≠ .bl) :
    (tk.setArr d T).bl_tree = d.bl_tree := by
  cases tk
  · rfl
  · rfl
  · exact False.elim (hne rfl)

/-- The actual sentinel array, with its full entry retained except for Len. -/
def scGuard (T : Array CtData) (M : Nat) : Array CtData :=
  T.set! (M + 1) { T[M + 1]! with dl := 0xffff }

theorem scGuard_lengths (T : Array CtData) (M : Nat) (hT : M + 1 < T.size) (i : Nat) :
    (scGuard T M)[i]!.dl.toNat = Out.guarded (fun n => T[n]!.dl.toNat) M i := by
  unfold scGuard Out.guarded
  rw [getD_set T (M + 1) i _ hT]
  split <;> rfl

/-- `local void scan_tree(deflate_state *s, ct_data *tree, int max_code)`.
For an internal literal or distance alphabet, the actual complete function
terminates, writes the sentinel and adds exactly the modeled run frequencies.
The explicit internal bounds are obtained from actual tree construction in
the composition theorem. No public API domain restriction is proposed. -/
theorem ws_scan_tree {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hne : tk ≠ .bl) (mc : Int32) (hmc0 : 0 ≤ mc.toInt) (hmc285 : mc.toInt ≤ 285)
    (hT : mc.toInt.toNat + 1 < (tk.arr d).size) (hB : 19 ≤ d.bl_tree.size)
    (h15 : ∀ i ≤ mc.toInt.toNat, (tk.arr d)[i]!.dl.toNat ≤ 15) :
    WS h0 id (scan_tree (Sp id) (.ref (tk.ref id) 0) mc) d (fun _ e =>
      ∃ B : Array CtData,
        e = { tk.setArr d (scGuard (tk.arr d) mc.toInt.toNat) with bl_tree := B } ∧
        B.size = d.bl_tree.size ∧ (∀ k : Nat, B[k]!.dl = d.bl_tree[k]!.dl) ∧
        ∀ k : Nat, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat
          (Out.scanFreqUpTo (Out.guarded (fun i => (tk.arr d)[i]!.dl.toNat) mc.toInt.toNat)
            (mc.toInt.toNat + 1) k)) := by
  let M := mc.toInt.toNat
  let L := Out.guarded (fun i => (tk.arr d)[i]!.dl.toNat) M
  have hm : mc.toInt = M := by dsimp [M]; omega
  have hone : (1 : Int32).toInt = 1 := rfl
  rw [scan_tree_eq]
  refine WS.bind' (ws_getDl tk 0 (by decide +kernel) (by omega)) fun len e ⟨hlen, he⟩ => ?_
  subst e; subst len
  refine WS.bind' (ws_iadd mc 1 (by omega) (by omega)) fun mc1 e ⟨hmc1, he⟩ => ?_
  subst e
  have hmc1N : mc1.toInt.toNat = M + 1 := by omega
  refine WS.bind' (ws_setDl tk mc1.toInt 0xffff (by omega) (by omega)) fun _ e he => ?_
  subst e
  rw [hmc1N]
  let base := tk.setArr d (scGuard (tk.arr d) M)
  have hbaseB : base.bl_tree = d.bl_tree := bl_tree_setArr tk d _ hne
  have hbaseT : tk.arr base = scGuard (tk.arr d) M := tk_arr_setArr tk _
  have hread : ∀ i ≤ M + 1, (tk.arr base)[i]!.dl.toNat = L i := by
    intro i hi
    rw [hbaseT]
    exact scGuard_lengths _ M hT i
  have h16 : ∀ i, L i < 65536 := by
    intro i
    unfold L Out.guarded
    split
    · decide +kernel
    · exact UInt16.toNat_lt _
  have h15' : ∀ i ≤ M, L i ≤ 15 := by
    intro i hi
    simp only [L, Out.guarded, ite_eq_right (show i ≠ M + 1 by omega)]
    exact h15 i hi
  have hl0 : (u16i (tk.arr d)[Int.toNat 0]!.dl).toInt = L 0 := by
    rw [Out.u16i_toInt]
    simp only [L, Out.guarded, ite_eq_right (show 0 ≠ M + 1 by omega)]
    rfl
  have hz : ((u16i (tk.arr d)[Int.toNat 0]!.dl == 0) = true) ↔ L 0 = 0 := by
    simp only [beq_iff_eq, ← Int32.toInt_inj, hl0]
    change (L 0 : Int) = 0 ↔ L 0 = 0
    omega
  have hstart : SCCorr
      (0, -1, u16i (tk.arr d)[Int.toNat 0]!.dl, 0,
        (if u16i (tk.arr d)[Int.toNat 0]!.dl == 0 then ((138, 3) : Int32 × Int32) else (7, 4)).1,
        (if u16i (tk.arr d)[Int.toNat 0]!.dl == 0 then ((138, 3) : Int32 × Int32) else (7, 4)).2, 0)
      0 (Out.runAt L 0) := by
    simp only [Out.runAt, Out.runInit, hz]
    split <;> exact ⟨rfl, rfl, hl0, rfl, rfl, rfl⟩
  refine WS.bind' (ws_scLoop (d := base) tk hne L mc M _ hm (by omega)
    (by rw [hbaseT]; simp only [scGuard, Array.size_set!]; exact hT)
    (by rw [hbaseB]; exact hB) hread h16 h15' hstart) fun r e ⟨hc, hf⟩ => ?_
  obtain ⟨B, he, hBs, hdl, hfc⟩ := hf
  exact WS.pure' ⟨B, he, by rw [← hbaseB]; exact hBs,
    by rw [← hbaseB]; exact hdl, by rw [← hbaseB]; exact hfc⟩

/-- Actual scanning on the live caller heap preserves its output invariant
and pending bits. The descriptor-alphabet bound supplies sentinel capacity. -/
theorem scan_tree_preserves {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (tk : TK) (hne : tk ≠ .bl) (mc : Int32)
    (hmc0 : 0 ≤ mc.toInt) (hmcN : mc.toInt < tk.buildDesc.elems.toInt)
    (h15 : ∀ i ≤ mc.toInt.toNat, (tk.arr d)[i]!.dl.toNat ≤ 15) :
    ∃ (e : DeflateState) (B : Array CtData),
      scan_tree (Sp id) (.ref (tk.ref id) 0) mc h = .ok ((), setD h id e) ∧
      e = { tk.setArr d (scGuard (tk.arr d) mc.toInt.toNat) with bl_tree := B } ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d ∧
      B.size = d.bl_tree.size ∧ (∀ k : Nat, B[k]!.dl = d.bl_tree[k]!.dl) ∧
      ∀ k : Nat, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat
        (Out.scanFreqUpTo (Out.guarded (fun i => (tk.arr d)[i]!.dl.toNat) mc.toInt.toNat)
          (mc.toInt.toNat + 1) k) := by
  have hwf := hI.base.wf
  obtain ⟨hLT, hDT, hBT, hBC, hH, hD⟩ := hwf
  have hmc285 : mc.toInt ≤ 285 := by
    cases tk
    · change mc.toInt < 286 at hmcN; omega
    · change mc.toInt < 30 at hmcN; omega
    · exact False.elim (hne rfl)
  have hT : mc.toInt.toNat + 1 < (tk.arr d).size := by
    cases tk
    · change mc.toInt.toNat + 1 < d.dyn_ltree.size; omega
    · change mc.toInt < 30 at hmcN
      change mc.toInt.toNat + 1 < d.dyn_dtree.size; omega
    · exact False.elim (hne rfl)
  obtain ⟨a, e, he, B, heB, hBs, hdl, hfc⟩ := ws_scan_tree (h0 := h) tk hne mc hmc0 hmc285 hT
    (by omega) h15
  have ha : a = () := Subsingleton.elim _ _
  subst a
  rw [setD_self hI.base.dstate] at he
  let guard := tk.setArr d (scGuard (tk.arr d) mc.toInt.toNat)
  have hguard := BTBuildFrame.codes tk tk d (scGuard (tk.arr d) mc.toInt.toNat)
    (by simp only [scGuard, Array.size_set!])
  have hguardB : guard.bl_tree = d.bl_tree := bl_tree_setArr tk d _ hne
  have hBframe := BTBuildFrame.codes .bl .bl guard B
    (by change B.size = guard.bl_tree.size; rw [hguardB]; exact hBs)
  have hIe := hBframe.treesInvAt (hguard.treesInvAt hI)
  have hout := (hBframe.outBits buf).trans (hguard.outBits buf)
  rw [setD_setD] at hIe
  have hee : e = TK.bl.setArr guard B := heB
  refine ⟨e, B, he, heB, ?_, ?_, hBs, hdl, hfc⟩
  · rw [hee]; exact hIe
  · rw [hee]; exact hout

/-- Independent accepted lengths supply the real scan's code-length bound. -/
theorem acceptable_scan_lengths (tk : TK) (d : DeflateState) (M : Nat)
    (ha : ZlibF.Spec.Acceptable .codeLength
      (Zlib.Inftrees.Proofs.lensOf (fun i => (tk.arr d)[i]!.dl.toNat) (M + 1))) :
    ∀ i ≤ M, (tk.arr d)[i]!.dl.toNat ≤ 15 := by
  intro i hi
  apply ha.1 _
  unfold Zlib.Inftrees.Proofs.lensOf
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩

/-- The actual tree constructor supplies every scalar, length and capacity
premise of actual scan_tree. Both calls run on one heap. This bridges tree
construction to description-frequency scanning, rather than assuming the
scan's precondition as a callee contract. -/
theorem build_tree_scan {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (tk : TK) (hne : tk ≠ .bl) :
    ∃ (built e : DeflateState) (B : Array CtData),
      build_tree (Sp id) (some (tk.descRef id)) h = .ok ((), setD h id built) ∧
      (do build_tree (Sp id) (some (tk.descRef id))
          scan_tree (Sp id) (.ref (tk.ref id) 0) (tk.getDesc (← rd (Sp id))).max_code) h =
        .ok ((), setD h id e) ∧
      scan_tree (Sp id) (.ref (tk.ref id) 0) (tk.getDesc built).max_code (setD h id built) =
        .ok ((), setD h id e) ∧
      e = { tk.setArr built (scGuard (tk.arr built) (tk.getDesc built).max_code.toInt.toNat) with bl_tree := B } ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d ∧
      B.size = built.bl_tree.size ∧
      ∀ k : Nat, B[k]!.fc = built.bl_tree[k]!.fc + UInt16.ofNat
        (Out.scanFreqUpTo
          (Out.guarded (fun i => (tk.arr built)[i]!.dl.toNat) (tk.getDesc built).max_code.toInt.toNat)
          ((tk.getDesc built).max_code.toInt.toNat + 1) k) := by
  obtain ⟨a, built, hbuild, hframe, M, hM, hmax, haccept, hdecode⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) tk hI.base.wf hI.base.static hI.run.to0)
    (ws_build_tree_decodable_initialized (h0 := h) tk hI.base.wf hI.base.static hI.run.to0)
  have ha : a = () := Subsingleton.elim _ _
  subst a
  rw [setD_self hI.base.dstate] at hbuild
  have hmc0 : 0 ≤ (tk.getDesc built).max_code.toInt := by omega
  have hmcN : (tk.getDesc built).max_code.toInt < tk.buildDesc.elems.toInt := by
    have hN0 : 0 ≤ tk.buildDesc.elems.toInt := by cases tk <;> decide +kernel
    omega
  have hlens := acceptable_scan_lengths tk built M (haccept .codeLength)
  have hlens' : ∀ i ≤ (tk.getDesc built).max_code.toInt.toNat, (tk.arr built)[i]!.dl.toNat ≤ 15 := by
    intro i hi
    exact hlens i (by omega)
  obtain ⟨e, B, hscan, heB, hIe, hout, hBs, hdl, hfc⟩ :=
    scan_tree_preserves (hframe.treesInvAt hI) tk hne (tk.getDesc built).max_code hmc0 hmcN hlens'
  rw [setD_setD] at hscan hIe
  refine ⟨built, e, B, hbuild, ?_, hscan, heB, hIe, hout.trans (hframe.outBits buf), hBs, hfc⟩
  have hrd : rd (Sp id) (setD h id built) = .ok (built, setD h id built) :=
    Out.rd_run (setD_dstates_same h id built)
  rw [bind_app, hbuild]
  simp only []
  rw [bind_app, hrd]
  exact hscan

/-- A finished run contributes at most its consumed length to any one
frequency. Repeated nonzero lengths use at most two symbols and require at
least three consumed lengths. -/
theorem scRunFreq_le (cur cnt mn k : Nat) (prev : Int) (hc : 1 ≤ cnt) (hm : 3 ≤ mn) :
    Out.runFreq (some (cur, prev, cnt, mn)) k ≤ cnt := by
  simp only [Out.runFreq]
  split
  · split <;> omega
  · rename_i hs
    split
    · split <;> split <;> omega
    · split <;> split <;> omega

/-- Finished counts plus the unfinished run never exceed the number of
scanned lengths. This supplies the non-wrapping bound for a real alphabet. -/
theorem scanFreq_with_pending_le (L : Nat → Nat) (hL : ∀ i, L i < 65536) (n k : Nat) :
    Out.scanFreqUpTo L n k + (Out.runAt L n).cnt ≤ n := by
  induction n with
  | zero =>
    simp only [Out.scanFreqUpTo, Out.runAt, Out.runInit]
    split <;> simp
  | succ n ih =>
    have hi := Out.runInv_runAt L hL n
    have hmn : 3 ≤ (Out.runAt L n).mn := by
      by_cases hz : (Out.runAt L n).next = 0
      · have := (hi.2.1 hz).2; omega
      · rcases hi.2.2.1 hz with ⟨h, h', rest⟩ | ⟨h, h', rest⟩ <;> omega
    have hb := scRunFreq_le (Out.runAt L n).next ((Out.runAt L n).cnt + 1)
      (Out.runAt L n).mn k (Out.runAt L n).prev (by omega) hmn
    simp only [Out.scanFreqUpTo, Out.runAt]
    unfold Out.runStep
    by_cases ha : (Out.runAt L n).cnt + 1 < (Out.runAt L n).mx ∧ (Out.runAt L n).next = L (n + 1)
    · simp only [ite_eq_left ha, Out.runFreq, Nat.add_zero]
      omega
    · simp only [ite_eq_right ha]
      split
      · dsimp only; omega
      · split <;> (dsimp only; omega)

theorem scanFreq_le (L : Nat → Nat) (hL : ∀ i, L i < 65536) (n k : Nat) :
    Out.scanFreqUpTo L n k ≤ n := by
  have := scanFreq_with_pending_le L hL n k
  omega

/-- The two scans' counts fit exactly in a 16-bit frequency cell when their
combined alphabet size is below 65536. No input-length restriction is used. -/
theorem scan_frequency_pair_exact (L D : Nat → Nat)
    (hL : ∀ i, L i < 65536) (hD : ∀ i, D i < 65536) (n m k : Nat) (hsize : n + m < 65536) :
    (UInt16.ofNat (Out.scanFreqUpTo L n k) + UInt16.ofNat (Out.scanFreqUpTo D m k)).toNat =
      Out.scanFreqUpTo L n k + Out.scanFreqUpTo D m k := by
  have h1 := scanFreq_le L hL n k
  have h2 := scanFreq_le D hD m k
  rw [← UInt16.ofNat_add, UInt16.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- The sentinel forces the last pending run to be counted. -/
theorem scan_guard_finishes (L : Nat → Nat) (M : Nat) (h15 : ∀ i ≤ M, L i ≤ 15) :
    (Out.runAt (Out.guarded L M) (M + 1)).cnt = 0 := by
  have hcur : (Out.runAt (Out.guarded L M) M).next ≤ 15 := by
    rw [Out.runAt_next]
    simp only [Out.guarded, ite_eq_right (show M ≠ M + 1 by omega)]
    exact h15 M (Nat.le_refl _)
  have hnx : Out.guarded L M (M + 1) = 65535 := by simp [Out.guarded]
  have hnot : ¬ ((Out.runAt (Out.guarded L M) M).cnt + 1 < (Out.runAt (Out.guarded L M) M).mx ∧
      (Out.runAt (Out.guarded L M) M).next = Out.guarded L M (M + 1)) := by
    rw [hnx]
    omega
  simp only [Out.runAt, Out.runStep, ite_eq_right hnot]
  split
  · rfl
  · split <;> rfl

end Zlib.Trees.Proofs
