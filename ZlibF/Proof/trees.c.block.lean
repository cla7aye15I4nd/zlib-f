import ZlibF.Proof.«trees.c.arrays»
import ZlibF.Proof.«trees.c.reverse»
import ZlibF.Proof.«trees.c.bits»

/-!
# trees.c: `init_block`, `_tr_init`
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-- The loop `for (n = 0; n < M; n++) tree[n].Freq = 0;` over one of the code arrays of the record: after it the
first `M` entries have `Freq = 0` and nothing else changed. `pS` is the translation's pointer to the array. -/
theorem zero_freq_loop {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d) (s : Sel)
    (pS : M CtDataPtr) (hp : ∀ h' : Heap, h'.dstates id ≠ none → pS h' = .ok (.ref (s.ref id) 0, h'))
    (M0 : Int32) (hM0 : M0.toInt ≤ (s.arr d).size) (hM1 : 0 ≤ M0.toInt) (hMb : M0.toInt ≤ 1000) :
    Wp (cfor (σ := Int32) (fun n => pure (decide (n.toInt < M0.toInt))) (fun n => iadd n 1)
        (fun n => do setFc (← pS) n.toInt 0; pure n) 0) h
      (fun _ h' => ∃ a, h' = setD h id (s.upd d a) ∧ a.size = (s.arr d).size ∧
        ∀ j, j < a.size → a[j]! = if j < M0.toInt.toNat then { (s.arr d)[j]! with fc := 0 } else (s.arr d)[j]!) := by
  unfold cfor
  refine Wp.cwhile (fun n h' => 0 ≤ n.toInt ∧ n.toInt ≤ M0.toInt ∧ ∃ a, h' = setD h id (s.upd d a) ∧
      a.size = (s.arr d).size ∧ ∀ j, j < a.size →
        a[j]! = if j < n.toInt.toNat then { (s.arr d)[j]! with fc := 0 } else (s.arr d)[j]!)
    (fun n => (M0.toInt - n.toInt).toNat) _ ?_ ?_ ?_
  · rintro n h' ⟨hn0, hn1, a, rfl, hsz, hj⟩
    have hd' : (setD h id (s.upd d a)).dstates id = some (s.upd d a) := setD_dstates_same _ _ _
    have hne : (setD h id (s.upd d a)).dstates id ≠ none := by simp
    by_cases hlt : n.toInt < M0.toInt
    · right
      have hn' : n.toInt.toNat < a.size := by omega
      have hi' : n.toInt.toNat < (s.arr (s.upd d a)).size := by rw [Sel.arr_upd]; exact hn'
      have hset := setFc_sel hd' s hi' 0
      rw [Sel.arr_upd] at hset
      have hadd := iadd_eq (a := n) (b := 1) (by rw [i32_one_toInt]; omega) (by rw [i32_one_toInt]; omega)
      have hcast : ((n.toInt.toNat : Nat) : Int) = n.toInt := by omega
      have hnn : (Int32.ofInt (n.toInt + 1)).toInt = n.toInt + 1 := i32_ofInt_toInt (by omega) (by omega)
      refine ⟨n, setD h id (s.upd d a), Int32.ofInt (n.toInt + 1),
        setD h id (s.upd d (a.set! n.toInt.toNat { a[n.toInt.toNat]! with fc := 0 })), ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · simp [hlt]
      · rw [hcast] at hset
        simp only [bind_app, hp _ hne, hset, pure_app, Sel.arr_upd, Sel.upd_upd, setD_setD]
        simp only [hadd, i32_one_toInt, pure_app]
      · rw [hnn]; omega
      · rw [hnn]; omega
      · refine ⟨_, rfl, by simp [hsz], ?_⟩
        intro j hj'
        simp only [Array.size_set!] at hj'
        rw [hnn]
        have e1 : (n.toInt + 1).toNat = n.toInt.toNat + 1 := by omega
        rw [e1]
        rw [getElem!_set!]
        by_cases hjn : n.toInt.toNat = j
        · subst hjn
          simp only [hn', and_self, ite_true]
          rw [hj _ hn']
          simp
        · have h1 : ¬ (n.toInt.toNat = j ∧ n.toInt.toNat < a.size) := fun h => hjn h.1
          simp only [h1, ite_false]
          rw [hj j (by simpa using hj')]
          have : (j < n.toInt.toNat + 1) ↔ (j < n.toInt.toNat) := by omega
          simp only [this]
      · rw [hnn]; omega
    · left
      have hnM : n.toInt = M0.toInt := by omega
      refine ⟨n, setD h id (s.upd d a), by simp [hlt], ⟨a, rfl, hsz, ?_⟩⟩
      rw [hnM] at hj
      exact hj
  · have h0 : (0 : Int32).toInt = 0 := by decide
    refine ⟨by rw [h0]; exact Int.le_refl 0, by rw [h0]; exact hM1, s.arr d, ?_, rfl, ?_⟩
    · rw [Sel.upd_arr, setD_self hd]
    · intro j hj'
      simp [h0]
  · show (M0.toInt - (0 : Int32).toInt).toNat < fuel
    have h0 : (0 : Int32).toInt = 0 := by decide
    rw [h0]; unfold fuel; omega


theorem L_CODES_toInt : L_CODES.toInt = 286 := by decide
theorem D_CODES_toInt : D_CODES.toInt = 30 := by decide
theorem BL_CODES_toInt : BL_CODES.toInt = 19 := by decide
theorem END_BLOCK_toInt : END_BLOCK.toInt = 256 := by decide

/-- The deflate record after `init_block`, given the three code arrays. -/
def ibRec (d : DeflateState) (a1 a2 a3 : Array CtData) : DeflateState :=
  { d with dyn_ltree := a1, dyn_dtree := a2, bl_tree := a3, opt_len := 0, static_len := 0, «matches» := 0, sym_next := 0 }

theorem init_block_inv {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hr : TreesRun0 id d) (a1 a2 a3 : Array CtData) (s1 : a1.size = 573)
    (s2 : a2.size = 61) (s3 : a3.size = 39) :
    TreesInvAt (setD h id (ibRec d a1 a2 a3)) id (ibRec d a1 a2 a3) b buf := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hb.wf
  refine ⟨hb.stepD _ ⟨s1, s2, s3, w4, w5, w6⟩ rfl rfl rfl rfl rfl hb.pending_le, ?_⟩
  exact ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, hr.bi_lo, hr.bi_hi, hr.bi_buf,
    by show (0 : UInt32).toNat ≤ d.sym_end.toNat; simp, by show (0 : UInt32).toNat % 3 = 0; simp⟩

/-- **`init_block`, safety and specification.** Zeroes the frequencies of the three code arrays
(`dyn_ltree[0 .. 286)`, `dyn_dtree[0 .. 30)`, `bl_tree[0 .. 19)`), sets `dyn_ltree[END_BLOCK].Freq = 1`,
`opt_len = static_len = 0`, `sym_next = matches = 0`. Nothing else changes (not the `Len` halves, not the bit
buffer, not `pending`). Precondition: `TreesBase` and the descriptor and bit-buffer part of `TreesRun`
(`init_block` does not read `sym_next`). The result is again `TreesInvAt`. -/
theorem init_block_spec0 {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hr : TreesRun0 id d) :
    ∃ a1 a2 a3 d', init_block (some (.tab id)) h = .ok ((), setD h id d') ∧
      TreesInvAt (setD h id d') id d' b buf ∧
      d' = ibRec d a1 a2 a3 ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧
      (∀ n : Nat, n < 286 → n ≠ 256 → (a1[n]!).fc = 0) ∧ (a1[256]!).fc = 1 ∧
      (∀ n : Nat, n < 30 → (a2[n]!).fc = 0) ∧ (∀ n : Nat, n < 19 → (a3[n]!).fc = 0) ∧
      (∀ n : Nat, (a1[n]! : CtData).dl = (d.dyn_ltree[n]! : CtData).dl) ∧ (∀ n : Nat, (a2[n]!).dl = (d.dyn_dtree[n]!).dl) ∧
      (∀ n : Nat, (a3[n]!).dl = (d.bl_tree[n]!).dl) := by
  have hd := hb.dstate
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hb.wf
  have hpL : ∀ h' : Heap, h'.dstates id ≠ none → pLtree (some (.tab id)) h' = .ok (.ref (Sel.l.ref id) 0, h') :=
    fun h' hne => by
      obtain ⟨dd, hdd⟩ := Option.ne_none_iff_exists'.mp hne
      exact pLtree_run hdd
  have hpD : ∀ h' : Heap, h'.dstates id ≠ none → pDtree (some (.tab id)) h' = .ok (.ref (Sel.d.ref id) 0, h') :=
    fun h' hne => by
      obtain ⟨dd, hdd⟩ := Option.ne_none_iff_exists'.mp hne
      exact pDtree_run hdd
  have hpB : ∀ h' : Heap, h'.dstates id ≠ none → pBltree (some (.tab id)) h' = .ok (.ref (Sel.bl.ref id) 0, h') :=
    fun h' hne => by
      obtain ⟨dd, hdd⟩ := Option.ne_none_iff_exists'.mp hne
      exact pBltree_run hdd
  obtain ⟨_, h1, e1, a1, rfl, hs1, hel1⟩ := zero_freq_loop hd .l _ hpL L_CODES
    (by rw [L_CODES_toInt]; show (286 : Int) ≤ d.dyn_ltree.size; omega) (by rw [L_CODES_toInt]; omega)
    (by rw [L_CODES_toInt]; omega)
  have hd1 : (setD h id (Sel.l.upd d a1)).dstates id = some (Sel.l.upd d a1) := setD_dstates_same _ _ _
  obtain ⟨_, h2, e2, a2, rfl, hs2, hel2⟩ := zero_freq_loop hd1 .d _ hpD D_CODES
    (by rw [D_CODES_toInt]; show (30 : Int) ≤ d.dyn_dtree.size; omega) (by rw [D_CODES_toInt]; omega)
    (by rw [D_CODES_toInt]; omega)
  have hd2 : (setD (setD h id (Sel.l.upd d a1)) id (Sel.d.upd (Sel.l.upd d a1) a2)).dstates id
      = some (Sel.d.upd (Sel.l.upd d a1) a2) := setD_dstates_same _ _ _
  obtain ⟨_, h3, e3, a3, rfl, hs3, hel3⟩ := zero_freq_loop hd2 .bl _ hpB BL_CODES
    (by rw [BL_CODES_toInt]; show (19 : Int) ≤ d.bl_tree.size; omega) (by rw [BL_CODES_toInt]; omega)
    (by rw [BL_CODES_toInt]; omega)
  have hd3 : (setD (setD (setD h id (Sel.l.upd d a1)) id (Sel.d.upd (Sel.l.upd d a1) a2)) id
      (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3)).dstates id
      = some (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3) := setD_dstates_same _ _ _
  unfold init_block
  rw [bind_app, e1]
  simp only []
  rw [bind_app, e2]
  simp only []
  rw [bind_app, e3]
  simp only []
  have sz1 : a1.size = 573 := by rw [hs1]; exact w1
  have sz2 : a2.size = 61 := by rw [hs2]; exact w2
  have sz3 : a3.size = 39 := by rw [hs3]; exact w3
  have hE : END_BLOCK.toInt = ((256 : Nat) : Int) := by rw [END_BLOCK_toInt]; rfl
  have hi256 : 256 < (Sel.l.arr (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3)).size := by
    show 256 < a1.size
    rw [hs1]; show 256 < d.dyn_ltree.size; omega
  have hset : setFc (.ref (CtDataRef.dstate_dyn_ltree id) 0) ((256 : Nat) : Int) 1
      (setD (setD (setD h id (Sel.l.upd d a1)) id (Sel.d.upd (Sel.l.upd d a1) a2)) id
        (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3)) = _ := setFc_sel hd3 .l hi256 1
  rw [bind_app, pLtree_run hd3]
  simp only []
  rw [bind_app, hE, hset]
  simp (disch := simp) only [bind_app, md_run', rdD_setD_same, setD_setD, pure_app]
  have ha1 : Sel.l.arr (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3) = a1 := rfl
  have hdl1 : ∀ n : Nat, (a1[n]! : CtData).dl = (d.dyn_ltree[n]! : CtData).dl := by
    intro n
    by_cases hn : n < a1.size
    · rw [hel1 n hn]; split <;> rfl
    · rw [getElem!_ge a1 n (by omega), getElem!_ge d.dyn_ltree n (by omega)]
  have hdl2 : ∀ n : Nat, (a2[n]! : CtData).dl = (d.dyn_dtree[n]! : CtData).dl := by
    intro n
    by_cases hn : n < a2.size
    · rw [hel2 n hn]; split <;> simp [Sel.arr, Sel.upd]
    · rw [getElem!_ge a2 n (by omega), getElem!_ge d.dyn_dtree n (by omega)]
  have hdl3 : ∀ n : Nat, (a3[n]! : CtData).dl = (d.bl_tree[n]! : CtData).dl := by
    intro n
    by_cases hn : n < a3.size
    · rw [hel3 n hn]; split <;> simp [Sel.arr, Sel.upd]
    · rw [getElem!_ge a3 n (by omega), getElem!_ge d.bl_tree n (by omega)]
  refine ⟨(Sel.l.arr (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3)).set! 256
      { (Sel.l.arr (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3))[256]! with fc := 1 }, a2, a3, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · suffices H : ∀ D : DeflateState, D = ibRec d ((Sel.l.arr (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3)).set! 256 { (Sel.l.arr (Sel.bl.upd (Sel.d.upd (Sel.l.upd d a1) a2) a3))[256]! with fc := 1 }) a2 a3 → TreesInvAt (setD h id D) id D b buf from
      H _ (by simp only [Sel.upd, Sel.arr, ibRec])
    intro D hD
    subst hD
    exact init_block_inv hb hr _ a2 a3 (by rw [Array.size_set!]; rw [ha1]; exact sz1) sz2 sz3
  · simp only [Sel.upd, Sel.arr, ibRec]
  · rw [ha1]; simp [sz1]
  · exact sz2
  · exact sz3
  · intro n hn hne
    rw [ha1, getElem!_set!]
    have h1 : ¬ (256 = n ∧ 256 < a1.size) := fun h => hne h.1.symm
    simp only [h1, ite_false]
    rw [hel1 n (by omega)]
    simp [L_CODES_toInt, hn]
  · rw [ha1, getElem!_set!]
    simp [sz1]
  · intro n hn
    rw [hel2 n (by omega)]
    simp [Sel.arr, Sel.upd, D_CODES_toInt, hn]
  · intro n hn
    rw [hel3 n (by omega)]
    simp [Sel.arr, Sel.upd, BL_CODES_toInt, hn]
  · intro n
    rw [ha1, getElem!_set!]
    by_cases hn : 256 = n
    · subst hn
      have h256 : 256 < a1.size := by omega
      simp only [h256, and_self, ite_true]
      exact hdl1 256
    · have h1 : ¬ (256 = n ∧ 256 < a1.size) := fun h => hn h.1
      simp only [h1, ite_false]; exact hdl1 n
  · exact hdl2
  · exact hdl3


/-- `init_block_spec0` for a state that satisfies the whole invariant. -/
theorem init_block_spec {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) :
    ∃ a1 a2 a3 d', init_block (some (.tab id)) h = .ok ((), setD h id d') ∧
      TreesInvAt (setD h id d') id d' b buf ∧ d' = ibRec d a1 a2 a3 ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 := by
  obtain ⟨a1, a2, a3, d', e, hi, hd, s1, s2, s3, -⟩ := init_block_spec0 hI.base hI.run.to0
  exact ⟨a1, a2, a3, d', e, hi, hd, s1, s2, s3⟩


/-- The record after the stores of `_tr_init` that precede `init_block`. -/
def trInitRec (id : Nat) (d : DeflateState) : DeflateState :=
  { d with
    l_desc := { d.l_desc with dyn_tree := .ref (.dstate_dyn_ltree id) 0, stat_desc := some .st_static_l_desc },
    d_desc := { d.d_desc with dyn_tree := .ref (.dstate_dyn_dtree id) 0, stat_desc := some .st_static_d_desc },
    bl_desc := { d.bl_desc with dyn_tree := .ref (.dstate_bl_tree id) 0, stat_desc := some .st_static_bl_desc },
    bi_buf := 0, bi_valid := 0, bi_used := 0 }

theorem trInitRec_inv {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) :
    TreesBase (setD h id (trInitRec id d)) id (trInitRec id d) b buf ∧ TreesRun0 id (trInitRec id d) := by
  refine ⟨hb.stepD _ hb.wf rfl rfl rfl rfl rfl hb.pending_le, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> simp [trInitRec]

/-- **`_tr_init`, safety and specification.** `_tr_init(s)` points the three tree descriptors at the arrays of the
record and at the static descriptors, empties the bit buffer (`bi_buf = bi_valid = bi_used = 0`) and calls
`init_block`. Precondition: `TreesBase` only (what `deflateInit2_` establishes before it calls `deflateReset`, which
reaches `_tr_init` through `deflateResetKeep`); the result satisfies the whole invariant `TreesInvAt`. `pending`,
`pending_buf` and the byte block are unchanged. -/
theorem tr_init_spec {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) :
    ∃ a1 a2 a3 d', «_tr_init» (some (.tab id)) h = .ok ((), setD h id d') ∧
      TreesInvAt (setD h id d') id d' b buf ∧ d' = ibRec (trInitRec id d) a1 a2 a3 ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 := by
  obtain ⟨hb6, hr6⟩ := trInitRec_inv hb
  obtain ⟨a1, a2, a3, d', e, hi, hd, s1, s2, s3, -⟩ := init_block_spec0 hb6 hr6
  simp only [setD_setD] at e hi
  refine ⟨a1, a2, a3, d', ?_, hi, hd, s1, s2, s3⟩
  have hne : h.dstates id ≠ none := by simp [hb.dstate]
  have hrd : rdD h id = d := by simp [rdD, hb.dstate]
  unfold «_tr_init»
  simp (disch := simp [hb.dstate]) only [tr_static_init, bind_app, pure_app, sid_run hb.dstate, md_run', rdD_setD_same, setD_setD, hrd]
  exact e

end Zlib.Trees.Proofs.Out
