import ZlibF.Proof.«trees.c.align»

/-!
# trees.c: `_tr_tally`
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-- One `s->sym_buf[s->sym_next++] = v` of `_tr_tally`. -/
theorem sym_put_run {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hlt : d.lit_bufsize.toNat + d.sym_next.toNat < buf.size) (v : UInt8)
    (hsn : d.sym_next.toNat < 2 ^ 31) :
    (do let d ← rd (some (.tab id))
        setAt d.sym_buf d.sym_next.toNat v
        md (some (.tab id)) fun d => { d with sym_next := d.sym_next + 1 } : M Unit) h =
      .ok ((), setD (setB h b (buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) v)) id
        { d with sym_next := d.sym_next + 1 }) := by
  have hg : Space.get h (BRef.blk b) = some buf := hb.bytes
  have e1 := Ptr.add_nat_ok (off := d.lit_bufsize.toNat) (n := d.sym_next.toNat) hg (by omega)
  have e2 := Ptr.store_ok (v := v) (off := d.lit_bufsize.toNat + d.sym_next.toNat) hg hb.rw hlt
  unfold OkOn at e1
  unfold setAt
  rw [bind_app, rd_run hb.dstate]
  simp only [hb.sym]
  rw [bind_app, bind_app, e1]
  simp only []
  rw [e2]
  simp only []
  have hd : (Space.put h (BRef.blk b) (buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) v)).dstates id = some d :=
    hb.dstate
  rw [md_run hd]
  simp [setD, Space.put, setB]
  rw [hb.sym]


theorem length_code_le (i : Nat) (hi : i < 256) : (length_code_tab[i]'(by rw [length_code_tab_size]; exact hi)).toNat ≤ 28 := by
  have : ∀ j : Fin 256, (length_code_tab[j.val]'(by rw [length_code_tab_size]; exact j.isLt)).toNat ≤ 28 := by
    decide +kernel
  exact this ⟨i, hi⟩

theorem dist_code_le (i : Nat) (hi : i < 512) : (dist_code_tab[i]'(by rw [dist_code_tab_size]; exact hi)).toNat ≤ 29 := by
  have : ∀ j : Fin 512, (dist_code_tab[j.val]'(by rw [dist_code_tab_size]; exact j.isLt)).toNat ≤ 29 := by
    decide +kernel
  exact this ⟨i, hi⟩

theorem arr_get_bang (a : Array UInt8) (i : Nat) (hi : i < a.size) : a[i]! = a[i] := getElem!_pos a i hi

/-- `d_code(dist)` as a number (`dist` here is `dist - 1` of the symbol). -/
def dcodeN (d : Nat) : Nat := if d < 256 then (dist_code_tab[d]!).toNat else (dist_code_tab[256 + d / 128]!).toNat

/-- `d_code` reads `_dist_code` inside its bounds for `dist < 32768`; the code is at most 29. -/
theorem d_code_run {h : Heap} (hs : TreesStatic h.static) (dist : UInt32) (hd : dist.toNat < 32768) :
    ∃ c : UInt8, d_code dist h = .ok (c, h) ∧ c.toNat = dcodeN dist.toNat ∧ c.toNat ≤ 29 := by
  have hg : Space.get h BRef.st_dist_code = some dist_code_tab := by simp [Space.get, hs.dist_code]
  unfold d_code
  by_cases h1 : dist < 256
  · have h2 : dist.toNat < 256 := by simpa [UInt32.lt_iff_toNat_lt] using h1
    have hi : dist.toNat < dist_code_tab.size := by rw [dist_code_tab_size]; omega
    have e := Ptr.index_ok (off := 0) (i := dist.toNat) hg (by omega)
    unfold OkOn at e
    simp only [h1, ite_true]
    refine ⟨_, e, ?_, ?_⟩
    · have := arr_get_bang dist_code_tab dist.toNat hi
      simp only [dcodeN, h2, ite_true, Nat.zero_add]
      exact congrArg UInt8.toNat this.symm
    · exact dist_code_le _ (by omega)
  · have h2 : ¬ dist.toNat < 256 := by simpa [UInt32.lt_iff_toNat_lt] using h1
    have hsh : (dist >>> 7).toNat = dist.toNat / 128 := by
      rw [UInt32.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
    have hidx : ((256 : UInt32) + (dist >>> 7)).toNat = 256 + dist.toNat / 128 := by
      rw [UInt32.toNat_add, hsh]; simp; omega
    have hi : 256 + dist.toNat / 128 < dist_code_tab.size := by rw [dist_code_tab_size]; omega
    have e := Ptr.index_ok (off := 0) (i := 256 + dist.toNat / 128) hg (by omega)
    unfold OkOn at e
    simp only [h1, ite_false]
    refine ⟨_, by rw [hidx, e], ?_, ?_⟩
    · have := arr_get_bang dist_code_tab (256 + dist.toNat / 128) hi
      simp only [dcodeN, h2, ite_false, Nat.zero_add]
      exact congrArg UInt8.toNat this.symm
    · exact dist_code_le _ (by omega)


theorem toNat_add_one_u32 {x : UInt32} (hx : x.toNat + 1 < 2 ^ 32) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]; have : (1 : UInt32).toNat = 1 := by decide
  rw [this]; omega

/-- The three stores of `_tr_tally` into the symbol buffer. -/
theorem tally_puts {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hroom : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) (dist lc : UInt32)
    (rest : Unit → M Int32) :
    ((do
          let d ← rd (some (DeflateStateRef.tab id))
          setAt d.sym_buf (↑d.sym_next.toNat) dist.toUInt8
          md (some (DeflateStateRef.tab id)) fun d => { d with sym_next := d.sym_next + 1 } : M Unit) >>= fun _ =>
      ((do
          let d ← rd (some (DeflateStateRef.tab id))
          setAt d.sym_buf (↑d.sym_next.toNat) (dist >>> 8).toUInt8
          md (some (DeflateStateRef.tab id)) fun d => { d with sym_next := d.sym_next + 1 } : M Unit) >>= fun _ =>
      ((do
          let d ← rd (some (DeflateStateRef.tab id))
          setAt d.sym_buf (↑d.sym_next.toNat) lc.toUInt8
          md (some (DeflateStateRef.tab id)) fun d => { d with sym_next := d.sym_next + 1 } : M Unit) >>= rest))) h =
    rest () (setD (setB h b (((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) lc.toUInt8)) id { d with sym_next := d.sym_next + 1 + 1 + 1 }) := by
  have hl := hb.lit_hi
  have hse := hb.sym_end
  have hs1 := hb.size
  have hsn1 : (d.sym_next + 1).toNat = d.sym_next.toNat + 1 := toNat_add_one_u32 (by omega)
  have hb1 := hb.step (buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8) (by simp)
    { d with sym_next := d.sym_next + 1 } hb.wf rfl rfl rfl rfl rfl hb.pending_le
  have hsn2 : (d.sym_next + 1 + 1).toNat = d.sym_next.toNat + 2 := by rw [toNat_add_one_u32 (by omega), hsn1]
  have hb2 : TreesBase (setD (setB h b ((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
      (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8)) id { d with sym_next := d.sym_next + 1 + 1 })
      id { d with sym_next := d.sym_next + 1 + 1 } b ((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
      (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8) := by
    simpa only [setB_setD, setD_setD, setB_setB] using hb1.step ((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
      (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8) (by simp)
      { d with sym_next := d.sym_next + 1 + 1 } hb.wf rfl rfl rfl rfl rfl hb.pending_le
  rw [bind_app, sym_put_run hb (by omega) _ (by omega)]
  simp only []
  rw [bind_app, sym_put_run hb1 (by simp only [Array.size_set!]; rw [hsn1]; omega) _ (by simp only []; rw [hsn1]; omega)]
  simp only [hsn1, Nat.add_assoc, setB_setD, setD_setD, setB_setB]
  rw [bind_app, sym_put_run hb2 (by simp only [Array.size_set!]; rw [hsn2]; omega) _ (by simp only []; rw [hsn2]; omega)]
  simp only [hsn2, Nat.add_assoc, setB_setD, setD_setD, setB_setB]


/-- The array with `Freq` of entry `i` incremented (`tree[i].Freq++`, modulo 2^16). -/
def bumpFc (a : Array CtData) (i : Nat) : Array CtData := a.set! i { (a[i]!) with fc := (a[i]!).fc + 1 }

/-- The part of `_tr_tally` after the three stores into the symbol buffer. -/
def tallyTail (s : DeflateStatePtr) (dist lc : UInt32) : M Int32 := do
  if dist == 0 then
    let lt ← pLtree s
    setFc lt lc.toNat ((← getFc lt lc.toNat) + 1)
  else
    md s fun d => { d with «matches» := d.«matches» + 1 }
    let dist := dist - 1
    let lcode ← Ptr.index (.ref .st_length_code 0 : BPtr) lc.toNat
    let idx := (u8i lcode).toInt + LITERALS.toInt + 1
    let lt ← pLtree s
    setFc lt idx ((← getFc lt idx) + 1)
    let dc ← d_code dist
    let dt ← pDtree s
    setFc dt dc.toNat ((← getFc dt dc.toNat) + 1)
  let d ← rd s
  return (if d.sym_next == d.sym_end then 1 else 0)

theorem tally_split (s : DeflateStatePtr) (dist lc : UInt32) :
    «_tr_tally» s dist lc = ((do
          let d ← rd s
          setAt d.sym_buf (↑d.sym_next.toNat) dist.toUInt8
          md s fun d => { d with sym_next := d.sym_next + 1 } : M Unit) >>= fun _ =>
      ((do
          let d ← rd s
          setAt d.sym_buf (↑d.sym_next.toNat) (dist >>> 8).toUInt8
          md s fun d => { d with sym_next := d.sym_next + 1 } : M Unit) >>= fun _ =>
      ((do
          let d ← rd s
          setAt d.sym_buf (↑d.sym_next.toNat) lc.toUInt8
          md s fun d => { d with sym_next := d.sym_next + 1 } : M Unit) >>= fun _ => tallyTail s dist lc))) := rfl

theorem tallyTail_lit {H : Heap} {id : Nat} {D : DeflateState} (hd : H.dstates id = some D) (dist lc : UInt32)
    (hdist : dist = 0) (hlc : lc.toNat < D.dyn_ltree.size) :
    tallyTail (some (.tab id)) dist lc H =
      .ok ((if D.sym_next == D.sym_end then 1 else 0),
        setD H id { D with dyn_ltree := bumpFc D.dyn_ltree lc.toNat }) := by
  subst hdist
  have hg : getFc (.ref (Sel.l.ref id) 0) ((lc.toNat : Nat) : Int) H = .ok ((D.dyn_ltree[lc.toNat]!).fc, H) :=
    getFc_sel hd .l hlc
  have hs := setFc_sel hd .l (i := lc.toNat) hlc ((D.dyn_ltree[lc.toNat]!).fc + 1)
  unfold tallyTail
  simp only [beq_self_eq_true, ite_true]
  rw [bind_app, pLtree_run hd]
  simp only []
  rw [bind_app]
  have hg' : getFc (.ref (CtDataRef.dstate_dyn_ltree id) 0) ((lc.toNat : Nat) : Int) H = _ := hg
  rw [hg']
  simp only []
  have hs' : setFc (.ref (CtDataRef.dstate_dyn_ltree id) 0) ((lc.toNat : Nat) : Int) ((D.dyn_ltree[lc.toNat]!).fc + 1) H = _ := hs
  rw [bind_app, hs']
  simp only []
  simp (disch := simp [hd]) only [bind_app, rd_run', rdD_setD_same, pure_app]
  simp only [Sel.upd, Sel.arr, bumpFc]
  rfl


theorem LITERALS_toInt : LITERALS.toInt = 256 := by decide

theorem u8i_toInt (x : UInt8) : (u8i x).toInt = x.toNat := by
  unfold u8i
  have := x.toNat_lt
  exact i32_ofInt_toInt (by omega) (by omega)

/-- The record after the counting part of a match symbol. -/
def tallyMatchRec (D : DeflateState) (dist lc : UInt32) : DeflateState :=
  { D with «matches» := D.«matches» + 1, dyn_ltree := bumpFc D.dyn_ltree ((length_code_tab[lc.toNat]!).toNat + 257), dyn_dtree := bumpFc D.dyn_dtree (dcodeN (dist.toNat - 1)) }

theorem idx_cast (x : UInt8) : (u8i x).toInt + LITERALS.toInt + 1 = (((x.toNat + 257 : Nat)) : Int) := by
  rw [u8i_toInt, LITERALS_toInt]; omega

theorem tallyTail_match {H : Heap} {id : Nat} {D : DeflateState} (hd : H.dstates id = some D)
    (hs : TreesStatic H.static) (hwf : D.WellFormed) (dist lc : UInt32)
    (hdist : (dist == 0) = false) (hlc : lc.toNat < 256) (hd32 : dist.toNat ≤ 32768) :
    tallyTail (some (.tab id)) dist lc H =
      .ok ((if D.sym_next == D.sym_end then 1 else 0), setD H id (tallyMatchRec D dist lc)) := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hwf
  have hd0 : dist ≠ 0 := by
    intro h0; subst h0; simp at hdist
  have hd1 : (dist - 1).toNat = dist.toNat - 1 := by
    have : 1 ≤ dist.toNat := by
      rcases Nat.eq_zero_or_pos dist.toNat with h0 | h0
      · exact absurd (UInt32.toNat_inj.mp (by simpa using h0)) hd0
      · exact h0
    rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le]; omega)]
    simp
  have hsL : (setD H id { D with «matches» := D.«matches» + 1 }).dstates id = some { D with «matches» := D.«matches» + 1 } :=
    setD_dstates_same _ _ _
  have hsS : TreesStatic (setD H id { D with «matches» := D.«matches» + 1 }).static := by simpa using hs
  have hlg : Space.get (setD H id { D with «matches» := D.«matches» + 1 }) BRef.st_length_code = some length_code_tab := by
    simp [Space.get, hs.length_code]
  have hil : lc.toNat < length_code_tab.size := by rw [length_code_tab_size]; omega
  have eL := Ptr.index_ok (off := 0) (i := lc.toNat) hlg (by omega)
  unfold OkOn at eL
  have eL' : Ptr.index (.ref .st_length_code 0 : BPtr) (lc.toNat : Int) (setD H id { D with «matches» := D.«matches» + 1 })
      = .ok (length_code_tab[lc.toNat]!, setD H id { D with «matches» := D.«matches» + 1 }) := by
    rw [eL]; simp only [Nat.zero_add]; rw [arr_get_bang length_code_tab lc.toNat hil]
  have hlc28 : (length_code_tab[lc.toNat]!).toNat ≤ 28 := by
    rw [arr_get_bang length_code_tab lc.toNat hil]; exact length_code_le _ hlc
  unfold tallyTail
  simp only [hdist, Bool.false_eq_true, ite_false]
  rw [bind_app, md_run hd]
  simp only []
  rw [bind_app, eL']
  simp only []
  have hD1w : ({ D with «matches» := D.«matches» + 1 } : DeflateState).dyn_ltree.size = 573 := w1
  have hD1w2 : ({ D with «matches» := D.«matches» + 1 } : DeflateState).dyn_dtree.size = 61 := w2
  generalize hD1 : ({ D with «matches» := D.«matches» + 1 } : DeflateState) = D1 at *
  rw [bind_app, pLtree_run hsL]
  simp only [idx_cast]
  have hi1 : (length_code_tab[lc.toNat]!).toNat + 257 < (Sel.l.arr D1).size := by
    show _ < D1.dyn_ltree.size; omega
  rw [bind_app]
  have g1 : getFc (.ref (CtDataRef.dstate_dyn_ltree id) 0) ((((length_code_tab[lc.toNat]!).toNat + 257 : Nat)) : Int)
      (setD H id D1) = _ := getFc_sel hsL .l hi1
  rw [g1]
  simp only []
  have s1 : setFc (.ref (CtDataRef.dstate_dyn_ltree id) 0) ((((length_code_tab[lc.toNat]!).toNat + 257 : Nat)) : Int)
      ((Sel.l.arr D1)[(length_code_tab[lc.toNat]!).toNat + 257]!.fc + 1) (setD H id D1) = _ :=
    setFc_sel hsL .l hi1 _
  rw [bind_app, s1]
  simp only [setD_setD]
  have hsz2 : (Sel.l.upd D1 ((Sel.l.arr D1).set! ((length_code_tab[lc.toNat]!).toNat + 257)
      { (Sel.l.arr D1)[(length_code_tab[lc.toNat]!).toNat + 257]! with fc := (Sel.l.arr D1)[(length_code_tab[lc.toNat]!).toNat + 257]!.fc + 1 })).dyn_dtree.size = 61 := hD1w2
  generalize hD2 : Sel.l.upd D1 ((Sel.l.arr D1).set! ((length_code_tab[lc.toNat]!).toNat + 257)
      { (Sel.l.arr D1)[(length_code_tab[lc.toNat]!).toNat + 257]! with fc := (Sel.l.arr D1)[(length_code_tab[lc.toNat]!).toNat + 257]!.fc + 1 }) = D2 at *
  have hsD : (setD H id D2).dstates id = some D2 := setD_dstates_same _ _ _
  obtain ⟨c, hcr, hcn, hc29⟩ := d_code_run (h := setD H id D2) (by simpa using hs) (dist - 1) (by omega)
  rw [bind_app, hcr]
  simp only []
  rw [bind_app, pDtree_run hsD]
  simp only []
  have hi2 : c.toNat < (Sel.d.arr D2).size := by show _ < D2.dyn_dtree.size; omega
  have g2 : getFc (.ref (CtDataRef.dstate_dyn_dtree id) 0) ((c.toNat : Nat) : Int) (setD H id D2) = _ := getFc_sel hsD .d hi2
  rw [bind_app, g2]
  simp only []
  have s2 : setFc (.ref (CtDataRef.dstate_dyn_dtree id) 0) ((c.toNat : Nat) : Int)
      ((Sel.d.arr D2)[c.toNat]!.fc + 1) (setD H id D2) = _ := setFc_sel hsD .d hi2 _
  rw [bind_app, s2]
  simp only [setD_setD]
  simp (disch := simp) only [bind_app, rd_run', rdD_setD_same, pure_app]
  rw [hcn, hd1]
  subst hD2
  subst hD1
  unfold tallyMatchRec bumpFc
  simp only [Sel.upd, Sel.arr]
  rfl


@[simp] theorem bumpFc_size (a : Array CtData) (i : Nat) : (bumpFc a i).size = a.size := by
  simp [bumpFc]

/-- The record after `_tr_tally`. -/
def tallyRec (d : DeflateState) (dist lc : UInt32) : DeflateState :=
  if dist = 0 then { d with sym_next := d.sym_next + 1 + 1 + 1, dyn_ltree := bumpFc d.dyn_ltree lc.toNat }
  else tallyMatchRec { d with sym_next := d.sym_next + 1 + 1 + 1 } dist lc

theorem tallyRec_wf {d : DeflateState} (hw : d.WellFormed) (dist lc : UInt32) : (tallyRec d dist lc).WellFormed := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hw
  unfold tallyRec tallyMatchRec
  split <;> exact ⟨by simpa using w1, by simpa using w2, w3, w4, w5, w6⟩

theorem tallyRec_fields (d : DeflateState) (dist lc : UInt32) :
    (tallyRec d dist lc).pending_buf = d.pending_buf ∧ (tallyRec d dist lc).pending_buf_size = d.pending_buf_size ∧
    (tallyRec d dist lc).sym_buf = d.sym_buf ∧ (tallyRec d dist lc).lit_bufsize = d.lit_bufsize ∧
    (tallyRec d dist lc).sym_end = d.sym_end ∧ (tallyRec d dist lc).pending = d.pending := by
  unfold tallyRec tallyMatchRec
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tallyRec_run {id : Nat} {d : DeflateState} (hr : TreesRun id d) (hroom : d.sym_next.toNat + 3 ≤ d.sym_end.toNat)
    (hm : d.sym_next.toNat % 3 = 0) (hsn : d.sym_next.toNat + 3 < 2 ^ 32) (dist lc : UInt32) :
    TreesRun id (tallyRec d dist lc) := by
  have e : (d.sym_next + 1 + 1 + 1).toNat = d.sym_next.toNat + 3 := by
    have e1 : (d.sym_next + 1).toNat = d.sym_next.toNat + 1 := toNat_add_one_u32 (by omega)
    have e2 : (d.sym_next + 1 + 1).toNat = d.sym_next.toNat + 2 := by
      rw [toNat_add_one_u32 (by rw [e1]; omega), e1]
    rw [toNat_add_one_u32 (by rw [e2]; omega), e2]
  unfold tallyRec tallyMatchRec
  split
  · exact ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, hr.bi_lo, hr.bi_hi, hr.bi_buf,
      by show (d.sym_next + 1 + 1 + 1).toNat ≤ d.sym_end.toNat; omega,
      by show (d.sym_next + 1 + 1 + 1).toNat % 3 = 0; omega⟩
  · exact ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, hr.bi_lo, hr.bi_hi, hr.bi_buf,
      by show (d.sym_next + 1 + 1 + 1).toNat ≤ d.sym_end.toNat; omega,
      by show (d.sym_next + 1 + 1 + 1).toNat % 3 = 0; omega⟩


/-- **`_tr_tally`, safety and specification.** `_tr_tally(s, dist, lc)` stores the symbol `(dist, lc)` as 3 bytes at
`sym_buf[sym_next ..]` (`dist` little-endian, then `lc`), counts it in `dyn_ltree` (a literal: `dyn_ltree[lc].Freq++`;
a match: `matches++`, `dyn_ltree[_length_code[lc] + 257].Freq++`, `dyn_dtree[d_code(dist - 1)].Freq++`) and returns
whether the symbol buffer is now full (`sym_next == sym_end`), which is when `deflate.c` flushes the block.
Preconditions: `TreesInvAt`; `sym_next + 3 <= sym_end` (deflate.c flushes the block as soon as `sym_next == sym_end`,
so a tally always starts below it); a literal has `lc < 256` (`lc` is a byte); a match has `lc < 256` (length minus
`MIN_MATCH`, at most 255) and `1 <= dist <= 32768` (`MAX_DIST` is at most 32506). Nothing else of the record changes;
the byte block changes only at the three symbol bytes. -/
theorem tr_tally_spec {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (dist lc : UInt32)
    (hroom : d.sym_next.toNat + 3 ≤ d.sym_end.toNat)
    (hlit : dist = 0 → lc.toNat < 256) (hmatch : dist ≠ 0 → lc.toNat < 256 ∧ dist.toNat ≤ 32768) :
    ∃ buf' r, «_tr_tally» (some (.tab id)) dist lc h = .ok (r, setD (setB h b buf') id (tallyRec d dist lc)) ∧
      TreesInvAt (setD (setB h b buf') id (tallyRec d dist lc)) id (tallyRec d dist lc) b buf' ∧
      r = (if d.sym_next + 1 + 1 + 1 == d.sym_end then 1 else 0) ∧
      buf'.size = buf.size ∧
      buf'.getD (d.lit_bufsize.toNat + d.sym_next.toNat) 0 = dist.toUInt8 ∧
      buf'.getD (d.lit_bufsize.toNat + d.sym_next.toNat + 1) 0 = (dist >>> 8).toUInt8 ∧
      buf'.getD (d.lit_bufsize.toNat + d.sym_next.toNat + 2) 0 = lc.toUInt8 ∧
      (∀ i, (i < d.lit_bufsize.toNat + d.sym_next.toNat ∨ d.lit_bufsize.toNat + d.sym_next.toNat + 3 ≤ i) →
        buf'.getD i 0 = buf.getD i 0) := by
  obtain ⟨hb, hr⟩ := hI
  have hl := hb.lit_hi
  have hse := hb.sym_end
  have hs1 := hb.size
  have hm := hr.sym_next_mod
  have hsn : d.sym_next.toNat + 3 < 2 ^ 32 := by omega
  have e1 : (d.sym_next + 1).toNat = d.sym_next.toNat + 1 := toNat_add_one_u32 (by omega)
  have e2 : (d.sym_next + 1 + 1).toNat = d.sym_next.toNat + 2 := by
    rw [toNat_add_one_u32 (by rw [e1]; omega), e1]
  have e3 : (d.sym_next + 1 + 1 + 1).toNat = d.sym_next.toNat + 3 := by
    rw [toNat_add_one_u32 (by rw [e2]; omega), e2]
  set_option maxRecDepth 4000 in
  have hbuf3 : ((((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) lc.toUInt8)).size = buf.size := by simp
  have hb3 : TreesBase (setD (setB h b ((((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) lc.toUInt8))) id { d with sym_next := d.sym_next + 1 + 1 + 1 })
      id { d with sym_next := d.sym_next + 1 + 1 + 1 } b ((((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) lc.toUInt8)) :=
    hb.step _ hbuf3 _ hb.wf rfl rfl rfl rfl rfl hb.pending_le
  have hd3 := setD_dstates_same (setB h b ((((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) lc.toUInt8))) id { d with sym_next := d.sym_next + 1 + 1 + 1 }
  have hrun : «_tr_tally» (some (.tab id)) dist lc h =
      .ok ((if d.sym_next + 1 + 1 + 1 == d.sym_end then 1 else 0),
        setD (setB h b ((((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) lc.toUInt8))) id (tallyRec d dist lc)) := by
    rw [tally_split, tally_puts hb hroom dist lc (fun _ => tallyTail (some (.tab id)) dist lc)]
    by_cases hz : dist = 0
    · have hlc := hlit hz
      have hlt : lc.toNat < ({ d with sym_next := d.sym_next + 1 + 1 + 1 } : DeflateState).dyn_ltree.size := by
        show lc.toNat < d.dyn_ltree.size
        have := hb.wf.1; omega
      rw [tallyTail_lit hd3 dist lc hz hlt]
      simp only [tallyRec, hz, ite_true, setD_setD]
    · obtain ⟨hlc, hdd⟩ := hmatch hz
      have hdz : (dist == 0) = false := by simpa using hz
      rw [tallyTail_match hd3 (by simpa using hb.static) hb.wf dist lc hdz hlc hdd]
      simp only [tallyRec, hz, ite_false, setD_setD]
  refine ⟨_, _, hrun, ?_, rfl, hbuf3, ?_, ?_, ?_, ?_⟩
  · obtain ⟨f1, f2, f3, f4, f5, f6⟩ := tallyRec_fields d dist lc
    exact ⟨hb.step _ hbuf3 _ (tallyRec_wf hb.wf dist lc) f1 f2 f3 f4 f5 (by rw [f6, f2]; exact hb.pending_le),
      tallyRec_run hr hroom hm hsn dist lc⟩
  · rw [getD_set_u8, getD_set_u8, getD_set_u8]
    have n1 : ¬ (d.lit_bufsize.toNat + (d.sym_next.toNat + 2) = d.lit_bufsize.toNat + d.sym_next.toNat) := by omega
    have n2 : ¬ (d.lit_bufsize.toNat + (d.sym_next.toNat + 1) = d.lit_bufsize.toNat + d.sym_next.toNat) := by omega
    have n3 : d.lit_bufsize.toNat + d.sym_next.toNat < buf.size := by omega
    simp [n1, n2, n3]
  · rw [getD_set_u8, getD_set_u8, getD_set_u8]
    have n1 : ¬ (d.lit_bufsize.toNat + (d.sym_next.toNat + 2) = d.lit_bufsize.toNat + d.sym_next.toNat + 1) := by omega
    have n3 : d.lit_bufsize.toNat + (d.sym_next.toNat + 1) < buf.size := by omega
    simp [n1, n3, Nat.add_assoc]
  · rw [getD_set_u8, getD_set_u8, getD_set_u8]
    have n3 : d.lit_bufsize.toNat + (d.sym_next.toNat + 2) < buf.size := by omega
    simp [n3, Nat.add_assoc]
  · intro i hi
    have n1 : ¬ (d.lit_bufsize.toNat + (d.sym_next.toNat + 2) = i) := by omega
    have n2 : ¬ (d.lit_bufsize.toNat + (d.sym_next.toNat + 1) = i) := by omega
    have n3 : ¬ (d.lit_bufsize.toNat + d.sym_next.toNat = i) := by omega
    rw [getD_set_u8, getD_set_u8, getD_set_u8]
    simp [n1, n2, n3]

end Zlib.Trees.Proofs.Out
