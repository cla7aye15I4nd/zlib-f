import ZlibF.Spec.InflateFast

/-!
# inffast.c: exact input advancement in the distance and length branches

These proofs retain the single-pull consequence of the existing bit bounds.
No new semantic definition or caller contract is introduced.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

theorem Wp.at_run {α : Type} {m : M α} {h h' : Heap} {a : α}
    {Q : α → Heap → Prop} (hw : Wp m h Q) (hr : m h = .ok (a, h')) : Q a h' := by
  obtain ⟨a1, h1, hr1, hq⟩ := hw
  have he := Except.ok.inj (hr1.symm.trans hr)
  rcases Prod.mk.inj he with ⟨rfl, rfl⟩
  exact hq

variable {e : Env} {c : Ctx}

theorem dodistBase_tight_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hx : l.op.toNat ≤ 13) (hd1 : 1 ≤ l.dist.toNat) (hd2 : l.dist.toNat ≤ 65536)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) (hbroke : l.broke = false)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 5 ≤ l.bits.toNat)) :
    Wp (dodistBase c l) (e.heap A msg m) (fun l' h' =>
      ∃ i' xv rest, i ≤ i' ∧ i' ≤ i + 2 ∧ (5 ≤ l.bits.toNat → i' ≤ i + 1) ∧ readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (xv, rest) ∧
        l'.againD = l.againD ∧
        ((l'.broke = false ∧ LS e l' i' (o + l.len.toNat) ∧ Sg e l'.hold.toNat l'.bits.toNat i' = rest ∧
            h' = e.heap (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o (l.dist.toNat + xv) l.len.toNat A) msg m) ∨
         (l'.broke = true ∧ LS e l' i' o ∧ ∃ p, h' = e.heap A p BAD))) := by
  unfold dodistBase
  by_cases h1 : l.bits < l.op
  · simp only [h1, ite_true]
    have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
    have hl3 := hls.pullL (by omega) hiin
    have hs3 := Sg_pullL hls (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    by_cases h2 : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits <
        (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op
    · simp only [h2, ite_true]
      have h2' : l.bits.toNat + 8 < l.op.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp h2
        simp only [pullL] at this hb3 ⊢
        omega
      have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
      have hb3' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by omega
      refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m)) ?_
      have hl4 := hl3.pullL hb3' hi2
      have hs4 := Sg_pullL hl3 hb3' hi2
      have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0)
        (.ref (BRef.blk e.ib) (i + 1 + 1)) hl3.hb
      refine Wp.mono (distCont_wp hc A msg m _ (i + 1 + 1) o hl4 hA ho hAb (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 hb4 ⊢; omega) (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)) ?_
      intro l' h' hq
      obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
      refine ⟨i + 1 + 1, xv, rest, by omega, by omega, (by intro h; omega), ?_, hagD, ?_⟩
      · simp only [pullL] at hr hs4 hs3 ⊢
        rw [hs4, hs3] at hr
        exact hr
      · simp only [pullL] at hres ⊢
        exact Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres
    · simp only [h2, ite_false]
      have h2n : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op.toNat ≤
          (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat := by
        have : ¬ ((pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat <
            (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op.toNat) :=
          fun h => h2 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (distCont_wp hc A msg m _ (i + 1) o hl3 hA ho hAb (by simp only [pullL]; omega)
        h2n (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)) ?_
      intro l' h' hq
      obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
      refine ⟨i + 1, xv, rest, by omega, by omega, (by intro h; omega), ?_, hagD, ?_⟩
      · simp only [pullL] at hr hs3 ⊢
        rw [hs3] at hr
        exact hr
      · simp only [pullL] at hres ⊢
        exact Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres
  · simp only [h1, ite_false]
    have h1' : l.op.toNat ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
      omega
    refine Wp.mono (distCont_wp hc A msg m l i o hls hA ho hAb hx h1' hd1 hd2 hlen hbroke) ?_
    intro l' h' hq
    obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
    exact ⟨i, xv, rest, by omega, by omega, (by intro h; omega), hr, hagD, Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres⟩


set_option maxHeartbeats 1000000 in
/-- One pass of the block at `dodist:`. Either it follows a link (`againD`), or it ends the distance block. -/
theorem dodist_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o d k : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd k) (hk : k < e.DCA.size)
    (hEb : (e.DCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.DCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : DistClass e (e.DCA.getD k default))
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat + d)) :
    Wp (dodist c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ i + 2 ∧ (20 ≤ l.bits.toNat + d → i' ≤ i + 1) ∧
        l'.in_ = .ref (BRef.blk e.ib) i') := by
  have hkE : e.DCA[k]'hk = e.DCA.getD k default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.DCA.getD k default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_DCA A msg m) hk
  have hEb64 : (((e.DCA.getD k default).bits.toUInt32).toUInt64).toNat = (e.DCA.getD k default).bits.toNat := by
    simp [toNat32]
  have hEbn : ((e.DCA.getD k default).bits.toUInt32).toNat = (e.DCA.getD k default).bits.toNat := toNat32 _
  have hls1 : LS e (dropL l (e.DCA.getD k default).bits.toUInt32) i o :=
    hls.dropL _ (by omega) (by omega)
  have hEb64 : (((e.DCA.getD k default).bits.toUInt32).toUInt64).toNat = (e.DCA.getD k default).bits.toNat := by
    simp [toNat32]
  have hEbn : ((e.DCA.getD k default).bits.toUInt32).toNat = (e.DCA.getD k default).bits.toNat := toNat32 _
  have hls1 : LS e (dropL l (e.DCA.getD k default).bits.toUInt32) i o :=
    hls.dropL _ (by omega) (by omega)
  have hsg1 := Sg_dropL (e := e) l (e.DCA.getD k default).bits.toUInt32 i (by omega) (by omega)
  have hlow64 : ∀ x : UInt32, x.toNat < 32 → (l.hold >>> (e.DCA.getD k default).bits.toUInt32.toUInt64).toNat = l.hold.toNat / 2 ^ (e.DCA.getD k default).bits.toNat := by
    intro x _; rw [u64_shr (by omega), hEbn]
  unfold dodist
  dsimp only
  refine Wp.bindO hld ?_
  refine Wp.bindO (shr64_ok (x := l.hold) (by omega)) ?_
  refine Wp.bindO hld ?_
  generalize e.DCA.getD k default = E at *
  have hsg1' : Sg e (l.hold >>> E.bits.toUInt32.toUInt64).toNat (l.bits - E.bits.toUInt32).toNat i =
      (Sg e l.hold.toNat l.bits.toNat i).drop E.bits.toNat := by
    have := hsg1; rw [hEbn] at this; exact this
  by_cases hb16 : (E.op.toUInt32 &&& 16 != 0) = true
  · simp only [hb16, ite_true]
    have hb16' : E.op &&& 16 ≠ 0 := by
      rw [mask16] at hb16; simpa using hb16
    have hbase : E.op &&& 16 ≠ 0 ∧ ((E.op &&& 15).toNat ≤ 13) ∧ 1 ≤ E.val.toNat := by
      rcases hcl with h | h | h
      · exact h
      · exact absurd h.1 hb16'
      · exact absurd h.1 hb16'
    refine Wp.bindO hld ?_
    have hv : E.val.toUInt32.toNat = E.val.toNat := by simp
    have hv2 := UInt16.toNat_lt E.val
    have hbn := dropL_bits l E.bits.toUInt32 (by omega)
    have key := (dodistBase_tight_wp hc A msg m
      { in_ := l.in_, out := l.out, hold := l.hold >>> E.bits.toUInt32.toUInt64, bits := l.bits - E.bits.toUInt32,
        here := l.here, op := E.op.toUInt32 &&& 15, len := l.len, dist := E.val.toUInt32, from_ := l.from_,
        broke := l.broke, againL := l.againL, againD := false } i o (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb
      (by rw [mask15]; exact hbase.2.1) (by rw [hv]; exact hbase.2.2) (by rw [hv]; omega) hlen hbroke
      (by rcases hpull with h | h
          · exact Or.inl h
          · refine Or.inr ⟨h.1, ?_⟩
            show 5 ≤ (l.bits - E.bits.toUInt32).toNat
            have hbn' : (l.bits - E.bits.toUInt32).toNat = l.bits.toNat - E.bits.toNat := by
              rw [u32_toNat_sub (by omega), hEbn]
            omega))
    unfold dodistBase distCont at key
    dsimp only at key
    refine Wp.mono key ?_
    intro l' h' hq
    obtain ⟨i', xv, rest, hi1, hi2, htight, _, _, hres⟩ := hq
    have hbound : 20 ≤ l.bits.toNat + d → i' ≤ i + 1 := by
      intro hh
      apply htight
      show 5 ≤ (l.bits - E.bits.toUInt32).toNat
      rw [u32_toNat_sub (by omega), hEbn]
      omega
    rcases hres with ⟨_, hls', _, _⟩ | ⟨_, hls', _⟩
    · exact ⟨i', hi1, hi2, hbound, hls'.hin⟩
    · exact ⟨i', hi1, hi2, hbound, hls'.hin⟩
  · -- not a base: a link or an invalid code
    have hb16' : E.op &&& 16 = 0 := by
      rw [mask16] at hb16; simpa using hb16
    by_cases hb64 : (E.op.toUInt32 &&& 64 == 0) = true
    · simp only [hb16, hb64, ite_true, ite_false, Bool.false_eq_true]
      have hb64' : E.op &&& 64 = 0 := by
        rw [mask64] at hb64; simpa using hb64
      have hlink : 1 ≤ E.op.toNat ∧ E.op.toNat ≤ 15 ∧ e.od + E.val.toNat + 2 ^ E.op.toNat ≤ e.DCA.size := by
        rcases hcl with h | h | h
        · exact absurd hb16' h.1
        · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
        · exact absurd hb64' h.2
      refine Wp.bindO hld ?_
      have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
      have hop32 : E.op.toUInt32.toNat < 32 := by rw [toNat32]; omega
      refine Wp.bindO (x := Ptr.ref e.rd (e.od + E.val.toNat)) ?_ ?_
      · rw [hdc]
        exact Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (Nat.le_trans (Nat.le_add_right _ _) hlink.2.2)
      refine Wp.bindO (shl32_ok hop32) ?_
      have hlow := hold_low64 (x := l.hold >>> E.bits.toUInt32.toUInt64) (k := E.op.toUInt32) hop32
      have hjlt : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat < 2 ^ E.op.toNat := by
        rw [toNat32]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))
      generalize hjd : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat = j at hlow hjlt
      refine Wp.bindO (x := Ptr.ref e.rd (e.od + E.val.toNat + j)) ?_ ?_
      · rw [hlow]
        exact Ptr.add_nat_ok (h := e.heap A msg m) (r := e.rd) (a := e.DCA) (off := e.od + E.val.toNat)
          (n := j) (e.heap_cget_DCA A msg m) (by have := hlink.2.2; omega)
      refine Wp.pure' ⟨i, by omega, by omega, by omega, hls.hin⟩
    · simp only [hb16, hb64, ite_false, Bool.false_eq_true]
      obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid distance code" (by decide +kernel)
      refine Wp.bindE hip ?_
      exact Wp.pure' ⟨i, by omega, by omega, by omega, hls.hin⟩


theorem dodistLoop_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o kidx : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat) (hk : kidx < 2 ^ e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd (e.od + kidx)) (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat)) :
    Wp (cdoWhile (dodist c) (fun l => pure (l.againD, l)) l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ i + 2 ∧ (20 ≤ l.bits.toNat → i' ≤ i + 1) ∧
        l'.in_ = .ref (BRef.blk e.ib) i') := by
  obtain ⟨hksz, hlk, hnl⟩ := distRoot hts kidx hk
  have hcl0 := distClass_of (e := e) _ hlk hnl
  have hEd0 : (e.DCA.getD (e.od + kidx) default).bits.toNat + 0 ≤ 15 := by
    by_cases hl : DistLink (e.DCA.getD (e.od + kidx) default)
    · have := (hlk hl).1; omega
    · have := (hnl hl).1; omega
  obtain ⟨l1, h1, e1, hq1⟩ := dodist_pass hc A msg m l i o 0 (e.od + kidx) hls hA ho hAb hbroke hlen hhere hksz
    (by omega) hEd0 hcl0 (by simpa using hpull)
  have hadv1 := Wp.at_run (dodist_advance_wp hc A msg m l i o 0 (e.od + kidx) hls hA ho hAb hbroke hlen hhere hksz
    (by omega) hEd0 hcl0 (by simpa using hpull)) e1
  obtain ⟨E0, hE0⟩ : ∃ E0, e.DCA.getD (e.od + kidx) default = E0 := ⟨_, rfl⟩
  rw [hE0] at hq1 hlk hnl hcl0 hEd0
  rcases hq1 with ⟨hag, hbr, hh, ⟨hl16, hl64⟩, j, hjlt, hjd, hhere1, hls1, hsg1, hb1, hlen1, hout1, hdist1, hagL1⟩ | ⟨hNL, hag, hend⟩
  · -- a link: the second pass ends the block
    subst hh
    have hlink : DistLink E0 := ⟨hl16, hl64⟩
    have hlk' := hlk hlink
    have hleaf := hlk'.2.2.2.2 j hjlt
    have hk2 : e.od + E0.val.toNat + j < e.DCA.size := by
      have := hlk'.2.2.2.1; omega
    have hcl1 : DistClass e (e.DCA.getD (e.od + E0.val.toNat + j) default) := by
      rcases hleaf.2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hb15' : E0.bits.toNat ≤ 15 := hlk'.1
    obtain ⟨l2, h2, e2, hq2⟩ := dodist_pass hc A msg m l1 i o E0.bits.toNat (e.od + E0.val.toNat + j) hls1 hA ho hAb hbr
      (by rw [hlen1]; exact hlen) hhere1 hk2 (by have := hleaf.1; omega) (by omega) hcl1 (by
        rcases hpull with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩)
    have hadv2 := Wp.at_run (dodist_advance_wp hc A msg m l1 i o E0.bits.toNat (e.od + E0.val.toNat + j) hls1 hA ho hAb hbr
      (by rw [hlen1]; exact hlen) hhere1 hk2 (by have := hleaf.1; omega) (by omega) hcl1 (by
        rcases hpull with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩)) e2
    rcases hq2 with ⟨hag2, -, -, ⟨hl16', hl64'⟩, -⟩ | hend2
    · rcases hleaf.2 with h | h
      · exact absurd hl16' h.1
      · exact absurd hl64' h.2
    · have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 (e.heap A msg m) = .ok ((true, l1), e.heap A msg m) := by simp [hag]
      have c2 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l2 h2 = .ok ((false, l2), h2) := by simp [hend2.2.1]
      have e1' : dodist c l (e.heap A msg m) = .ok (l1, e.heap A msg m) := e1
      refine Wp.of_eq (cdoWhile_two e1' c1 e2 c2) ?_
      obtain ⟨i', hi1, hi2, htight, hin⟩ := hadv2
      exact ⟨i', hi1, hi2, (by intro h; apply htight; omega), hin⟩
  · -- the first pass ended the block
    have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 h1 = .ok ((false, l1), h1) := by simp [hag]
    refine Wp.of_eq (cdoWhile_one e1 c1) ?_
    obtain ⟨i', hi1, hi2, htight, hin⟩ := hadv1
    exact ⟨i', hi1, hi2, (by intro h; apply htight; omega), hin⟩


theorem dolenDist_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat)) :
    Wp (dolenDist c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ i + 2 ∧ (20 ≤ l.bits.toNat → i' ≤ i + 1) ∧
        l'.in_ = .ref (BRef.blk e.ib) i') := by
  unfold dolenDist
  have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
  have hR : e.s0.distbits.toNat < 32 := by have := hts.1; omega
  have hmask : c.dmask.toUInt64.toNat = 2 ^ e.s0.distbits.toNat - 1 := by
    rw [hc.dmask, UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hR
  have hidx := u64_and_mask (x := l.hold) hmask
  have hmod : l.hold.toNat % 2 ^ e.s0.distbits.toNat < 2 ^ e.s0.distbits.toNat :=
    Nat.mod_lt _ (Nat.pow_pos (by omega))
  refine Wp.bindO (x := Ptr.ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat)) ?_ ?_
  · rw [hdc, hidx]
    exact Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (by have := hts.2.1; omega)
  · exact Wp.mono (dodistLoop_advance_wp hc A msg m { l with here := Ptr.ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) }
      i o _ hts hmod (LS.congr hls rfl rfl rfl rfl) hA ho hAb hbroke hlen rfl hb15 hpull) (fun _ _ h => h)

theorem dolenRefill_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3) (hT3 : i = s + 3 → 4 ≤ l.bits.toNat) :
    Wp (dolenRefill c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ s + 6 ∧ l'.in_ = .ref (BRef.blk e.ib) i') := by
  unfold dolenRefill
  by_cases h1 : l.bits < 15
  · simp only [h1, ite_true]
    have h1' : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
    have hl3 := hls.pullL (by omega) hiin
    have hs3 := Sg_pullL hls (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
    have hb3' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at hb3 ⊢; omega
    refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m)) ?_
    have hl4 := hl3.pullL hb3' hi2
    have hs4 := Sg_pullL hl3 hb3' hi2
    have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0)
      (.ref (BRef.blk e.ib) (i + 1 + 1)) hl3.hb
    simp only [pullL] at hb3 hb4
    refine Wp.mono (dolenDist_advance_wp hc A msg m _ (i + 1 + 1) o hts hl4 hA ho hAb hbroke hlen (by simp only [pullL]; omega) ?_) ?_
    · by_cases hc3 : i = s + 3
      · right; have := hT3 hc3; simp only [pullL]; omega
      · left; omega
    · intro l' h' hq
      obtain ⟨i', hi1, hi2, htight, hin⟩ := hq
      refine ⟨i', by omega, ?_, hin⟩
      by_cases hc3 : i = s + 3
      · have hb : 20 ≤ (pullL (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)))
          (e.IN.getD (i + 1) 0) (.ref (BRef.blk e.ib) (i + 1 + 1))).bits.toNat := by
          have := hT3 hc3
          simp only [pullL] at hb3 hb4 ⊢
          omega
        have := htight hb
        omega
      · omega
  · simp only [h1, ite_false]
    have h1' : 15 ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < 15) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
      omega
    refine Wp.mono (dolenDist_advance_wp hc A msg m l i o hts hls hA ho hAb hbroke hlen h1' (Or.inl (by omega))) ?_
    intro l' h' hq
    obtain ⟨i', hi1, hi2, _, hin⟩ := hq
    exact ⟨i', hi1, by omega, hin⟩


theorem dolenExt_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5) (hxb : l.op.toNat ≤ l.bits.toNat)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3)
    (hT3 : i = s + 3 → 4 + l.op.toNat ≤ l.bits.toNat) :
    Wp (dolenExt c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ s + 6 ∧ l'.in_ = .ref (BRef.blk e.ib) i') := by
  unfold dolenExt
  have hxs : l.op.toNat < 32 := by omega
  refine Wp.bindO (shl32_ok hxs) ?_
  dsimp only
  have hlow := hold_low32 (x := l.hold) (k := l.op) hxs
  have hlowlt : l.hold.toNat % 2 ^ l.op.toNat < 2 ^ l.op.toNat := Nat.mod_lt _ (Nat.pow_pos (by omega))
  have hpow : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
  have hlen' : (l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1)).toNat = l.len.toNat + l.hold.toNat % 2 ^ l.op.toNat := by
    rw [u32_toNat_add (by rw [hlow]; omega), hlow]
  refine Wp.bindO (shr64_ok (x := l.hold) (n := l.op.toUInt64) (by rw [UInt32.toNat_toUInt64]; omega)) ?_
  have hls1 : LS e (dropL l l.op) i o := hls.dropL l.op hxb (by omega)
  have hbn := dropL_bits l l.op hxb
  have hrb := readBits_bitsOfNat l.op.toNat l.bits.toNat l.hold.toNat (inBits e i) hxb
  have hsg := Sg_dropL (e := e) l l.op i hxb (by omega)
  refine Wp.mono (dolenRefill_advance_wp hc A msg m
    { in_ := l.in_, out := l.out, hold := l.hold >>> l.op.toUInt64, bits := l.bits - l.op, here := l.here, op := l.op,
      len := l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1), dist := l.dist, from_ := l.from_, broke := l.broke,
      againL := l.againL, againD := l.againD } i o s hts (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb hbroke
    (by rw [hlen']; omega) hs6 hT (by intro h3; have := hT3 h3; show 4 ≤ (l.bits - l.op).toNat; simp only [dropL] at hbn; omega)) ?_
  exact fun _ _ hq => hq


theorem dolenLen_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 2) (hb2 : i = s + 2 → 1 ≤ l.bits.toNat) :
    Wp (dolenLen c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ s + 6 ∧ l'.in_ = .ref (BRef.blk e.ib) i') := by
  unfold dolenLen
  by_cases h0 : l.op != 0
  · simp only [h0, ite_true]
    have h0' : l.op.toNat ≠ 0 := by
      intro h; apply (by simpa using h0 : l.op ≠ 0); exact UInt32.toNat_inj.mp (by simpa using h)
    by_cases h1 : l.bits < l.op
    · simp only [h1, ite_true]
      have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
      have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
      refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
      have hl3 := hls.pullL (by omega) hiin
      have hs3 := Sg_pullL hls (by omega) hiin
      have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
      refine Wp.mono (dolenExt_advance_wp hc A msg m _ (i + 1) o s hts hl3 hA ho hAb hbroke (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 ⊢; omega) (by simp only [pullL]; omega) hs6 (by omega)
        (by intro h3; simp only [pullL] at hb3 ⊢; have := hb2 (by omega); omega)) ?_
      intro l' h' hq
      obtain ⟨i', hi1, hi2, hin⟩ := hq
      exact ⟨i', by omega, hi2, hin⟩
    · simp only [h1, ite_false]
      have h1' : l.op.toNat ≤ l.bits.toNat := by
        have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (dolenExt_advance_wp hc A msg m l i o s hts hls hA ho hAb hbroke hx h1' hlen hs6 (by omega)
        (by intro h3; omega)) ?_
      exact fun _ _ hq => hq
  · simp only [h0, ite_false]
    have h0' : l.op.toNat = 0 := by
      have : l.op = 0 := by simpa using h0
      rw [this]; rfl
    refine Wp.mono (dolenRefill_advance_wp hc A msg m l i o s hts hls hA ho hAb hbroke ⟨hlen.1, by
      have : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
      omega⟩ hs6 (by omega) (by intro h3; omega)) ?_
    exact fun _ _ hq => hq


theorem readBits_value_lt {n : Nat} {inp rest : List Bool} {v : Nat}
    (hr : readBits n inp = some (v, rest)) : v < 2 ^ n := by
  induction n generalizing inp v rest with
  | zero => simp only [readBits, Option.some.injEq, Prod.mk.injEq] at hr; omega
  | succ n ih =>
    cases inp with
    | nil => cases hr
    | cons b r =>
      cases hread : readBits n r with
      | none => simp [readBits, hread] at hr
      | some vr =>
        rcases vr with ⟨v1, r1⟩
        have hv := ih hread
        simp only [readBits, hread, Option.some.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨rfl, rfl⟩
        rw [Nat.pow_succ]
        cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

end Zlib.Inffast.Proofs
