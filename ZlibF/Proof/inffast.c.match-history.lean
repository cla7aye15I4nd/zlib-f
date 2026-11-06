import ZlibF.Spec.InflateFastMatchHistory
import ZlibF.Math.InflateFastMatchHistory

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

variable {e : Env} {c : Ctx}

/- The original execution proof is strengthened with the actual branch test.
The bit/input frame and both original postconditions are preserved. -/
private theorem copy_match_branch_run (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (o : Nat)
    (hout : l.out = .ref (BRef.blk e.ob) o) (hbg : e.bg ≤ o) (hop : l.op.toNat = o - e.bg)
    (hdist : 1 ≤ l.dist.toNat) (hlen : 3 ≤ l.len.toNat) (hroom : o + l.len.toNat ≤ A.size)
    (hbroke : l.broke = false) :
    Wp (copyMatch c l) (e.heap A msg m) (fun l' h' =>
      l'.in_ = l.in_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧ l'.againL = l.againL ∧ l'.againD = l.againD ∧
      l'.broke = decide (c.whave.toNat + (o - e.bg) < l.dist.toNat) ∧
      ((l'.broke = false ∧ l'.out = .ref (BRef.blk e.ob) (o + l.len.toNat) ∧
          h' = e.heap (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o l.dist.toNat l.len.toNat A) msg m) ∨
       (l'.broke = true ∧ ∃ p, h' = e.heap A p BAD ∧ l'.out = l.out))) := by
  have hoA : o ≤ A.size := by omega
  unfold copyMatch
  dsimp only
  by_cases hd : l.dist > l.op
  · simp only [hd, ite_true]
    have hd1 : l.op.toNat < l.dist.toNat := UInt32.lt_iff_toNat_lt.mp hd
    have hop1 : (l.dist - l.op).toNat = l.dist.toNat - (o - e.bg) := by
      rw [u32_toNat_sub (by omega)]; omega
    by_cases hw : l.dist - l.op > c.whave
    · -- too far back
      simp only [hw, ite_true]
      refine Wp.bindO (e.heap_ldstate hc A msg m) ?_
      have hsane : (({ e.s0 with mode := m } : InflateState).sane != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; exact e.hsane
      simp only [hsane, ite_true]
      obtain ⟨i, hi⟩ := badData_run hc A msg m "invalid distance too far back" (by decide +kernel)
      refine Wp.bindE hi ?_
      refine Wp.pure' ?_
      have hhw : c.whave.toNat < (l.dist - l.op).toNat := UInt32.lt_iff_toNat_lt.mp hw
      have htoo : c.whave.toNat + (o - e.bg) < l.dist.toNat := by omega
      exact ⟨rfl, rfl, rfl, rfl, rfl, (by simp [htoo]), Or.inr ⟨rfl, _, rfl, rfl⟩⟩
    · simp only [hw, ite_false]
      have hw' : (l.dist - l.op).toNat ≤ c.whave.toNat := by
        have h1 : ¬ (c.whave < l.dist - l.op) := hw
        have h2 : ¬ (c.whave.toNat < (l.dist - l.op).toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      have hwh : c.whave.toNat ≤ c.wsize.toNat := by rw [hc.whave, hc.wsize]; exact e.hwh
      have hwn : c.wnext.toNat ≤ c.wsize.toNat := by rw [hc.wnext, hc.wsize]; exact e.hwn
      have hws : c.wsize.toNat ≤ 32768 := by rw [hc.wsize]; exact e.hws
      have hwne : e.s0.whave ≠ 0 := by
        intro h0
        have : c.whave.toNat = 0 := by rw [hc.whave, h0]; rfl
        omega
      obtain ⟨hwptr, hwb, hWb, hWsz⟩ := e.hwin hwne
      have hwptr' : c.window = Ptr.ref (BRef.blk e.wb) e.woff := by rw [hc.window]; exact hwptr
      have hsrc : Src e e.wb (fun _ => e.W) := Src.win e e.wb e.W hwb hWb
      have hWg : Space.get (e.heap A msg m) (BRef.blk e.wb) = some e.W := by
        show (e.heap A msg m).bytes e.wb = some e.W
        rw [e.heap_bytes_ne A msg m hwb]; exact hWb
      have hwsz : c.wsize.toNat = e.s0.wsize.toNat := by rw [hc.wsize]
      have hwnx : c.wnext.toNat = e.s0.wnext.toNat := by rw [hc.wnext]
      by_cases hn0 : c.wnext = 0
      · -- (i) the window has not wrapped
        have hn0' : (c.wnext == 0) = true := by simp [hn0]
        simp only [hn0', ite_true]
        have hsubw : (c.wsize - (l.dist - l.op)).toNat = c.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by
          rw [u32_toNat_sub (by omega), hop1]
        have hadd : OkOn (e.heap A msg m) (Ptr.add c.window ↑(c.wsize - (l.dist - l.op)).toNat)
            (Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))))) := by
          rw [hwptr', hsubw]
          exact Ptr.add_nat_ok hWg (by omega)
        refine Wp.bindO hadd ?_
        generalize l.dist - l.op = op1 at hop1 hw' hadd ⊢
        by_cases hlt : op1 < l.len
        · simp only [hlt, ite_true]
          have hlt' : op1.toNat < l.len.toNat := UInt32.lt_iff_toNat_lt.mp hlt
          have hlen1 : (l.len - op1).toNat = l.len.toNat - op1.toNat := u32_toNat_sub (by omega)
          refine Wp.bindE (copyOp_win e e.W msg m e.wb hwb hWb A
            { l with op := op1, len := l.len - op1, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) }
            op1.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o rfl (by omega) rfl hout
            (by omega) (by omega)) ?_
          dsimp only
          generalize hA1 : blitN e.W op1.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o A = A1
          have hA1sz : A1.size = A.size := by rw [← hA1]; exact blitN_size _ _ _ _ _
          have hsub2 : OkOn (e.heap A1 msg m) (subn (Ptr.ref (BRef.blk e.ob) (o + op1.toNat)) l.dist)
              (Ptr.ref (BRef.blk e.ob) (o + op1.toNat - l.dist.toNat)) :=
            subn_ok (r := BRef.blk e.ob) (a := A1) (e.heap_bytes_ob A1 msg m) (by omega) (by omega)
          refine Wp.bindO hsub2 ?_
          refine Wp.of_eq (a := _) (h' := _) (tailW_run (Src.out e) A1 msg m
            { l with out := Ptr.ref (BRef.blk e.ob) (o + op1.toNat), op := 0, len := l.len - op1,
                     from_ := Ptr.ref (BRef.blk e.ob) (o + op1.toNat - l.dist.toNat) }
            (l.len - op1).toNat (o + op1.toNat - l.dist.toNat) (o + op1.toNat) rfl rfl rfl (by simp; omega)
            (by omega)) ?_
          refine ⟨rfl, rfl, rfl, rfl, rfl, (by simp only [hbroke]; have hn : ¬ (c.whave.toNat + (o - e.bg) < l.dist.toNat) := (by omega); simp [hn]), Or.inl ⟨hbroke, ?_, ?_⟩⟩
          · simp only [hlen1]; rw [show o + op1.toNat + (l.len.toNat - op1.toNat) = o + l.len.toNat by omega]
          · simp only [hlen1]
            rw [cpyG_id]
            unfold matchArr
            have h1 : o - e.bg < l.dist.toNat := by omega
            have h2 : e.s0.wnext.toNat = 0 := by rw [← hwnx]; rw [hn0]; rfl
            simp only [h1, h2, hwsz, ite_true]
            have h3 : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
            have h4 : op1.toNat < l.len.toNat := by omega
            have h4' : l.dist.toNat - (o - e.bg) < l.len.toNat := by omega
            have h5 : e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))) =
                e.woff + e.s0.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by omega
            simp only [h3, h4'] at hA1 ⊢
            rw [h5] at hA1
            rw [← hA1]
            try simp
        · simp only [hlt, ite_false]
          have hlt' : l.len.toNat ≤ op1.toNat := by
            have h1 : ¬ (op1 < l.len) := hlt
            have h2 : ¬ (op1.toNat < l.len.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
            omega
          refine Wp.of_eq (a := _) (h' := _) (tailW_run hsrc A msg m
            { l with op := op1, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) }
            l.len.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o rfl rfl hout
            (by show _ ≤ e.W.size; omega) (by omega)) ?_
          refine ⟨rfl, rfl, rfl, rfl, rfl, (by simp only [hbroke]; have hn : ¬ (c.whave.toNat + (o - e.bg) < l.dist.toNat) := (by omega); simp [hn]), Or.inl ⟨hbroke, rfl, ?_⟩⟩
          rw [cpyG_const]
          unfold matchArr
          have h1 : o - e.bg < l.dist.toNat := by omega
          have h2 : e.s0.wnext.toNat = 0 := by rw [← hwnx]; rw [hn0]; rfl
          have h3 : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
          have h4' : ¬ (l.dist.toNat - (o - e.bg) < l.len.toNat) := by omega
          have h5 : e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))) =
              e.woff + e.s0.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by omega
          simp only [h1, h2, h4', ite_true, ite_false, h5]
      · -- the window has wrapped (ii) or the data is contiguous (iii)
        have hn0' : (c.wnext == 0) = false := by simp [hn0]
        simp only [hn0']
        have hn0n : 0 < c.wnext.toNat := by
          have : c.wnext.toNat ≠ 0 := fun h => hn0 (UInt32.toNat_inj.mp (by simpa using h))
          omega
        by_cases hwl : c.wnext < l.dist - l.op
        · -- (ii)
          simp only [hwl, ite_true]
          have hwl' : c.wnext.toNat < (l.dist - l.op).toNat := UInt32.lt_iff_toNat_lt.mp hwl
          have hsum : (c.wsize + c.wnext).toNat = c.wsize.toNat + c.wnext.toNat := u32_toNat_add (by omega)
          have hsubw : (c.wsize + c.wnext - (l.dist - l.op)).toNat =
              c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by
            rw [u32_toNat_sub (by omega), hsum, hop1]
          have hadd : OkOn (e.heap A msg m) (Ptr.add c.window ↑(c.wsize + c.wnext - (l.dist - l.op)).toNat)
              (Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg))))) := by
            rw [hwptr', hsubw]
            exact Ptr.add_nat_ok hWg (by omega)
          refine Wp.bindO hadd ?_
          generalize l.dist - l.op = op1 at hop1 hw' hadd hwl' ⊢
          have hop2 : (op1 - c.wnext).toNat = op1.toNat - c.wnext.toNat := u32_toNat_sub (by omega)
          generalize op1 - c.wnext = op2 at hop2 ⊢
          have hfo1 : e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg))) =
              e.woff + e.s0.wsize.toNat + e.s0.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by omega
          by_cases hlt : op2 < l.len
          · simp only [hlt, ite_true]
            have hlt' : op2.toNat < l.len.toNat := UInt32.lt_iff_toNat_lt.mp hlt
            have hlen1 : (l.len - op2).toNat = l.len.toNat - op2.toNat := u32_toNat_sub (by omega)
            refine Wp.bindE (copyOp_win e e.W msg m e.wb hwb hWb A
              { l with op := op2, len := l.len - op2, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) }
              op2.toNat (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o rfl (by omega) rfl hout
              (by omega) (by omega)) ?_
            dsimp only
            generalize hA1 : blitN e.W op2.toNat (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o A = A1
            have hA1sz : A1.size = A.size := by rw [← hA1]; exact blitN_size _ _ _ _ _
            by_cases hwl2 : c.wnext < l.len - op2
            · simp only [hwl2, ite_true]
              have hwl2' : c.wnext.toNat < (l.len - op2).toNat := UInt32.lt_iff_toNat_lt.mp hwl2
              have hlen2 : (l.len - op2 - c.wnext).toNat = l.len.toNat - op2.toNat - c.wnext.toNat := by
                rw [u32_toNat_sub (by omega), hlen1]
              refine Wp.bindE (copyOp_win e e.W msg m e.wb hwb hWb A1
                { l with out := Ptr.ref (BRef.blk e.ob) (o + op2.toNat), op := c.wnext, len := l.len - op2 - c.wnext,
                         from_ := c.window }
                c.wnext.toNat e.woff (o + op2.toNat) rfl hn0n hwptr' rfl (by omega) (by omega)) ?_
              dsimp only
              generalize hA2 : blitN e.W c.wnext.toNat e.woff (o + op2.toNat) A1 = A2
              have hA2sz : A2.size = A.size := by rw [← hA2]; rw [blitN_size]; exact hA1sz
              have hsub2 : OkOn (e.heap A2 msg m) (subn (Ptr.ref (BRef.blk e.ob) (o + op2.toNat + c.wnext.toNat)) l.dist)
                  (Ptr.ref (BRef.blk e.ob) (o + op2.toNat + c.wnext.toNat - l.dist.toNat)) :=
                subn_ok (r := BRef.blk e.ob) (a := A2) (e.heap_bytes_ob A2 msg m) (by omega) (by omega)
              refine Wp.bindO hsub2 ?_
              refine Wp.of_eq (a := _) (h' := _) (tailW_run (Src.out e) A2 msg m
                { l with out := Ptr.ref (BRef.blk e.ob) (o + op2.toNat + c.wnext.toNat), op := 0,
                         len := l.len - op2 - c.wnext,
                         from_ := Ptr.ref (BRef.blk e.ob) (o + op2.toNat + c.wnext.toNat - l.dist.toNat) }
                (l.len - op2 - c.wnext).toNat (o + op2.toNat + c.wnext.toNat - l.dist.toNat)
                (o + op2.toNat + c.wnext.toNat) rfl rfl rfl (by simp; omega) (by omega)) ?_
              refine ⟨rfl, rfl, rfl, rfl, rfl, (by simp only [hbroke]; have hn : ¬ (c.whave.toNat + (o - e.bg) < l.dist.toNat) := (by omega); simp [hn]), Or.inl ⟨hbroke, ?_, ?_⟩⟩
              · simp only [hlen2]; rw [show o + op2.toNat + c.wnext.toNat + (l.len.toNat - op2.toNat - c.wnext.toNat) = o + l.len.toNat by omega]
              · simp only [hlen2]
                rw [cpyG_id]
                unfold matchArr
                have h1 : o - e.bg < l.dist.toNat := by omega
                have h2 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
                have h3 : e.s0.wnext.toNat < l.dist.toNat - (o - e.bg) := by rw [← hwnx]; omega
                have h4 : l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat < l.len.toNat := by rw [← hwnx]; omega
                have h5 : e.s0.wnext.toNat < l.len.toNat - (l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat) := by
                  rw [← hwnx]; omega
                simp only [h1, h2, h3, h4, h5, ite_true, ite_false]
                rw [← hA2, ← hA1, hfo1]
                have hop2' : op2.toNat = l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat := by omega
                simp only [hop2', hwnx]
            · simp only [hwl2, ite_false]
              have hwl2' : (l.len - op2).toNat ≤ c.wnext.toNat := by
                have h1 : ¬ (c.wnext < l.len - op2) := hwl2
                have h2 : ¬ (c.wnext.toNat < (l.len - op2).toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
                omega
              refine Wp.of_eq (a := _) (h' := _) (tailW_run hsrc A1 msg m
                { l with out := Ptr.ref (BRef.blk e.ob) (o + op2.toNat), op := 0, len := l.len - op2, from_ := c.window }
                (l.len - op2).toNat e.woff (o + op2.toNat) rfl hwptr' rfl (by show _ ≤ e.W.size; omega) (by omega)) ?_
              refine ⟨rfl, rfl, rfl, rfl, rfl, (by simp only [hbroke]; have hn : ¬ (c.whave.toNat + (o - e.bg) < l.dist.toNat) := (by omega); simp [hn]), Or.inl ⟨hbroke, ?_, ?_⟩⟩
              · simp only [hlen1]; rw [show o + op2.toNat + (l.len.toNat - op2.toNat) = o + l.len.toNat by omega]
              · simp only [hlen1]
                rw [cpyG_const]
                unfold matchArr
                have h1 : o - e.bg < l.dist.toNat := by omega
                have h2 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
                have h3 : e.s0.wnext.toNat < l.dist.toNat - (o - e.bg) := by rw [← hwnx]; omega
                have h4 : l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat < l.len.toNat := by rw [← hwnx]; omega
                have h5 : ¬ (e.s0.wnext.toNat < l.len.toNat - (l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat)) := by
                  rw [← hwnx]; omega
                simp only [h1, h2, h3, h4, h5, ite_true, ite_false]
                rw [← hA1, hfo1]
                have hop2' : op2.toNat = l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat := by omega
                simp only [hop2', hwnx]
          · simp only [hlt, ite_false]
            have hlt' : l.len.toNat ≤ op2.toNat := by
              have h1 : ¬ (op2 < l.len) := hlt
              have h2 : ¬ (op2.toNat < l.len.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
              omega
            refine Wp.of_eq (a := _) (h' := _) (tailW_run hsrc A msg m
              { l with op := op2, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) }
              l.len.toNat (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o rfl rfl hout
              (by show _ ≤ e.W.size; omega) (by omega)) ?_
            refine ⟨rfl, rfl, rfl, rfl, rfl, (by simp only [hbroke]; have hn : ¬ (c.whave.toNat + (o - e.bg) < l.dist.toNat) := (by omega); simp [hn]), Or.inl ⟨hbroke, rfl, ?_⟩⟩
            rw [cpyG_const]
            unfold matchArr
            have h1 : o - e.bg < l.dist.toNat := by omega
            have h2 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
            have h3 : e.s0.wnext.toNat < l.dist.toNat - (o - e.bg) := by rw [← hwnx]; omega
            have h4 : ¬ (l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat < l.len.toNat) := by rw [← hwnx]; omega
            simp only [h1, h2, h3, h4, ite_true, ite_false]
            rw [hfo1]
        · -- (iii)
          simp only [hwl, ite_false]
          have hwl' : (l.dist - l.op).toNat ≤ c.wnext.toNat := by
            have h2 : ¬ (c.wnext.toNat < (l.dist - l.op).toNat) := fun h => hwl (UInt32.lt_iff_toNat_lt.mpr h)
            omega
          have hsubw : (c.wnext - (l.dist - l.op)).toNat = c.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by
            rw [u32_toNat_sub (by omega), hop1]
          have hadd : OkOn (e.heap A msg m) (Ptr.add c.window ↑(c.wnext - (l.dist - l.op)).toNat)
              (Ptr.ref (BRef.blk e.wb) (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg))))) := by
            rw [hwptr', hsubw]
            exact Ptr.add_nat_ok hWg (by omega)
          refine Wp.bindO hadd ?_
          generalize l.dist - l.op = op1 at hop1 hw' hadd hwl' ⊢
          by_cases hlt : op1 < l.len
          · simp only [hlt, ite_true]
            have hlt' : op1.toNat < l.len.toNat := UInt32.lt_iff_toNat_lt.mp hlt
            have hlen1 : (l.len - op1).toNat = l.len.toNat - op1.toNat := u32_toNat_sub (by omega)
            refine Wp.bindE (copyOp_win e e.W msg m e.wb hwb hWb A
              { l with op := op1, len := l.len - op1, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) }
              op1.toNat (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o rfl (by omega) rfl hout
              (by omega) (by omega)) ?_
            dsimp only
            generalize hA1 : blitN e.W op1.toNat (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o A = A1
            have hA1sz : A1.size = A.size := by rw [← hA1]; exact blitN_size _ _ _ _ _
            have hsub2 : OkOn (e.heap A1 msg m) (subn (Ptr.ref (BRef.blk e.ob) (o + op1.toNat)) l.dist)
                (Ptr.ref (BRef.blk e.ob) (o + op1.toNat - l.dist.toNat)) :=
              subn_ok (r := BRef.blk e.ob) (a := A1) (e.heap_bytes_ob A1 msg m) (by omega) (by omega)
            refine Wp.bindO hsub2 ?_
            refine Wp.of_eq (a := _) (h' := _) (tailW_run (Src.out e) A1 msg m
              { l with out := Ptr.ref (BRef.blk e.ob) (o + op1.toNat), op := 0, len := l.len - op1,
                       from_ := Ptr.ref (BRef.blk e.ob) (o + op1.toNat - l.dist.toNat) }
              (l.len - op1).toNat (o + op1.toNat - l.dist.toNat) (o + op1.toNat) rfl rfl rfl (by simp; omega)
              (by omega)) ?_
            refine ⟨rfl, rfl, rfl, rfl, rfl, (by simp only [hbroke]; have hn : ¬ (c.whave.toNat + (o - e.bg) < l.dist.toNat) := (by omega); simp [hn]), Or.inl ⟨hbroke, ?_, ?_⟩⟩
            · simp only [hlen1]; rw [show o + op1.toNat + (l.len.toNat - op1.toNat) = o + l.len.toNat by omega]
            · simp only [hlen1]
              rw [cpyG_id]
              unfold matchArr
              have h1 : o - e.bg < l.dist.toNat := by omega
              have h2 : ¬ (e.s0.wnext.toNat < l.dist.toNat - (o - e.bg)) := by rw [← hwnx]; omega
              have h3 : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
              have h4' : l.dist.toNat - (o - e.bg) < l.len.toNat := by omega
              have h5 : e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg))) =
                  e.woff + e.s0.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by omega
              have h6 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
              simp only [h1, h2, h3, h4', h6, ite_true, ite_false] at hA1 ⊢
              rw [h5] at hA1
              rw [← hA1]
          · simp only [hlt, ite_false]
            have hlt' : l.len.toNat ≤ op1.toNat := by
              have h1 : ¬ (op1 < l.len) := hlt
              have h2 : ¬ (op1.toNat < l.len.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
              omega
            refine Wp.of_eq (a := _) (h' := _) (tailW_run hsrc A msg m
              { l with op := op1, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) }
              l.len.toNat (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o rfl rfl hout
              (by show _ ≤ e.W.size; omega) (by omega)) ?_
            refine ⟨rfl, rfl, rfl, rfl, rfl, (by simp only [hbroke]; have hn : ¬ (c.whave.toNat + (o - e.bg) < l.dist.toNat) := (by omega); simp [hn]), Or.inl ⟨hbroke, rfl, ?_⟩⟩
            rw [cpyG_const]
            unfold matchArr
            have h1 : o - e.bg < l.dist.toNat := by omega
            have h2 : ¬ (e.s0.wnext.toNat < l.dist.toNat - (o - e.bg)) := by rw [← hwnx]; omega
            have h4' : ¬ (l.dist.toNat - (o - e.bg) < l.len.toNat) := by omega
            have h5 : e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg))) =
                e.woff + e.s0.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by omega
            have h6 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
            simp only [h1, h2, h4', h6, ite_true, ite_false, h5]
  · simp only [hd, ite_false]
    have hd' : l.dist.toNat ≤ o - e.bg := by
      have h1 : ¬ (l.op < l.dist) := hd
      have h2 : ¬ (l.op.toNat < l.dist.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
      omega
    have hsub : OkOn (e.heap A msg m) (subn l.out l.dist) (Ptr.ref (BRef.blk e.ob) (o - l.dist.toNat)) := by
      rw [hout]; exact subn_ok (r := BRef.blk e.ob) (a := A) (e.heap_bytes_ob A msg m) (by omega) hoA
    refine Wp.bindO hsub ?_
    refine Wp.of_eq (a := _) (h' := _) (tailD_run (Src.out e) A msg m
      { l with from_ := Ptr.ref (BRef.blk e.ob) (o - l.dist.toNat) } l.len.toNat (o - l.dist.toNat) o rfl hlen rfl hout
      (by simp; omega) (by omega)) ?_
    have hmb : ¬ (o - e.bg < l.dist.toNat) := by omega
    refine ⟨rfl, rfl, rfl, rfl, rfl, (by simp only [hbroke]; have hn : ¬ (c.whave.toNat + (o - e.bg) < l.dist.toNat) := (by omega); simp [hn]), Or.inl ⟨hbroke, rfl, ?_⟩⟩
    simp [matchArr, hmb, cpyG_id]



/-- The actual fast copy cut point rejects exactly unavailable history, and
otherwise implements the independent growing-history match operation. -/
theorem actual_copy_match_refines_lz77 : MatchHistory.Goal.actual_copy_match_refines_lz77 := by
  intro e c bytes msg mode l o hc hout hbg hop hdist hlen hroom hbroke
  dsimp only
  have hsaved : (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
      e.s0.whave.toNat e.woff).length = e.s0.whave.toNat := by
    simp [MatchHistory.saved]
  have hcurrent : (ZlibF.Math.LZ77Copy.writtenBytes bytes o (o - e.bg)).length = o - e.bg := by
    simp only [ZlibF.Math.LZ77Copy.writtenBytes, List.length_take,
      List.length_drop, Array.length_toList]
    omega
  simp only [hsaved, hcurrent]
  obtain ⟨l', after, hrun, hin, hhold, hbits, hagainL, hagainD, hbranch, hpost⟩ :=
    copy_match_branch_run hc bytes msg mode l o hout hbg hop hdist hlen hroom hbroke
  rw [hc.whave] at hbranch
  by_cases htoo : e.s0.whave.toNat + (o - e.bg) < l.dist.toNat
  · simp only [htoo, ite_true]
    have hbreak : l'.broke = true := by simpa only [htoo, decide_true] using hbranch
    rcases hpost with hsuccess | ⟨_, p, hheap, hout'⟩
    · rw [hsuccess.1] at hbreak
      contradiction
    · exact ⟨l', after, p, hrun, hin, hhold, hbits, hagainL, hagainD, hbreak, hout', hheap⟩
  · simp only [htoo, ite_false]
    have hbreak : l'.broke = false := by simpa only [htoo, decide_false] using hbranch
    rcases hpost with ⟨_, hout', hheap⟩ | ⟨hbad, _⟩
    · refine ⟨l', after, hrun, hin, hhold, hbits, hagainL, hagainD, hbreak, hout', hheap, ?_⟩
      apply fast_match_array_refines_lz77 e.W bytes e.s0.wsize.toNat e.s0.wnext.toNat
        e.s0.whave.toNat e.woff e.bg o l.dist.toNat l.len.toNat e.hwh e.hwn
      · intro hwh
        have hne : e.s0.whave ≠ 0 := by
          intro hz
          apply hwh
          simp [hz]
        exact (e.hwin hne).2.2.2
      · exact hbg
      · exact hroom
      · omega
      · omega
    · rw [hbad] at hbreak
      contradiction

end Zlib.Inffast.Proofs
