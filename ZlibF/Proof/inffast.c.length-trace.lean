import ZlibF.Spec.InflateFastLengthTrace
import ZlibF.Proof.«inffast.c.body»

/-!
# Selected length-table entries through the actual fast body

The source pass retains its exact entry and both levels' bit count. The
four leaf outcomes retain actual output or the real length-extra and
subsequent distance results. Existing safety is joined on the same run.
-/

namespace Zlib.Inffast.Proofs.LengthTraceProof
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Proofs ZlibF.Spec
open Zlib.Inffast.Spec.LengthTrace

variable {e : Env} {c : Ctx}

set_option maxHeartbeats 1000000 in
private theorem pass_trace_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s d k : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat + d) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat + d)
    (hhere : l.here = .ref e.rl k) (hk : k < e.LCA.size)
    (hEb : (e.LCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.LCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : (LenLink (e.LCA.getD k default) ∧ LinkOK LenLeaf e.LCA e.ol (e.LCA.getD k default)) ∨
      LenLeaf d (e.LCA.getD k default)) :
    Wp (dolen c l) (e.heap A msg m) (fun l' h' =>
      (l'.againL = true ∧ l'.broke = false ∧ h' = e.heap A msg m ∧
        LenLink (e.LCA.getD k default) ∧
        ∃ j, j < 2 ^ (e.LCA.getD k default).op.toNat ∧
          l'.here = .ref e.rl (e.ol + (e.LCA.getD k default).val.toNat + j) ∧
          j = (l.hold.toNat / 2 ^ (e.LCA.getD k default).bits.toNat) % 2 ^ (e.LCA.getD k default).op.toNat ∧
          LS e l' i o ∧ l'.bits.toNat = l.bits.toNat - (e.LCA.getD k default).bits.toNat ∧
          Sg e l'.hold.toNat l'.bits.toNat i = (Sg e l.hold.toNat l.bits.toNat i).drop (e.LCA.getD k default).bits.toNat) ∨
      End e A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop (e.LCA.getD k default).bits.toNat)
        i o (e.LCA.getD k default) l' h') := by
  have hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hAb : A.size < 2 ^ 63 := by rw [hAsz]; exact e.hAbig
  have hkE : e.LCA[k]'hk = e.LCA.getD k default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.LCA.getD k default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A msg m) hk
  have hEbn : (e.LCA.getD k default).bits.toUInt32.toNat = (e.LCA.getD k default).bits.toNat := toNat32 _
  have hEb64 : (e.LCA.getD k default).bits.toUInt32.toUInt64.toNat = (e.LCA.getD k default).bits.toNat := by simp [toNat32]
  have hls1 := hls.dropL (e.LCA.getD k default).bits.toUInt32 (by omega) (by omega)
  have hsg1 := Sg_dropL (e := e) l (e.LCA.getD k default).bits.toUInt32 i (by omega) (by omega)
  rw [dolen_eq_len]
  dsimp only
  refine Wp.bindO hld ?_
  refine Wp.bindO (shr64_ok (x := l.hold) (by omega)) ?_
  refine Wp.bindO hld ?_
  generalize e.LCA.getD k default = E at *
  have hsg1' : Sg e (l.hold >>> E.bits.toUInt32.toUInt64).toNat (l.bits - E.bits.toUInt32).toNat i =
      (Sg e l.hold.toNat l.bits.toNat i).drop E.bits.toNat := by
    simpa only [dropL, hEbn] using hsg1
  by_cases hz : (E.op.toUInt32 == 0) = true
  · simp only [hz, ite_true]
    refine Wp.bindO hld ?_
    have hst : store8 l.out E.val.toUInt8 (e.heap A msg m) =
        .ok ((), e.heap (A.set! o E.val.toUInt8) msg m) := by
      rw [hls.hout, ← e.heap_put A (A.set! o E.val.toUInt8) msg m]
      exact Ptr.store_ok (e.heap_bytes_ob A msg m) (e.heap_ro_ob A msg m) (by omega)
    refine Wp.bindE hst ?_
    refine Wp.bindO (x := Ptr.ref (BRef.blk e.ob) (o + 1)) ?_ ?_
    · rw [hls.hout]
      exact Ptr.add_nat_ok (e.heap_bytes_ob _ msg m) (by simp; omega)
    · have hop : E.op = 0 := by rw [mask0] at hz; simpa using hz
      refine Wp.pure' (Or.inr ?_)
      refine ⟨?_, rfl, Or.inl ⟨hop, hbroke, ?_, hsg1', rfl⟩⟩
      · intro link; exact link.1 hop
      · exact ⟨hls.hin, rfl, hls.hi0, hls.hi1, by have := hls.ho0; omega, hls1.hb, hls1.hH, hls1.hacc⟩
  · have hz' : E.op ≠ 0 := by rw [mask0] at hz; simpa using hz
    by_cases hb16 : (E.op.toUInt32 &&& 16 != 0) = true
    · simp only [hz, hb16, ite_true, ite_false, Bool.false_eq_true]
      have hb16' : E.op &&& 16 ≠ 0 := by rw [mask16] at hb16; simpa using hb16
      have hbase : (E.op &&& 15).toNat ≤ 5 ∧ 3 ≤ E.val.toNat ∧
          E.val.toNat + 2 ^ (E.op &&& 15).toNat ≤ 259 := by
        rcases hcl with h | h
        · exact False.elim (hb16' h.1.2.1)
        · rcases h.2 with h0 | h | h
          · exact False.elim (hz' h0)
          · exact h.2
          · exact False.elim (hb16' h.1)
      refine Wp.bindO hld ?_
      let stage : L :=
        { in_ := l.in_, out := l.out, hold := l.hold >>> E.bits.toUInt32.toUInt64, bits := l.bits - E.bits.toUInt32,
          here := l.here, op := E.op.toUInt32 &&& 15, len := E.val.toUInt32, dist := l.dist, from_ := l.from_,
          broke := l.broke, againL := false, againD := l.againD }
      obtain ⟨l', h', run, result⟩ := dolenLen_wp hc A msg m stage i o s e.hdt
        (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb hbroke
        (by dsimp [stage]; rw [mask15]; exact hbase.1)
        (by simpa [stage, mask15] using hbase.2) hs6 hT
        (by intro hi; have := hbi2 hi; show 1 ≤ (l.bits - E.bits.toUInt32).toNat
            rw [u32_toNat_sub (by omega), hEbn]; omega)
      have hag : l'.againL = false := by simpa [stage] using dolenLen_againL run
      refine Wp.of_eq run (Or.inr ?_)
      refine ⟨?_, hag, Or.inr (Or.inl ⟨hz', hb16', ?_⟩)⟩
      · intro link; exact hb16' link.2.1
      · obtain ⟨i', extra, rest, hi, hi1, read, refill⟩ := result
        refine ⟨i', extra, rest, hi, hi1, ?_, ?_⟩
        · simpa only [stage, mask15, hsg1'] using read
        · simpa only [stage, UInt16.toNat_toUInt32] using refill
    · have hb16' : E.op &&& 16 = 0 := by rw [mask16] at hb16; simpa using hb16
      by_cases hb64 : (E.op.toUInt32 &&& 64 == 0) = true
      · simp only [hz, hb16, hb64, ite_true, ite_false, Bool.false_eq_true]
        have hb64' : E.op &&& 64 = 0 := by rw [mask64] at hb64; simpa using hb64
        have hl : LenLink E := ⟨hz', hb16', hb64'⟩
        have hlk : LinkOK LenLeaf e.LCA e.ol E := by
          rcases hcl with h | h
          · exact h.2
          · rcases h.2 with h0 | h | h
            · exact False.elim (hz' h0)
            · exact False.elim (h.1 hb16')
            · exact False.elim (h.2 hb64')
        refine Wp.bindO hld ?_
        have hlc : c.lcode = .ref e.rl e.ol := by rw [hc.lcode]; exact e.hlc
        have hop32 : E.op.toUInt32.toNat < 32 := by rw [toNat32]; have := hlk.2.2.1; omega
        refine Wp.bindO (x := Ptr.ref e.rl (e.ol + E.val.toNat)) ?_ ?_
        · rw [hlc]
          exact Ptr.add_nat_ok (h := e.heap A msg m) (r := e.rl) (a := e.LCA) (off := e.ol)
            (n := E.val.toNat) (e.heap_cget_LCA A msg m)
            (Nat.le_trans (Nat.le_add_right _ _) hlk.2.2.2.1)
        refine Wp.bindO (shl32_ok hop32) ?_
        have hlow := hold_low64 (x := l.hold >>> E.bits.toUInt32.toUInt64) (k := E.op.toUInt32) hop32
        have hjlt : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat < 2 ^ E.op.toNat := by
          rw [toNat32]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))
        generalize hjd : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat = j at hlow hjlt
        refine Wp.bindO (x := Ptr.ref e.rl (e.ol + E.val.toNat + j)) ?_ ?_
        · rw [hlow]
          exact Ptr.add_nat_ok (h := e.heap A msg m) (r := e.rl) (a := e.LCA) (off := e.ol + E.val.toNat)
            (n := j) (e.heap_cget_LCA A msg m) (by have := hlk.2.2.2.1; omega)
        refine Wp.pure' (Or.inl ⟨rfl, hbroke, rfl, hl, j, hjlt, rfl, ?_,
          LS.congr hls1 rfl rfl rfl rfl, ?_, hsg1'⟩)
        · have hshift : (l.hold >>> E.bits.toUInt32.toUInt64).toNat = l.hold.toNat / 2 ^ E.bits.toNat := by
            rw [u64_shr (by omega), hEbn]
          simpa only [hshift, toNat32] using hjd.symm
        · rw [u32_toNat_sub (by omega), hEbn]
      · simp only [hz, hb16, hb64, ite_false, Bool.false_eq_true]
        by_cases hb32 : (E.op.toUInt32 &&& 32 != 0) = true
        · simp only [hb32, ite_true]
          refine Wp.bindE (e.heap_ldstate hc A msg m) ?_
          refine Wp.bindE (e.heap_stmode hc A msg m TYPE _ rfl) ?_
          have hb64' : E.op &&& 64 ≠ 0 := by rw [mask64] at hb64; simpa using hb64
          have hb32' : E.op &&& 32 ≠ 0 := by rw [mask32] at hb32; simpa using hb32
          refine Wp.pure' (Or.inr ?_)
          refine ⟨?_, rfl, Or.inr (Or.inr (Or.inl ⟨hz', hb16', hb64', hb32', rfl,
            LS.congr hls1 rfl rfl rfl rfl, hsg1', rfl⟩))⟩
          intro link; exact hb64' link.2.2
        · simp only [hb32, ite_false, Bool.false_eq_true]
          obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid literal/length code" (by decide +kernel)
          refine Wp.bindE hip ?_
          have hb64' : E.op &&& 64 ≠ 0 := by rw [mask64] at hb64; simpa using hb64
          have hb32' : E.op &&& 32 = 0 := by rw [mask32] at hb32; simpa using hb32
          refine Wp.pure' (Or.inr ?_)
          refine ⟨?_, rfl, Or.inr (Or.inr (Or.inr ⟨hz', hb16', hb64', hb32', rfl,
            LS.congr hls1 rfl rfl rfl rfl, hsg1', .ref (.str ip) 0, rfl⟩))⟩
          intro link; exact hb64' link.2.2

private theorem loop_trace_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s kidx : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat)
    (hk : kidx < 2 ^ e.s0.lenbits.toNat) (hhere : l.here = .ref e.rl (e.ol + kidx)) :
    Wp (cdoWhile (dolen c) (fun l => pure (l.againL, l)) l) (e.heap A msg m)
      (fun l' h' => ∃ entry consumed, consumed ≤ 15 ∧
        LengthSemantics.Look e l.hold.toNat kidx entry consumed ∧
        End e A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop consumed) i o entry l' h') := by
  obtain ⟨hR, hsz, hall⟩ := e.hlt
  have hksz : e.ol + kidx < e.LCA.size := by omega
  have hclass : (LenLink (e.LCA.getD (e.ol + kidx) default) ∧
      LinkOK LenLeaf e.LCA e.ol (e.LCA.getD (e.ol + kidx) default)) ∨
      LenLeaf 0 (e.LCA.getD (e.ol + kidx) default) := by
    have hh := hall kidx hk
    by_cases hl : LenLink (e.LCA.getD (e.ol + kidx) default)
    · rw [if_pos hl] at hh; exact Or.inl ⟨hl, hh⟩
    · rw [if_neg hl] at hh; exact Or.inr hh
  have hEd0 : (e.LCA.getD (e.ol + kidx) default).bits.toNat + 0 ≤ 15 := by
    rcases hclass with h | h
    · exact h.2.1
    · exact h.1
  obtain ⟨l1, h1, run1, result1⟩ := pass_trace_wp hc A msg m l i o s 0 (e.ol + kidx) hls hAsz ho hbroke
    hs6 hsi hT (by omega) (by intro hi; have := hbi2 hi; omega) hhere hksz (by omega) hEd0 hclass
  generalize firstCell : e.LCA.getD (e.ol + kidx) default = first at result1 hclass hEd0
  rcases result1 with ⟨again1, broke1, heap1, link1, j, jLt, here1, jEq, locals1, bits1, stream1⟩ | end1
  · subst heap1
    have links : LinkOK LenLeaf e.LCA e.ol first := by
      rcases hclass with h | h
      · exact h.2
      · rcases h.2 with h0 | h | h
        · exact False.elim (link1.1 h0)
        · exact False.elim (h.1 link1.2.1)
        · exact False.elim (h.2 link1.2.2)
    have leaf := links.2.2.2.2 j jLt
    have secondIn : e.ol + first.val.toNat + j < e.LCA.size := by have := links.2.2.2.1; omega
    obtain ⟨l2, h2, run2, result2⟩ := pass_trace_wp hc A msg m l1 i o s first.bits.toNat
      (e.ol + first.val.toNat + j) locals1 hAsz ho broke1 hs6 hsi hT
      (by omega) (by intro hi; have := hbi2 hi; omega) here1 secondIn
      (by have := leaf.1; omega) leaf.1 (Or.inr leaf)
    rcases result2 with ⟨_, _, _, link2, _⟩ | end2
    · rcases leaf.2 with h0 | h | h
      · exact False.elim (link2.1 h0)
      · exact False.elim (h.1 link2.2.1)
      · exact False.elim (h.2 link2.2.2)
    · have cond1 : (fun q : L => (pure (q.againL, q) : M (Bool × L))) l1 (e.heap A msg m) =
          .ok ((true, l1), e.heap A msg m) := by simp [again1]
      have cond2 : (fun q : L => (pure (q.againL, q) : M (Bool × L))) l2 h2 =
          .ok ((false, l2), h2) := by simp [end2.2.1]
      refine Wp.of_eq (cdoWhile_two run1 cond1 run2 cond2)
        ⟨e.LCA.getD (e.ol + first.val.toNat + j) default,
          first.bits.toNat + (e.LCA.getD (e.ol + first.val.toNat + j) default).bits.toNat,
          by have := leaf.1; omega, ?_, ?_⟩
      · exact Or.inr ⟨first, j, firstCell, link1, jLt, jEq, rfl, rfl, by have := leaf.1; omega, end2.1⟩
      · simpa only [stream1, List.drop_drop] using end2
  · have cond1 : (fun q : L => (pure (q.againL, q) : M (Bool × L))) l1 h1 =
        .ok ((false, l1), h1) := by simp [end1.2.1]
    exact Wp.of_eq (cdoWhile_one run1 cond1)
      ⟨first, first.bits.toNat, by omega, Or.inl ⟨firstCell, rfl, end1.1⟩, end1⟩

private theorem root_trace_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat) :
    Wp (do
      let here ← c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat
      cdoWhile (dolen c) (fun l => pure (l.againL, l)) {l with here}) (e.heap A msg m)
      (fun l' h' => ∃ entry consumed, consumed ≤ 15 ∧
        LengthSemantics.Look e l.hold.toNat (l.hold.toNat % 2 ^ e.s0.lenbits.toNat) entry consumed ∧
        End e A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop consumed) i o entry l' h') := by
  have hlc : c.lcode = .ref e.rl e.ol := by rw [hc.lcode]; exact e.hlc
  have hR : e.s0.lenbits.toNat < 32 := by have := e.hlt.1; omega
  have hmask : c.lmask.toUInt64.toNat = 2 ^ e.s0.lenbits.toNat - 1 := by
    rw [hc.lmask, UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hR
  have hidx := u64_and_mask (x := l.hold) hmask
  have hmod : l.hold.toNat % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
    Nat.mod_lt _ (Nat.pow_pos (by omega))
  refine Wp.bindO (x := Ptr.ref e.rl (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat)) ?_ ?_
  · rw [hlc, hidx]
    exact Ptr.add_nat_ok (e.heap_cget_LCA A msg m) (by have := e.hlt.2.1; omega)
  · exact loop_trace_wp hc A msg m _ i o s _ (LS.congr hls rfl rfl rfl rfl)
      hAsz ho hbroke hs6 hsi hT hb15 hbi2 hmod rfl

/-- The complete source body retains the chosen literal/length leaf and
its exact effects, together with the independently proved safety result. -/
theorem actual_body_retains_selected_length : LengthTrace.Goal.actual_body_retains_selected_length := by
  intro e c A msg m l i o hp
  have hc := hp.context
  have hls := hp.locals
  have hAsz := hp.outputSize
  have hi6 := hp.inputRoom
  have ho258 := hp.outputRoom
  have hbroke := hp.notStopped
  have trace : Wp (inflate_fast_body c l) (e.heap A msg m) (fun l' h' =>
      Sg e (ready e l i).1.hold.toNat (ready e l i).1.bits.toNat (ready e l i).2 =
        Sg e l.hold.toNat l.bits.toNat i ∧
      ∃ entry consumed, consumed ≤ 15 ∧
        LengthSemantics.Look e (ready e l i).1.hold.toNat
          ((ready e l i).1.hold.toNat % 2 ^ e.s0.lenbits.toNat) entry consumed ∧
        End e A msg m ((Sg e (ready e l i).1.hold.toNat (ready e l i).1.bits.toNat
          (ready e l i).2).drop consumed) (ready e l i).2 o entry l' h') := by
    unfold inflate_fast_body
    by_cases h1 : l.bits < 15
    · simp only [ready, h1, ite_true]
      have hb : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
      have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
      refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
      have hl1 := hls.pullL (by omega) hiin
      have stream1 := Sg_pullL hls (by omega) hiin
      have hb1 := pullL_bits l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)) hls.hb
      have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
      have hb1' : (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
        simp only [pullL] at hb1 ⊢; omega
      refine Wp.bindO (pull_run e _ _ (i + 1) o hl1 hb1' hi2 (e.heap_bytes_in A msg m)) ?_
      have hl2 := hl1.pullL hb1' hi2
      have stream2 := Sg_pullL hl1 hb1' hi2
      have hb2 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (.blk e.ib) (i + 1)))
        (e.IN.getD (i + 1) 0) (.ref (.blk e.ib) (i + 1 + 1)) hl1.hb
      refine Wp.mono (root_trace_wp hc A msg m _ (i + 1 + 1) o i hl2 hAsz ho258 hbroke hi6 (by omega) (by omega)
        (by simp only [pullL] at hb1 hb2 ⊢; omega)
        (by intro _; simp only [pullL] at hb1 hb2 ⊢; omega)) ?_
      intro l' h' result
      exact ⟨stream2.trans stream1, result⟩
    · simp only [ready, h1, ite_false]
      have hb : 15 ≤ l.bits.toNat := by
        have : ¬ l.bits.toNat < 15 := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
        omega
      exact Wp.mono (root_trace_wp hc A msg m l i o i hls hAsz ho258 hbroke hi6 (by omega) (by omega) hb (by omega))
        (fun _ _ result => ⟨by trivial, result⟩)
  obtain ⟨l', after, run, sameStream, result⟩ := trace
  have safe := Wp.at_run (inflate_fast_body_step_safe e c A msg m l i o hp) run
  exact ⟨l', after, run, safe, sameStream, result⟩

end Zlib.Inffast.Proofs.LengthTraceProof

namespace Zlib.Inffast.Proofs
open Zlib.Inffast.Spec
/-- The selected literal/length leaf and its actual four-way result are
retained by the complete fast body on the existing safety domain. -/
theorem actual_body_retains_selected_length : LengthTrace.Goal.actual_body_retains_selected_length :=
  LengthTraceProof.actual_body_retains_selected_length
end Zlib.Inffast.Proofs
