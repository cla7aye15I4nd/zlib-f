import ZlibF.Proof.«inffast.c.body»

/-!
# inffast.c: the message at end of block

The original StepPost is unchanged. These derived execution lemmas retain
that TYPE does not overwrite the message; only the BAD paths do so.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec
variable {e : Env} {c : Ctx}

/-- The actual length branch preserves the message when it finishes in TYPE. -/
theorem dolenLen_message_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hbroke : l.broke = false) (hagain : l.againL = false) (hx : l.op.toNat ≤ 5)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb2 : i = s + 2 → 1 ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (dolenLen c l) (e.heap A msg m) (fun l' h' => ∃ B p q, h' = e.heap B p q ∧ l'.againL = false ∧ (q = TYPE → p = msg)) := by
  have hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hAb : A.size < 2 ^ 63 := by rw [hAsz]; exact e.hAbig
  obtain ⟨l', h', hr, hq⟩ := dolenLen_wp hc A msg m l i o s e.hdt hls hA ho hAb hbroke hx hlen hs6 hT hb2 (hfr.mono (by omega))
  refine ⟨l', h', hr, ?_⟩
  have hag : l'.againL = false := (dolenLen_againL hr).trans hagain
  obtain ⟨i2, lx, S1, _, _, hrb, i3, H3, b3, E, cb, _, _, _, _, _, _, _, _, hend⟩ := hq
  rcases hend.2.2 with hgood | hbad
  · obtain ⟨i', xv, rest, _, _, _, hb, hls', _, hh⟩ := hgood
    exact ⟨_, msg, m, hh, hag, fun _ => rfl⟩
  · obtain ⟨i', p, _, _, hb, hls', hh⟩ := hbad
    exact ⟨A, p, BAD, hh, hag, fun h => False.elim ((by decide : BAD ≠ TYPE) h)⟩

set_option maxHeartbeats 1000000 in
/-- One actual length-table pass either follows its one permitted link or
returns a concrete heap whose TYPE mode preserves the message. -/
theorem dolen_pass_message_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s d k : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat + d) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat + d)
    (hhere : l.here = .ref e.rl k) (hk : k < e.LCA.size)
    (hEb : (e.LCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.LCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : (LenLink (e.LCA.getD k default) ∧ LinkOK LenLeaf e.LCA e.ol (e.LCA.getD k default)) ∨
      LenLeaf d (e.LCA.getD k default))
    (hfr : e.InputFrame A i) :
    Wp (dolen c l) (e.heap A msg m) (fun l' h' =>
      (l'.againL = true ∧ l'.broke = false ∧ h' = e.heap A msg m ∧
        LenLink (e.LCA.getD k default) ∧
        ∃ j, j < 2 ^ (e.LCA.getD k default).op.toNat ∧
          l'.here = .ref e.rl (e.ol + (e.LCA.getD k default).val.toNat + j) ∧
          LS e l' i o ∧ l'.bits.toNat = l.bits.toNat - (e.LCA.getD k default).bits.toNat) ∨
      (∃ B p q, h' = e.heap B p q ∧ l'.againL = false ∧ (q = TYPE → p = msg))) := by
  have hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hkE : e.LCA[k]'hk = e.LCA.getD k default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.LCA.getD k default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A msg m) hk
  have hEbn : (e.LCA.getD k default).bits.toUInt32.toNat = (e.LCA.getD k default).bits.toNat := toNat32 _
  have hEb64 : (e.LCA.getD k default).bits.toUInt32.toUInt64.toNat = (e.LCA.getD k default).bits.toNat := by simp [toNat32]
  have hls1 := hls.dropL (e.LCA.getD k default).bits.toUInt32 (by omega) (by omega)
  rw [dolen_eq_len]
  dsimp only
  refine Wp.bindO hld ?_
  refine Wp.bindO (shr64_ok (x := l.hold) (by omega)) ?_
  refine Wp.bindO hld ?_
  generalize e.LCA.getD k default = E at *
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
    · exact Wp.pure' (Or.inr ⟨_, msg, m, rfl, rfl, fun _ => rfl⟩)
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
      refine Wp.mono (dolenLen_message_wp hc A msg m
        { in_ := l.in_, out := l.out, hold := l.hold >>> E.bits.toUInt32.toUInt64, bits := l.bits - E.bits.toUInt32,
          here := l.here, op := E.op.toUInt32 &&& 15, len := E.val.toUInt32, dist := l.dist, from_ := l.from_,
          broke := l.broke, againL := false, againD := l.againD }
        i o s (LS.congr hls1 rfl rfl rfl rfl) hAsz ho hbroke rfl
        (by rw [mask15]; exact hbase.1) (by simpa [mask15] using hbase.2)
        hs6 hsi hT (by intro hi; have := hbi2 hi; show 1 ≤ (l.bits - E.bits.toUInt32).toNat
                       rw [u32_toNat_sub (by omega), hEbn]; omega) (hfr.mono (by omega))) ?_
      exact fun _ _ h => Or.inr h
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
        refine Wp.pure' (Or.inl ⟨rfl, hbroke, rfl, hl, j, hjlt, rfl,
          LS.congr hls1 rfl rfl rfl rfl, ?_⟩)
        rw [u32_toNat_sub (by omega), hEbn]
      · simp only [hz, hb16, hb64, ite_false, Bool.false_eq_true]
        by_cases hb32 : (E.op.toUInt32 &&& 32 != 0) = true
        · simp only [hb32, ite_true]
          refine Wp.bindE (e.heap_ldstate hc A msg m) ?_
          refine Wp.bindE (e.heap_stmode hc A msg m TYPE _ rfl) ?_
          exact Wp.pure' (Or.inr ⟨A, msg, TYPE, rfl, rfl, fun _ => rfl⟩)
        · simp only [hb32, ite_false, Bool.false_eq_true]
          obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid literal/length code" (by decide +kernel)
          refine Wp.bindE hip ?_
          exact Wp.pure' (Or.inr ⟨A, .ref (BRef.str ip) 0, BAD, rfl, rfl,
            fun h => False.elim ((by decide : BAD ≠ TYPE) h)⟩)

/-- The actual `dolen` root/link loop ends after at most two passes. -/
theorem dolenLoop_message_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s kidx : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat)
    (hk : kidx < 2 ^ e.s0.lenbits.toNat) (hhere : l.here = .ref e.rl (e.ol + kidx))
    (hfr : e.InputFrame A i) :
    Wp (cdoWhile (dolen c) (fun l => pure (l.againL, l)) l) (e.heap A msg m)
      (fun l' h' => ∃ B p q, h' = e.heap B p q ∧ l'.againL = false ∧ (q = TYPE → p = msg)) := by
  have hts := e.hlt
  obtain ⟨hR, hsz, hall⟩ := hts
  have hksz : e.ol + kidx < e.LCA.size := by omega
  have hclass : (LenLink (e.LCA.getD (e.ol + kidx) default) ∧
      LinkOK LenLeaf e.LCA e.ol (e.LCA.getD (e.ol + kidx) default)) ∨
      LenLeaf 0 (e.LCA.getD (e.ol + kidx) default) := by
    have hh := hall kidx hk
    by_cases hl : LenLink (e.LCA.getD (e.ol + kidx) default)
    · rw [ite_eq_left hl] at hh; exact Or.inl ⟨hl, hh⟩
    · rw [ite_eq_right hl] at hh; exact Or.inr hh
  have hEd0 : (e.LCA.getD (e.ol + kidx) default).bits.toNat + 0 ≤ 15 := by
    rcases hclass with h | h
    · exact h.2.1
    · exact h.1
  obtain ⟨l1, h1, e1, hq1⟩ := dolen_pass_message_wp hc A msg m l i o s 0 (e.ol + kidx) hls hAsz ho hbroke
    hs6 hsi hT (by omega) (by intro hi; have := hbi2 hi; omega) hhere hksz (by omega) hEd0 hclass (hfr.mono (by omega))
  generalize hE0 : e.LCA.getD (e.ol + kidx) default = E0 at hq1 hclass hEd0
  rcases hq1 with ⟨hag, hbr, hh, hlink, j, hjlt, hhere1, hls1, hb1⟩ | hend
  · subst hh
    have hlk : LinkOK LenLeaf e.LCA e.ol E0 := by
      rcases hclass with h | h
      · exact h.2
      · rcases h.2 with h0 | h | h
        · exact False.elim (hlink.1 h0)
        · exact False.elim (h.1 hlink.2.1)
        · exact False.elim (h.2 hlink.2.2)
    have hleaf := hlk.2.2.2.2 j hjlt
    have hk2 : e.ol + E0.val.toNat + j < e.LCA.size := by have := hlk.2.2.2.1; omega
    obtain ⟨l2, h2, e2, hq2⟩ := dolen_pass_message_wp hc A msg m l1 i o s E0.bits.toNat (e.ol + E0.val.toNat + j)
      hls1 hAsz ho hbr hs6 hsi hT (by omega) (by intro hi; have := hbi2 hi; omega)
      hhere1 hk2 (by have := hleaf.1; omega) hleaf.1 (Or.inr hleaf) (hfr.mono (by omega))
    rcases hq2 with ⟨_, _, _, hl2, _⟩ | hend2
    · rcases hleaf.2 with h0 | h | h
      · exact False.elim (hl2.1 h0)
      · exact False.elim (h.1 hl2.2.1)
      · exact False.elim (h.2 hl2.2.2)
    · have c1 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l1 (e.heap A msg m) =
          .ok ((true, l1), e.heap A msg m) := by simp [hag]
      have c2 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l2 h2 =
          .ok ((false, l2), h2) := by obtain ⟨_, _, _, _, hf, _⟩ := hend2; simp [hf]
      exact Wp.of_eq (cdoWhile_two e1 c1 e2 c2) hend2
  · have c1 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l1 h1 =
        .ok ((false, l1), h1) := by obtain ⟨_, _, _, _, hf, _⟩ := hend; simp [hf]
    exact Wp.of_eq (cdoWhile_one e1 c1) hend

/-- Root-table lookup followed by the actual length root/link loop. -/
theorem dolenRoot_message_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o s : Nat) (hls : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hbroke : l.broke = false)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hsi : s ≤ i) (hT : i ≤ s + 2)
    (hb15 : 15 ≤ l.bits.toNat) (hbi2 : i = s + 2 → 16 ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (do
      let here ← c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat
      cdoWhile (dolen c) (fun l => pure (l.againL, l)) {l with here})
      (e.heap A msg m) (fun l' h' => ∃ B p q, h' = e.heap B p q ∧ l'.againL = false ∧ (q = TYPE → p = msg)) := by
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
  · exact dolenLoop_message_wp hc A msg m _ i o s _ (LS.congr hls rfl rfl rfl rfl) hAsz ho hbroke
      hs6 hsi hT hb15 hbi2 hmod rfl (hfr.mono (by omega))

/-- A real fast-body execution that finishes in TYPE keeps the stream's
original message. This supplements, without changing, the checked StepPost. -/
theorem inflate_fast_body_type_message (e : Env) (c : Ctx) (A : Array UInt8)
    (msg : BPtr) (m : UInt32) (l : L) (i o : Nat) (hp : StepPre e c A l i o) :
    Wp (inflate_fast_body c l) (e.heap A msg m)
      (fun l' h' => ∃ B p q, h' = e.heap B p q ∧ l'.againL = false ∧ (q = TYPE → p = msg)) := by
  rcases hp with ⟨hc, hls, hAsz, hi6, ho258, hbroke, hfr⟩
  unfold inflate_fast_body
  by_cases h1 : l.bits < 15
  · simp only [h1, ite_true]
    have hb : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl1 := hls.pullL (by omega) hiin
    have hb1 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
    have hb1' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at hb1 ⊢; omega
    refine Wp.bindO (pull_run e _ _ (i + 1) o hl1 hb1' hi2 (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl2 := hl1.pullL hb1' hi2
    have hb2 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)))
      (e.IN.getD (i + 1) 0) (.ref (BRef.blk e.ib) (i + 1 + 1)) hl1.hb
    exact dolenRoot_message_wp hc A msg m _ (i + 1 + 1) o i hl2 hAsz ho258 hbroke hi6 (by omega) (by omega)
      (by simp only [pullL] at hb1 hb2 ⊢; omega)
      (by intro _; simp only [pullL] at hb1 hb2 ⊢; omega) (hfr.mono (by omega))
  · simp only [h1, ite_false]
    have hb : 15 ≤ l.bits.toNat := by
      have : ¬ l.bits.toNat < 15 := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
      omega
    exact dolenRoot_message_wp hc A msg m l i o i hls hAsz ho258 hbroke hi6 (by omega) (by omega) hb (by omega) (hfr.mono (by omega))

end Zlib.Inffast.Proofs
