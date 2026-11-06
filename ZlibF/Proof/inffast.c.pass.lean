import ZlibF.Proof.«inffast.c.dist»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

variable {e : Env} {c : Ctx}

set_option maxHeartbeats 1000000 in
/-- One pass of the block at `dodist:`. Either it follows a link (`againD`), or it ends the distance block. -/
theorem dodist_pass (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o d k : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd k) (hk : k < e.DCA.size)
    (hEb : (e.DCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.DCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : DistClass e (e.DCA.getD k default))
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat + d)) :
    Wp (dodist c l) (e.heap A msg m) (fun l' h' =>
      (l'.againD = true ∧ l'.broke = false ∧ h' = e.heap A msg m ∧
        ((e.DCA.getD k default).op &&& 16 = 0 ∧ (e.DCA.getD k default).op &&& 64 = 0) ∧
        ∃ j, j < 2 ^ (e.DCA.getD k default).op.toNat ∧
          j = (l.hold.toNat / 2 ^ (e.DCA.getD k default).bits.toNat) % 2 ^ (e.DCA.getD k default).op.toNat ∧
          l'.here = .ref e.rd (e.od + (e.DCA.getD k default).val.toNat + j) ∧ LS e l' i o ∧
          Sg e l'.hold.toNat l'.bits.toNat i = (Sg e l.hold.toNat l.bits.toNat i).drop (e.DCA.getD k default).bits.toNat ∧
          l'.bits.toNat = l.bits.toNat - (e.DCA.getD k default).bits.toNat ∧
          l'.len = l.len ∧ l'.out = l.out ∧ l'.dist = l.dist ∧ l'.againL = l.againL) ∨
      DistEnd e A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop (e.DCA.getD k default).bits.toNat) i o l.len.toNat
        (e.DCA.getD k default) l' h') := by
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
    have key := (dodistBase_wp hc A msg m
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
    obtain ⟨i', xv, rest, hi1, hi2, hr, hagD, hres⟩ := hq
    refine Or.inr ⟨fun hl => hb16' hl.1, hagD, ?_⟩
    rcases hres with ⟨hb, hls', hsg, hh⟩ | ⟨hb, hls', p, hh⟩
    · refine Or.inl ⟨i', xv, rest, hi1, hi2, ?_, hb, hls', hsg, ?_⟩
      · have : (E.op.toUInt32 &&& 15).toNat = (E.op &&& 15).toNat := mask15 _
        rw [this] at hr
        rw [hsg1'] at hr
        exact hr
      · rw [hh]; simp only [hv]
    · exact Or.inr ⟨i', p, hi1, hi2, hb, hls', hh⟩
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
      refine Wp.pure' (Or.inl ⟨rfl, hbroke, rfl, ⟨hb16', hb64'⟩, j, hjlt, by rw [← hjd, u64_shr (by omega), hEbn, toNat32],  rfl, LS.congr hls1 rfl rfl rfl rfl, hsg1',
        (by show (l.bits - E.bits.toUInt32).toNat = _; rw [u32_toNat_sub (by omega), hEbn]), rfl, rfl, rfl, rfl⟩)
    · simp only [hb16, hb64, ite_false, Bool.false_eq_true]
      obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid distance code" (by decide +kernel)
      refine Wp.bindE hip (Wp.pure' (Or.inr ⟨fun hl => (by rw [mask64] at hb64; simpa using hb64 : E.op &&& 64 ≠ 0) hl.2, rfl, Or.inr ⟨i, Ptr.ref (BRef.str ip) 0, Nat.le_refl _, by omega, rfl,
        LS.congr hls1 rfl rfl rfl rfl, rfl⟩⟩))

end Zlib.Inffast.Proofs
