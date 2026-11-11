import ZlibF.Proof.«inffast.c.pass»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

theorem fuel_split2 : ∃ n, fuel = n + 1 + 1 := ⟨fuel - 2, by unfold fuel; omega⟩

theorem cdoWhile_one {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} {s s1 s1' : σ} {h h1 : Heap}
    (e1 : body s h = .ok (s1, h1)) (c1 : cond s1 h1 = .ok ((false, s1'), h1)) :
    cdoWhile body cond s h = .ok (s1', h1) := by
  obtain ⟨n, hn⟩ := fuel_split2
  unfold cdoWhile
  rw [hn]
  simp [cdoWhile.go, e1, c1]

theorem cdoWhile_two {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} {s s1 s1' s2 s2' : σ} {h h1 h2 : Heap}
    (e1 : body s h = .ok (s1, h1)) (c1 : cond s1 h1 = .ok ((true, s1'), h1))
    (e2 : body s1' h1 = .ok (s2, h2)) (c2 : cond s2 h2 = .ok ((false, s2'), h2)) :
    cdoWhile body cond s h = .ok (s2', h2) := by
  obtain ⟨n, hn⟩ := fuel_split2
  unfold cdoWhile
  rw [hn]
  simp [cdoWhile.go, e1, c1, e2, c2]


variable {e : Env} {c : Ctx}

theorem DistLeaf_class (d : Nat) (E : Code) (h : DistLeaf d E) : (E.op &&& 16 ≠ 0 ∧ (E.op &&& 15).toNat ≤ 13 ∧ 1 ≤ E.val.toNat) ∨
    (E.op &&& 16 = 0 ∧ E.op &&& 64 ≠ 0) := h.2

/-- A root entry of the distance table is either a leaf or a link whose second level is in range. -/
theorem distRoot (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat) (kidx : Nat) (hk : kidx < 2 ^ e.s0.distbits.toNat) :
    e.od + kidx < e.DCA.size ∧
    ((DistLink (e.DCA.getD (e.od + kidx) default) → LinkOK DistLeaf e.DCA e.od (e.DCA.getD (e.od + kidx) default)) ∧
     (¬ DistLink (e.DCA.getD (e.od + kidx) default) → DistLeaf 0 (e.DCA.getD (e.od + kidx) default))) := by
  obtain ⟨_, hsz, hall⟩ := hts
  refine ⟨by omega, ?_⟩
  have := hall kidx hk
  by_cases hl : DistLink (e.DCA.getD (e.od + kidx) default)
  · rw [ite_eq_left hl] at this
    exact ⟨fun _ => this, fun h => absurd hl h⟩
  · rw [ite_eq_right hl] at this
    exact ⟨fun h => absurd h hl, fun _ => this⟩

theorem distClass_of (E : Code) (hl : DistLink E → LinkOK DistLeaf e.DCA e.od E) (hn : ¬ DistLink E → DistLeaf 0 E) :
    DistClass e E := by
  by_cases h : DistLink E
  · have := hl h
    exact Or.inr (Or.inl ⟨h.1, h.2, this.2.1, this.2.2.1, this.2.2.2.1⟩)
  · have := (hn h).2
    rcases this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)


/-- The entry on which a distance lookup ends and the number of bits it consumes, for the hold value `H` and the root
index `kidx`: a root leaf, or a root link and a leaf of its second level. -/
def DistLook (e : Env) (H kidx : Nat) (E : Code) (cb : Nat) : Prop :=
  (e.DCA.getD (e.od + kidx) default = E ∧ cb = E.bits.toNat ∧ ¬ DistLink E) ∨
  (∃ E0 j, e.DCA.getD (e.od + kidx) default = E0 ∧ DistLink E0 ∧ j < 2 ^ E0.op.toNat ∧
     j = (H / 2 ^ E0.bits.toNat) % 2 ^ E0.op.toNat ∧ e.DCA.getD (e.od + E0.val.toNat + j) default = E ∧
     cb = E0.bits.toNat + E.bits.toNat ∧ E0.bits.toNat + E.bits.toNat ≤ 15 ∧ ¬ DistLink E)

theorem dodistLoop_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o kidx : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat) (hk : kidx < 2 ^ e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd (e.od + kidx)) (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat))
    (hfr : e.InputFrame A i) :
    Wp (cdoWhile (dodist c) (fun l => pure (l.againD, l)) l) (e.heap A msg m) (fun l' h' =>
      ∃ E cb, cb ≤ 15 ∧ DistLook e l.hold.toNat kidx E cb ∧
        DistEnd e A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop cb) i o l.len.toNat E l' h') := by
  obtain ⟨hksz, hlk, hnl⟩ := distRoot hts kidx hk
  have hcl0 := distClass_of (e := e) _ hlk hnl
  have hEd0 : (e.DCA.getD (e.od + kidx) default).bits.toNat + 0 ≤ 15 := by
    by_cases hl : DistLink (e.DCA.getD (e.od + kidx) default)
    · have := (hlk hl).1; omega
    · have := (hnl hl).1; omega
  obtain ⟨l1, h1, e1, hq1⟩ := dodist_pass hc A msg m l i o 0 (e.od + kidx) hls hA ho hAb hbroke hlen hhere hksz
    (by omega) hEd0 hcl0 (by simpa using hpull) (hfr.mono (by omega))
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
        · exact Or.inr ⟨h.1, by omega⟩) (hfr.mono (by omega))
    rcases hq2 with ⟨hag2, -, -, ⟨hl16', hl64'⟩, -⟩ | hend2
    · rcases hleaf.2 with h | h
      · exact absurd hl16' h.1
      · exact absurd hl64' h.2
    · have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 (e.heap A msg m) = .ok ((true, l1), e.heap A msg m) := by simp [hag]
      have c2 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l2 h2 = .ok ((false, l2), h2) := by simp [hend2.2.1]
      have e1' : dodist c l (e.heap A msg m) = .ok (l1, e.heap A msg m) := e1
      refine Wp.of_eq (cdoWhile_two e1' c1 e2 c2) ?_
      refine ⟨e.DCA.getD (e.od + E0.val.toNat + j) default, E0.bits.toNat + (e.DCA.getD (e.od + E0.val.toNat + j) default).bits.toNat, by have := hleaf.1; omega, ?_, ?_⟩
      · refine Or.inr ⟨E0, j, hE0, hlink, hjlt, ?_, rfl, rfl, by have := hleaf.1; omega, ?_⟩
        · rw [hjd]
        · intro hl; rcases hleaf.2 with h | h
          · exact absurd hl.1 h.1
          · exact absurd hl.2 h.2
      · have := hend2
        rw [hlen1] at this
        have hd : (Sg e l.hold.toNat l.bits.toNat i).drop (E0.bits.toNat + (e.DCA.getD (e.od + E0.val.toNat + j) default).bits.toNat) =
            ((Sg e l.hold.toNat l.bits.toNat i).drop E0.bits.toNat).drop (e.DCA.getD (e.od + E0.val.toNat + j) default).bits.toNat := by
          rw [List.drop_drop]
        rw [hd, ← hsg1]
        exact this
  · -- the first pass ended the block
    have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 h1 = .ok ((false, l1), h1) := by simp [hag]
    refine Wp.of_eq (cdoWhile_one e1 c1) ?_
    refine ⟨E0, E0.bits.toNat, by omega, Or.inl ⟨hE0, rfl, hNL⟩, ⟨hNL, hag, hend⟩⟩

end Zlib.Inffast.Proofs
