import ZlibF.Proof.«infback.c.inv»

/-!
# infback.c: `PULL()` with the call-back, on the invariant of the loop

`PULL_run` is the part of `PULLBYTE_run` before the byte is taken. `STORED` and the copy loops use `PULL` alone.
-/

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-- **`PULL()` with the call-back.** No fault. Either input is left afterwards (`ok`, `have /= 0`; `in` is called only when the
chunk was used up; only the input registers change), or `in` returned 0 and the call ends with `goto inf_leave`,
`Z_BUF_ERROR`. The call-back changed only its own blocks, `R` holds again, the registers describe the chunk in use, and the
input still to be read never grows. -/
theorem PULL_run (c : BCtx) {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {h : Heap} {l : IL} {bs : List UInt8} (B : BIn ownI h l bs) (hR : R h) :
    ∃ r l' h' bs', runX (PULL c) l h = .ok ((r, l'), h') ∧ CbFrame ownI h h' ∧ R h' ∧ BIn ownI h' l' bs' ∧
      (r = .ok () → l'.have_ ≠ 0 ∧ InShape l l') ∧ (r = .error Ex.leave → l' = EofRegs l) ∧
      (∀ e, r = .error e → e = Ex.leave) ∧ (l'.bits = l.bits ∧ l'.hold = l.hold) ∧ phi μ h' l' ≤ phi μ h l := by
  by_cases hz : l.have_ = 0
  · have hz0 : l.have_.toNat = 0 := by rw [hz]; rfl
    obtain ⟨n, nx, h', he, fr, hR', hbuf⟩ := hK.inOk h l.next hR
    have hs := hF.step h l.next n nx h' hR he
    by_cases hn : n = 0
    · subst hn
      refine ⟨.error Ex.leave, EofRegs l, h', [], PULL_noinput hz he, fr, hR',
        ⟨⟨by simp [EofRegs], Or.inl rfl, B.bit.hold_lt⟩, Or.inl rfl⟩, (fun e => by cases e), fun _ => rfl,
        (fun e he => by cases he; rfl), ⟨rfl, rfl⟩, ?_⟩
      simp only [phi, EofRegs]
      simp only [UInt32.toNat_zero] at hs ⊢
      omega
    · obtain ⟨bb, off, a, hnx, hown, ha, hle⟩ := hbuf hn
      have hn1 : ({ l with have_ := n, next := nx } : IL).have_ ≠ 0 := hn
      have hlen : ((a.toList.drop off).take n.toNat).length = n.toNat := by simp; omega
      refine ⟨.ok (), { l with have_ := n, next := nx }, h', (a.toList.drop off).take n.toNat, PULL_chunk hz hn he, fr, hR',
        ⟨⟨hlen.symm, Or.inr ⟨.blk bb, a, off, by simp [hnx], ha, by omega, by rw [hlen]⟩, B.bit.hold_lt⟩,
          Or.inr ⟨bb, off, by simp [hnx], hown⟩⟩, fun _ => ⟨hn1, rfl⟩, (fun e => by cases e), (fun e he => by cases he), ⟨rfl, rfl⟩, ?_⟩
      simp only [phi]
      omega
  · refine ⟨.ok (), l, h, bs, PULL_have hz, CbFrame.refl _ _, hR, B, fun _ => ⟨hz, InShape.refl l⟩, (fun e => by cases e),
      (fun e he => by cases he), ⟨rfl, rfl⟩, Nat.le_refl _⟩

end Zlib.Infback.Proofs
