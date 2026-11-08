import ZlibF.Proof.«inflate.c.input-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate

/-- The actual NEEDBITS loop can return normally or leave on exhausted input.
The companion result retains all existing bit-stream facts and rules out
an arbitrary direct API return from this macro. -/
theorem NEEDBITS_run_cursor {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) (n : UInt32) (hn : n.toNat ≤ 49) :
    ∃ r l' j, runX (NEEDBITS n) l h = .ok ((r, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧ l'.bits.toNat = l.bits.toNat + 8 * j ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits } ∧
      l'.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧ (n.toNat ≤ l.bits.toNat → l' = l) ∧
      (r = .ok () → n.toNat ≤ l'.bits.toNat) ∧
      (r = .error Ex.leave → j = bs.length ∧ l'.have_ = 0 ∧ l'.bits.toNat < n.toNat) ∧
      (r = .ok () ∨ r = .error Ex.leave) ∧ l'.next = inputAdvance l.next j := by
  have hlen : bs.length < 2 ^ 32 := by
    have := B.have_eq; have := UInt32.toNat_lt l.have_; simp at *; omega
  let Inv : Nat → IL → Heap → Prop := fun k current heap =>
    heap = h ∧ ∃ j, (NBase h l bs n current j ∧ current.next = inputAdvance l.next j) ∧
      k = (if current.bits.toNat < n.toNat then min ((n.toNat - current.bits.toNat + 7) / 8) (bs.length - j + 1) else 0)
  have key := xwhileBrk_run (cond := (do return (← get).bits < n : X Bool)) (body := (do PULLBYTE; pure false : X Bool))
    Inv
    (fun r l1 h1 => h1 = h ∧ ∃ j, (NBase h l bs n l1 j ∧ l1.next = inputAdvance l.next j) ∧ (r = .ok () → n.toNat ≤ l1.bits.toNat) ∧
      (r = .error Ex.leave → j = bs.length ∧ l1.have_ = 0 ∧ l1.bits.toNat < n.toNat) ∧
      (r = .ok () ∨ r = .error Ex.leave))
    (fun k l1 h1 hP => by
      obtain ⟨hh, j, hb, hk⟩ := hP
      subst hh
      have hnl : l1.bits.toNat < n.toNat := by
        by_cases hc : l1.bits.toNat < n.toNat
        · exact hc
        · rw [if_neg hc] at hk; omega
      have hnl' : l1.bits < n := UInt32.lt_iff_toNat_lt.mpr hnl
      obtain ⟨⟨hj, hB, hS, hbits, hshape, hmax, hz⟩, cursor⟩ := hb
      have hcond : runX (do return (← get).bits < n : X Bool) l1 h1 = .ok ((.ok true, l1), h1) := by
        rw [runX_cond_lt]; simp [hnl']
      refine ⟨l1, h1, hcond, ?_⟩
      by_cases h0 : l1.have_ = 0
      · refine ⟨.error Ex.leave, l1, h1, ?_, ?_⟩
        · rw [runX_bind, PULLBYTE_zero h0]
        · have := hB.have_eq
          have h00 : l1.have_.toNat = 0 := by rw [h0]; rfl
          simp only [List.length_drop] at this
          refine ⟨rfl, j, ⟨⟨hj, hB, hS, hbits, hshape, hmax, hz⟩, cursor⟩, (fun e => nomatch e), (fun _ => ⟨by omega, h0, hnl⟩), Or.inr rfl⟩
      · have hlenj : j < bs.length := by
          have := hB.have_eq
          simp only [List.length_drop] at this
          apply Decidable.byContradiction
          intro hc
          apply h0
          have : l1.have_.toNat = 0 := by omega
          exact UInt32.toNat_inj.mp (by simpa using this)
        have hdrop : bs.drop j = bs[j] :: bs.drop (j + 1) := List.drop_eq_getElem_cons hlenj
        rw [hdrop] at hB hS
        obtain ⟨nx, hrun, hB2, hS2, hb2, nextCursor⟩ := PULLBYTE_succ_cursor hB (by omega)
        refine ⟨.ok false, pulled l1 bs[j] nx, h1, ?_, ?_⟩
        · rw [runX_bind, hrun]; rfl
        · refine ⟨rfl, j + 1, ⟨⟨by omega, hB2, ?_, by omega, ?_, by omega, by omega⟩, ?_⟩, ?_⟩
          · rw [hS2, hS]
          · rw [hshape]; simp [pulled]
          · change nx = inputAdvance l.next (j + 1)
            rw [nextCursor, cursor, inputAdvance_add]
          · rw [if_pos hnl] at hk
            rw [hb2]
            split <;> omega)

    (fun l1 h1 hP => by
      obtain ⟨hh, j, hb, hk⟩ := hP
      subst hh
      have hnl : ¬ l1.bits.toNat < n.toNat := by intro hl; rw [if_pos hl] at hk; omega
      refine ⟨l1, h1, by rw [runX_cond_lt]; simp [UInt32.lt_iff_toNat_lt, hnl], rfl, j, hb, ?_, ?_, Or.inl rfl⟩
      · intro _
        omega
      · intro e; cases e)
    (k := (if l.bits.toNat < n.toNat then min ((n.toNat - l.bits.toNat + 7) / 8) (bs.length + 1) else 0)) (l := l) (h := h)
    ⟨rfl, 0, ⟨⟨by omega, by simpa using B, by simp [stream], by simp, by simp, by omega, fun _ => rfl⟩,
      (inputAdvance_zero l.next).symm⟩, by simp⟩
    (by unfold fuel; split <;> omega)
  obtain ⟨r, l', h', hr, rfl, j, hb, hq1, hq2, kinds⟩ := key
  obtain ⟨⟨hj, hB, hS, hbits, hshape, hmax, hz⟩, cursor⟩ := hb
  refine ⟨r, l', j, by unfold NEEDBITS xwhile; exact hr, hj, hB, hS, hbits, hshape, hmax, ?_, hq1, hq2, kinds, cursor⟩
  intro hge
  by_cases hj0 : j = 0
  · exact hz hj0
  · exfalso; omega

/-- Projection retaining the original exhaustive NEEDBITS outcomes. -/
theorem NEEDBITS_run_complete {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) (n : UInt32) (hn : n.toNat ≤ 49) :
    ∃ r l' j, runX (NEEDBITS n) l h = .ok ((r, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧ l'.bits.toNat = l.bits.toNat + 8 * j ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits } ∧
      l'.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧ (n.toNat ≤ l.bits.toNat → l' = l) ∧
      (r = .ok () → n.toNat ≤ l'.bits.toNat) ∧
      (r = .error Ex.leave → j = bs.length ∧ l'.have_ = 0 ∧ l'.bits.toNat < n.toNat) ∧
      (r = .ok () ∨ r = .error Ex.leave) := by
  obtain ⟨result, regs, used, run, usedBound, inv, bits, count, shape, bitBound,
    noPull, enough, empty, kinds, _⟩ := NEEDBITS_run_cursor B n hn
  exact ⟨result, regs, used, run, usedBound, inv, bits, count, shape, bitBound,
    noPull, enough, empty, kinds⟩

end Zlib.Inflate.Proofs
