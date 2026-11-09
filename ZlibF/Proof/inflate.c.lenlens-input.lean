import ZlibF.Proof.«inflate.c.main.table6»
import ZlibF.Proof.«inflate.c.bits-complete»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The actual three-bit length read retains its input cursor and bit cap. -/
theorem llBody_run_cursor {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {t : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (ht : h.istates zs = some t) (hsz : t.lens.size = 320) (hH : t.«have».toNat < 19)
    (B : BitInv h l bs) :
    ∃ rr l' j, runX (NEEDBITS 3) l h = .ok ((rr, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits } ∧
      (rr = .error Ex.leave → l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 3 ∧
        runX (llBody c) l h = .ok ((.error Ex.leave, l'), h)) ∧
      (rr = .ok () → 3 ≤ l'.bits.toNat ∧
        runX (llBody c) l h = .ok ((.ok (), { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 }),
          setI h zs { t with «have» := t.«have» + 1, lens := t.lens.set! (orderNat t.«have».toNat) (l'.hold.toUInt32 &&& 7).toUInt16 })) ∧ l'.next = inputAdvance l.next j ∧ l'.bits.toNat ≤ max l.bits.toNat 10 := by
  obtain ⟨rr, regs, used, read, bound, inv, stream, shape, wait, ready⟩ := llBody_run hc ht hsz hH B
  obtain ⟨rr2, regs2, used2, read2, bound2, inv2, _, _, _, bits, _, _, _, _, cursor⟩ :=
    NEEDBITS_run_cursor B 3 (by decide)
  rw [read] at read2
  cases read2
  have same : used2 = used := by
    have one := inv.have_eq
    have two := inv2.have_eq
    rw [List.length_drop] at one two
    omega
  subst used2
  exact ⟨rr, regs, used, read, bound, inv, stream, shape, wait, ready, cursor, bits⟩

/-- The complete actual LENLENS reading loop retains the exact input
cursor and its bit cap through every successful prefix extension. -/
theorem ll1_run_cursor {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hsz : s.lens.size = 320)
    (hnc : s.ncode.toNat ≤ 19) (hhn : s.«have».toNat ≤ s.ncode.toNat) (B : BitInv h l bs) :
    ∃ r l' j, runX (xwhile (llCond c) (llBody c)) l h =
        .ok ((r, l'), setI h zs (llSt s (stream l bs) (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)))) ∧
      j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = (stream l bs).drop (3 * min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)) ∧
      TcRegShape l l' ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) < s.ncode.toNat - s.«have».toNat →
        r = .error Ex.leave ∧ l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 3) ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) = s.ncode.toNat - s.«have».toNat → r = .ok ()) ∧ l'.next = inputAdvance l.next j ∧
      l'.bits.toNat ≤ max l.bits.toNat 10 := by
  obtain ⟨n, hn⟩ : ∃ n, n = s.ncode.toNat - s.«have».toNat := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = stream l bs := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = min n (S.length / 3) := ⟨_, rfl⟩
  rw [← hn, ← hS, ← hM]
  have key := xwhileBrk_run (cond := llCond c) (body := (do llBody c; pure false : X Bool))
    (fun k l1 h1 => ∃ m j, k + m = n ∧ m ≤ M ∧ j ≤ bs.length ∧ h1 = setI h zs (llSt s S m) ∧
      BitInv h l1 (bs.drop j) ∧ stream l1 (bs.drop j) = S.drop (3 * m) ∧ TcRegShape l l1 ∧ l1.next = inputAdvance l.next j ∧ l1.bits.toNat ≤ max l.bits.toNat 10)
    (fun r l1 h1 => ∃ j, j ≤ bs.length ∧ h1 = setI h zs (llSt s S M) ∧ BitInv h l1 (bs.drop j) ∧
      stream l1 (bs.drop j) = S.drop (3 * M) ∧ TcRegShape l l1 ∧
      (M < n → r = .error Ex.leave ∧ l1.have_ = 0 ∧ j = bs.length ∧ l1.bits.toNat < 3) ∧ (M = n → r = .ok ()) ∧ l1.next = inputAdvance l.next j ∧ l1.bits.toNat ≤ max l.bits.toNat 10)
    (fun k l1 h1 hP => by
      obtain ⟨m, j, hk, hmM, hj, hh1, B1, hS1, hsh1, cursor, bitBound⟩ := hP
      subst hh1
      have hmn : m < n := by omega
      have hb19 : s.«have».toNat + m < 19 := by omega
      have hht := llSt_have s S m (by omega)
      have ht : (setI h zs (llSt s S m)).istates zs = some (llSt s S m) := by simp
      have hszt : (llSt s S m).lens.size = 320 := by simp [llSt, lensRead_size, hsz]
      have hHt : (llSt s S m).«have».toNat < 19 := by omega
      have hcond : runX (llCond c) l1 (setI h zs (llSt s S m)) = .ok ((.ok true, l1), setI h zs (llSt s S m)) := by
        unfold llCond
        rw [hc]
        simp only [runX_bind, runX_lift, ldI_eq, ht, runX_pure]
        have : (llSt s S m).«have» < (llSt s S m).ncode := by
          rw [UInt32.lt_iff_toNat_lt, hht]
          show _ < s.ncode.toNat
          omega
        simp [this]
      obtain ⟨rr, l', jn, hrun, hjn, B', hS', hshape, hleave, hok, stepCursor, stepBits⟩ :=
        llBody_run_cursor (c := c) hc ht hszt hHt (B1.tc_setI zs _)
      have nextCursor : l'.next = inputAdvance l.next (j + jn) := by
        rw [stepCursor, cursor, inputAdvance_add]
      have nextBits : l'.bits.toNat ≤ max l.bits.toNat 10 := by omega
      have hlen := tcStream_length B1
      have hlen' := tcStream_length B'
      refine ⟨l1, setI h zs (llSt s S m), hcond, ?_⟩
      cases rr with
      | error e =>
        cases e with
        | leave =>
          obtain ⟨h1, h2, h3, hbody⟩ := hleave rfl
          refine ⟨.error Ex.leave, l', setI h zs (llSt s S m), ?_, ?_⟩
          · rw [runX_bind, hbody]
          · -- the loop stops here: `m = M`
            have hlenS : (S.drop (3 * m)).length = l'.bits.toNat := by
              rw [← hS1, ← hS', tcStream_length B', h2, List.drop_length]; simp
            simp only [List.length_drop] at hlenS
            have hmM' : m = M := by omega
            subst hmM'
            have hjl : j + jn = bs.length := by
              have : (bs.drop j).length = bs.length - j := by simp
              omega
            refine ⟨j + jn, by omega, rfl, ?_, ?_, ?_, fun _ => ⟨rfl, h1, hjl, h3⟩, (fun hh => by omega), nextCursor, nextBits⟩
            · simpa [tcDrop_drop] using B'.tc_of_heap (h' := h) rfl rfl rfl rfl
            · rw [← hS1, ← hS']; simp [tcDrop_drop]
            · exact hsh1.trans hshape
        | ret v => exact absurd rfl (noRet_NEEDBITS 3 l1 _ _ l' _ hrun v)
      | ok u =>
        cases u
        obtain ⟨h3, hbody⟩ := hok rfl
        have hSlen : 3 ≤ (S.drop (3 * m)).length := by
          have hh : (S.drop (3 * m)).length = l'.bits.toNat + 8 * ((bs.drop j).drop jn).length := by
            rw [← hS1, ← hS']; exact tcStream_length B'
          omega
        simp only [List.length_drop] at hSlen
        have hmM1 : m + 1 ≤ M := by
          rw [hM]
          apply Nat.le_min.mpr
          constructor <;> omega
        have hgrp : grp S m = l'.hold.toNat % 8 := by
          unfold grp
          rw [← hS1, ← hS']
          simp only [stream, tcDrop_drop]
          exact grp_head _ _ _ h3
        have hbits7 : (l'.hold.toUInt32 &&& 7).toNat = grp S m := by
          rw [hgrp]
          have := BITS_toNat l' 3 (by decide)
          rw [show ((1 : UInt32) <<< (3 : UInt32) - 1) = 7 by decide] at this
          rw [this]
          rfl
        have hv : (l'.hold.toUInt32 &&& 7).toUInt16 = (grp S m).toUInt16 := by
          show UInt16.ofNat (l'.hold.toUInt32 &&& 7).toNat = UInt16.ofNat (grp S m)
          rw [hbits7]
        obtain ⟨hB3, hS3, hsub3⟩ := DROPBITS_inv B' 3 h3 (by decide)
        have hB3' : BitInv h { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 } ((bs.drop j).drop jn) := by
          have := hB3.tc_of_heap (h := setI h zs (llSt s S m)) (h' := h) rfl rfl rfl rfl
          exact this
        refine ⟨.ok false, { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 }, setI h zs (llSt s S (m + 1)), ?_, ?_⟩
        · rw [runX_bind, hbody, ← llSt_succ s S m hb19 _ hv]
          simp [runX_pure, setI_setI]
        · have hjn' : jn ≤ bs.length - j := by simpa using hjn
          refine ⟨m + 1, j + jn, by omega, hmM1, by omega, rfl, ?_, ?_, ?_, nextCursor, ?_⟩
          · simpa [tcDrop_drop] using hB3'
          · have hS3' : stream { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 } ((bs.drop j).drop jn) =
                (stream l' ((bs.drop j).drop jn)).drop 3 := hS3
            rw [hS'] at hS3'
            simp only [tcDrop_drop] at hS3' ⊢
            rw [hS3', hS1, tcDrop_drop]
            congr 1
          · exact (hsh1.trans hshape).drop _ _
          · change (l'.bits - 3).toNat ≤ _
            rw [hsub3]
            omega)
    (fun l1 h1 hP => by
      obtain ⟨m, j, hk, hmM, hj, hh1, B1, hS1, hsh1, cursor, bitBound⟩ := hP
      subst hh1
      have hmn : m = n := by omega
      have hMm : M = m := by omega
      have ht : (setI h zs (llSt s S m)).istates zs = some (llSt s S m) := by simp
      have hht := llSt_have s S m (by omega)
      have hcond : runX (llCond c) l1 (setI h zs (llSt s S m)) = .ok ((.ok false, l1), setI h zs (llSt s S m)) := by
        unfold llCond
        rw [hc]
        simp only [runX_bind, runX_lift, ldI_eq, ht, runX_pure]
        have : ¬ (llSt s S m).«have» < (llSt s S m).ncode := by
          rw [UInt32.lt_iff_toNat_lt, hht]
          show ¬ _ < s.ncode.toNat
          omega
        simp [this]
      refine ⟨l1, _, hcond, j, hj, by rw [hMm], B1, by rw [hMm]; exact hS1, hsh1, (fun hh => by omega), (fun _ => rfl), cursor, bitBound⟩)
    (k := n) (l := l) (h := h)
    ⟨0, 0, by omega, by omega, by omega, by rw [llSt_zero]; exact (tcSetI_same hs).symm, by simpa using B,
      by simp [hS], TcRegShape.refl l, (inputAdvance_zero l.next).symm, by omega⟩ (by unfold fuel; omega)
  obtain ⟨r, l', h', hrun, j, hj, hh', B', hS', hsh, hl, hok, cursor, bits⟩ := key
  subst hh'
  exact ⟨r, l', j, hrun, hj, B', hS', hsh, hl, hok, cursor, bits⟩


end Zlib.Inflate.Proofs
