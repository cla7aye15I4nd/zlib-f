import ZlibF.Proof.«inflate.c.main.table3»

/-!
# inflate.c: `case LENLENS:` -- the first loop (reading the code-length code lengths)
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
open Zlib.Inftrees (inflate_table)

/-- The state record after the first `m` iterations of the first loop of `LENLENS`, reading from the stream `S`. -/
def llSt (s : InflateState) (S : List Bool) (m : Nat) : InflateState :=
  { s with «have» := s.«have» + m.toUInt32, lens := lensRead s.lens s.«have».toNat S m }

theorem llSt_zero (s : InflateState) (S : List Bool) : llSt s S 0 = s := by
  simp [llSt, lensRead]

theorem tcU32_add_nat (a : UInt32) (m : Nat) (h : a.toNat + m < 2 ^ 32) : (a + m.toUInt32).toNat = a.toNat + m := by
  rw [UInt32.toNat_add]
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : m < 2 ^ 32), Nat.mod_eq_of_lt h]

theorem llSt_have (s : InflateState) (S : List Bool) (m : Nat) (hb : s.«have».toNat + m ≤ 19) :
    (llSt s S m).«have».toNat = s.«have».toNat + m := by
  simp only [llSt]
  exact tcU32_add_nat _ _ (by omega)

theorem llSt_succ (s : InflateState) (S : List Bool) (m : Nat) (hb : s.«have».toNat + m < 19) (v : UInt16)
    (hv : v = (grp S m).toUInt16) :
    { llSt s S m with «have» := (llSt s S m).«have» + 1, lens := (llSt s S m).lens.set! (orderNat (llSt s S m).«have».toNat) v } = llSt s S (m + 1) := by
  have h1 := llSt_have s S m (by omega)
  subst hv
  simp only [llSt, lensRead] at h1 ⊢
  congr 1
  · rw [UInt32.add_assoc]; congr 1
    show m.toUInt32 + 1 = UInt32.ofNat (m + 1)
    rw [UInt32.ofNat_add]; rfl
  · rw [h1]

theorem tcSetI_same {h : Heap} {zs : Nat} {s : InflateState} (e : h.istates zs = some s) : setI h zs s = h := by
  unfold setI
  rw [upd_self _ _ _ e]

/-- `l'` differs from `l` only in `next`, `have`, `hold`, `bits`. -/
def TcRegShape (l l' : IL) : Prop := l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits }

theorem TcRegShape.refl (l : IL) : TcRegShape l l := rfl

theorem TcRegShape.trans {l1 l2 l3 : IL} (a : TcRegShape l1 l2) (b : TcRegShape l2 l3) : TcRegShape l1 l3 := by
  unfold TcRegShape at *
  rw [b, a]

theorem TcRegShape.drop {l l' : IL} (a : TcRegShape l l') (hold : UInt64) (bits : UInt32) :
    TcRegShape l { l' with hold := hold, bits := bits } := by
  unfold TcRegShape at *
  rw [a]

theorem tcStream_length {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) :
    (stream l bs).length = l.bits.toNat + 8 * bs.length := by
  unfold stream
  simp [natBits_length, bytesBits_length]

theorem tcDrop_drop (L : List α) (a b : Nat) : (L.drop a).drop b = L.drop (a + b) := by
  rw [List.drop_drop]

/-- **The first loop of `LENLENS`.** From `have ≤ ncode ≤ 19`, `M = min (ncode - have) (⌊|S| / 3⌋)` three-bit code lengths are
read from the unread stream `S` into `lens[order[have + u]]`, `u < M`; `have` grows by `M`. If `M < ncode - have` the input
ran out (`goto inf_leave`): every byte was pulled, fewer than 3 bits remain. -/
theorem ll1_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hsz : s.lens.size = 320)
    (hnc : s.ncode.toNat ≤ 19) (hhn : s.«have».toNat ≤ s.ncode.toNat) (B : BitInv h l bs) :
    ∃ r l' j, runX (xwhile (llCond c) (llBody c)) l h =
        .ok ((r, l'), setI h zs (llSt s (stream l bs) (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)))) ∧
      j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = (stream l bs).drop (3 * min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)) ∧
      TcRegShape l l' ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) < s.ncode.toNat - s.«have».toNat →
        r = .error Ex.leave ∧ l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 3) ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) = s.ncode.toNat - s.«have».toNat → r = .ok ()) := by
  obtain ⟨n, hn⟩ : ∃ n, n = s.ncode.toNat - s.«have».toNat := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = stream l bs := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = min n (S.length / 3) := ⟨_, rfl⟩
  rw [← hn, ← hS, ← hM]
  have key := xwhileBrk_run (cond := llCond c) (body := (do llBody c; pure false : X Bool))
    (fun k l1 h1 => ∃ m j, k + m = n ∧ m ≤ M ∧ j ≤ bs.length ∧ h1 = setI h zs (llSt s S m) ∧
      BitInv h l1 (bs.drop j) ∧ stream l1 (bs.drop j) = S.drop (3 * m) ∧ TcRegShape l l1)
    (fun r l1 h1 => ∃ j, j ≤ bs.length ∧ h1 = setI h zs (llSt s S M) ∧ BitInv h l1 (bs.drop j) ∧
      stream l1 (bs.drop j) = S.drop (3 * M) ∧ TcRegShape l l1 ∧
      (M < n → r = .error Ex.leave ∧ l1.have_ = 0 ∧ j = bs.length ∧ l1.bits.toNat < 3) ∧ (M = n → r = .ok ()))
    (fun k l1 h1 hP => by
      obtain ⟨m, j, hk, hmM, hj, hh1, B1, hS1, hsh1⟩ := hP
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
      obtain ⟨rr, l', jn, hrun, hjn, B', hS', hshape, hleave, hok⟩ :=
        llBody_run (c := c) hc ht hszt hHt (B1.tc_setI zs _)
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
            refine ⟨j + jn, by omega, rfl, ?_, ?_, ?_, fun _ => ⟨rfl, h1, hjl, h3⟩, fun hh => by omega⟩
            · simpa [tcDrop_drop] using B'.tc_of_heap (h' := h) rfl rfl rfl
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
          have := hB3.tc_of_heap (h := setI h zs (llSt s S m)) (h' := h) rfl rfl rfl
          exact this
        refine ⟨.ok false, { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 }, setI h zs (llSt s S (m + 1)), ?_, ?_⟩
        · rw [runX_bind, hbody, ← llSt_succ s S m hb19 _ hv]
          simp [runX_pure, setI_setI]
        · have hjn' : jn ≤ bs.length - j := by simpa using hjn
          refine ⟨m + 1, j + jn, by omega, hmM1, by omega, rfl, ?_, ?_, ?_⟩
          · simpa [tcDrop_drop] using hB3'
          · have hS3' : stream { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 } ((bs.drop j).drop jn) =
                (stream l' ((bs.drop j).drop jn)).drop 3 := hS3
            rw [hS'] at hS3'
            simp only [tcDrop_drop] at hS3' ⊢
            rw [hS3', hS1, tcDrop_drop]
            congr 1
          · exact (hsh1.trans hshape).drop _ _)
    (fun l1 h1 hP => by
      obtain ⟨m, j, hk, hmM, hj, hh1, B1, hS1, hsh1⟩ := hP
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
      refine ⟨l1, _, hcond, j, hj, by rw [hMm], B1, by rw [hMm]; exact hS1, hsh1, fun hh => by omega, fun _ => rfl⟩)
    (k := n) (l := l) (h := h)
    ⟨0, 0, by omega, by omega, by omega, by rw [llSt_zero]; exact (tcSetI_same hs).symm, by simpa using B,
      by simp [hS], TcRegShape.refl l⟩ (by unfold fuel; omega)
  obtain ⟨r, l', h', hrun, j, hj, hh', B', hS', hsh, hl, hok⟩ := key
  subst hh'
  exact ⟨r, l', j, hrun, hj, B', hS', hsh, hl, hok⟩

/-! ## The second loop: the remaining code lengths are 0 -/

/-- The state record after the first `m` iterations of the second loop of `LENLENS`. -/
def lzSt (s : InflateState) (m : Nat) : InflateState :=
  { s with «have» := s.«have» + m.toUInt32, lens := lensZero s.lens s.«have».toNat m }

theorem lzSt_zero (s : InflateState) : lzSt s 0 = s := by simp [lzSt, lensZero]

theorem lzSt_have (s : InflateState) (m : Nat) (hb : s.«have».toNat + m ≤ 19) :
    (lzSt s m).«have».toNat = s.«have».toNat + m := by
  simp only [lzSt]
  exact tcU32_add_nat _ _ (by omega)

theorem lzSt_succ (s : InflateState) (m : Nat) (hb : s.«have».toNat + m < 19) :
    { lzSt s m with «have» := (lzSt s m).«have» + 1, lens := (lzSt s m).lens.set! (orderNat (lzSt s m).«have».toNat) 0 } = lzSt s (m + 1) := by
  have h1 := lzSt_have s m (by omega)
  simp only [lzSt, lensZero] at h1 ⊢
  congr 1
  · rw [UInt32.add_assoc]; congr 1
    show m.toUInt32 + 1 = UInt32.ofNat (m + 1)
    rw [UInt32.ofNat_add]; rfl
  · rw [h1]

/-- One iteration of the second loop of `LENLENS`: `lens[order[have++]] = 0`, in a state with `have < 19`. -/
theorem lzBody_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {t : InflateState}
    (hc : c.st = some (.tab zs)) (ht : h.istates zs = some t) (hsz : t.lens.size = 320) (hH : t.«have».toNat < 19) :
    runX (lzBody c) l h = .ok ((.ok (), l),
      setI h zs { t with «have» := t.«have» + 1, lens := t.lens.set! (orderNat t.«have».toNat) 0 }) := by
  have ho : orderNat t.«have».toNat < 19 := order_lt _ hH
  have hoa := orderAt_run (setI h zs { t with «have» := t.«have» + 1 }) t.«have» hH
  have hadd := tcAdd_lens (h := setI h zs { t with «have» := t.«have» + 1 }) (zs := zs)
    (t := { t with «have» := t.«have» + 1 }) (k := (order[t.«have».toNat]!).toNat) (by simp)
    (by have := ho; unfold orderNat at this; simp [hsz]; omega)
  have hst := tcStore_lens (h := setI h zs { t with «have» := t.«have» + 1 }) (zs := zs)
    (t := { t with «have» := t.«have» + 1 }) (k := (order[t.«have».toNat]!).toNat) (0 : UInt16)
    (by simp) (by have := ho; unfold orderNat at this; simp [hsz]; omega)
  unfold lzBody
  rw [hc]
  simp at hst
  simp [runX_bind, runX_lift, ldI_eq, ht, wrI_eq, hoa, hadd, hst, lensP, orderNat]

/-- **The second loop of `LENLENS`**: `while (have < 19) lens[order[have++]] = 0`, from `have ≤ 19`: the registers are unchanged,
`have` becomes 19 (at least) and the entries `lens[order[have ..]]` are 0 (`lzSt`). -/
theorem lz_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hsz : s.lens.size = 320)
    (hHv : s.«have».toNat ≤ 19) :
    runX (xwhile (lzCond c) (lzBody c)) l h = .ok ((.ok (), l), setI h zs (lzSt s (19 - s.«have».toNat))) := by
  obtain ⟨n, hn⟩ : ∃ n, n = 19 - s.«have».toNat := ⟨_, rfl⟩
  rw [← hn]
  have key := xwhileBrk_run (cond := lzCond c) (body := (do lzBody c; pure false : X Bool))
    (fun k l1 h1 => ∃ m, k + m = n ∧ h1 = setI h zs (lzSt s m) ∧ l1 = l)
    (fun r l1 h1 => h1 = setI h zs (lzSt s n) ∧ l1 = l ∧ r = .ok ())
    (fun k l1 h1 hP => by
      obtain ⟨m, hk, hh1, hl1⟩ := hP
      subst h1 l1
      have hb19 : s.«have».toNat + m < 19 := by omega
      have hht := lzSt_have s m (by omega)
      have ht : (setI h zs (lzSt s m)).istates zs = some (lzSt s m) := by simp
      have hszt : (lzSt s m).lens.size = 320 := by simp [lzSt, lensZero_size, hsz]
      have hcond : runX (lzCond c) l (setI h zs (lzSt s m)) = .ok ((.ok true, l), setI h zs (lzSt s m)) := by
        unfold lzCond
        rw [hc]
        simp only [runX_bind, runX_lift, ldI_eq, ht, runX_pure]
        have : (lzSt s m).«have» < 19 := by
          rw [UInt32.lt_iff_toNat_lt, hht]
          show _ < 19
          omega
        simp [this]
      refine ⟨l, setI h zs (lzSt s m), hcond, .ok false, l, setI h zs (lzSt s (m + 1)), ?_, ?_⟩
      · rw [runX_bind, lzBody_run hc ht hszt (by omega), ← lzSt_succ s m hb19]
        simp [runX_pure, setI_setI]
      · exact ⟨m + 1, by omega, rfl, rfl⟩)
    (fun l1 h1 hP => by
      obtain ⟨m, hk, hh1, hl1⟩ := hP
      subst h1 l1
      have hmn : m = n := by omega
      subst hmn
      have ht : (setI h zs (lzSt s m)).istates zs = some (lzSt s m) := by simp
      have hht := lzSt_have s m (by omega)
      refine ⟨l, setI h zs (lzSt s m), ?_, rfl, rfl, rfl⟩
      unfold lzCond
      rw [hc]
      simp only [runX_bind, runX_lift, ldI_eq, ht, runX_pure]
      have : ¬ (lzSt s m).«have» < 19 := by
        rw [UInt32.lt_iff_toNat_lt, hht]
        show ¬ _ < 19
        omega
      simp [this])
    (k := n) (l := l) (h := h) ⟨0, by omega, by rw [lzSt_zero]; exact (tcSetI_same hs).symm, rfl⟩ (by unfold fuel; omega)
  obtain ⟨r, l', h', hrun, hh', hl', hr⟩ := key
  subst hh' hl' hr
  exact hrun

end Zlib.Inflate.Proofs
