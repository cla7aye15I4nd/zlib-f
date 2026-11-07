import ZlibF.Proof.«adler32.c.public-block»

/-! Adler execution over every represented byte reference. -/
namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec Zlib.Adler32.Proofs


variable {h : Heap} {ref : BRef} {bytes : Array UInt8}

theorem do1_ok_any (hb : Space.get h ref = some bytes) (s : Locals) (p i : Nat)
    (hbuf : s.buf = .ref ref p) (hlt : p + i < bytes.size) :
    OkOn h (do1 s i) (upd s bytes[p + i]!) := by
  obtain ⟨a, s2, buf, len, n⟩ := s
  simp only at hbuf
  subst hbuf
  unfold do1
  refine OkOn.bind (Ptr.index_ok hb hlt) ?_
  rw [getElem_eq_bang bytes _ hlt]
  exact OkOn.pure _ _

theorem upd_buf_any (t : Locals) (b : UInt8) : (upd t b).buf = t.buf := rfl

theorem do16_ok_any (hb : Space.get h ref = some bytes) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref ref p) (hlt : p + 16 ≤ bytes.size) :
    OkOn h (do16 s) (updL s (seg bytes p 16)) := by
  have st : ∀ (t : Locals) (i : Nat), t.buf = .ref ref p → i < 16 →
      OkOn h (do1 t i) (upd t bytes[p + i]!) :=
    fun t i ht hi => do1_ok_any (ref := ref) hb t p i ht (by omega)
  unfold do16
  refine OkOn.bind (st _ 0 hbuf (by omega)) ?_
  refine OkOn.bind (st _ 1 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 2 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 3 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 4 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 5 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 6 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 7 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 8 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 9 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 10 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 11 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 12 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 13 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  refine OkOn.bind (st _ 14 (by simp only [upd_buf_any]; exact hbuf) (by omega)) ?_
  have e : updL s (seg bytes p 16) = upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd
      (upd (upd (upd (upd (upd s bytes[p + 0]!) bytes[p + 1]!) bytes[p + 2]!) bytes[p + 3]!)
      bytes[p + 4]!) bytes[p + 5]!) bytes[p + 6]!) bytes[p + 7]!) bytes[p + 8]!) bytes[p + 9]!)
      bytes[p + 10]!) bytes[p + 11]!) bytes[p + 12]!) bytes[p + 13]!) bytes[p + 14]!) bytes[p + 15]! := rfl
  rw [e]
  exact st _ 15 (by simp only [upd_buf_any]; exact hbuf) (by omega)

theorem stepByte_ok_any (hb : Space.get h ref = some bytes) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref ref p) (hlt : p < bytes.size) :
    OkOn h (stepByte s) { upd s bytes[p]! with buf := .ref ref (p + 1) } := by
  obtain ⟨a, s2, buf, len, n⟩ := s
  simp only at hbuf
  subst hbuf
  unfold stepByte
  refine OkOn.bind (Ptr.load_ok hb hlt) ?_
  refine OkOn.bind (Ptr.add_ok hb (by omega) (by omega)) ?_
  rw [getElem_eq_bang bytes _ hlt]
  have : ((p : Int) + 1).toNat = p + 1 := by omega
  rw [this]
  exact OkOn.pure _ _

theorem bufAdd16_ok_any (hb : Space.get h ref = some bytes) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref ref p) (hlt : p + 16 ≤ bytes.size) :
    OkOn h (do pure { s with buf := ← s.buf.add 16 }) { s with buf := .ref ref (p + 16) } := by
  rw [hbuf]
  refine OkOn.bind (Ptr.add_ok hb (by omega) (by omega)) ?_
  have : ((p : Int) + 16).toNat = p + 16 := by omega
  rw [this]
  exact OkOn.pure _ _

theorem byteLoop_ok_any (hb : Space.get h ref = some bytes) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref ref p) (hfit : p + s.len.toNat ≤ bytes.size) :
    ∃ s', OkOn h (cwhile lenPostDec stepByte s) s' ∧
      s'.buf = .ref ref (p + s.len.toNat) ∧ AccFrom s s' (seg bytes p s.len.toNat) := by
  have hk := fuel_gt s.len
  generalize hkdef : s.len.toNat = k at hfit hk ⊢
  let P : Nat → Locals → Prop := fun j t => ∃ i, i + j = k ∧ t.buf = .ref ref (p + i) ∧
    t.len.toNat = j ∧ AccFrom s t (seg bytes p i)
  let Q : Locals → Prop := fun t => t.buf = .ref ref (p + k) ∧ AccFrom s t (seg bytes p k)
  refine cwhile_ok (h := h) P Q ?_ ?_ (k := k) ⟨0, by omega, by simpa using hbuf, hkdef, AccFrom.refl s⟩ hk
  · intro j t ⟨i, hi, htb, htl, hacc⟩
    have hne : (t.len != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; rw [h0] at htl; simp at htl
    refine ⟨{ t with len := t.len - 1 }, { upd { t with len := t.len - 1 } bytes[p + i]! with
        buf := .ref ref (p + i + 1) }, ?_, stepByte_ok_any (ref := ref) hb _ (p + i) htb (by omega), ?_⟩
    · show OkOn h (pure (t.len != 0, { t with len := t.len - 1 })) _
      rw [hne]; exact OkOn.pure _ _
    · refine ⟨i + 1, by omega, by simp [Nat.add_assoc], ?_, ?_⟩
      · simp only [Zlib.Adler32.Proofs.upd]
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      · rw [seg_add, seg_one]
        exact (hacc.congr rfl rfl).upd _
  · intro t ⟨i, hi, htb, htl, hacc⟩
    have he : (t.len != 0) = false := by
      simp only [bne_eq_false_iff_eq]; exact UInt64.toNat_inj.mp (by simp [htl])
    refine ⟨{ t with len := t.len - 1 }, ?_, ?_, ?_⟩
    · show OkOn h (pure (t.len != 0, { t with len := t.len - 1 })) _
      rw [he]; exact OkOn.pure _ _
    · simpa [show i = k by omega] using htb
    · exact (show i = k by omega) ▸ hacc.congr rfl rfl

/-- `while (len >= 16) { len -= 16; DO16(buf); buf += 16; }` -/
theorem chunkLoop_ok_any (hb : Space.get h ref = some bytes) (s : Locals) (p : Nat)
    (hbuf : s.buf = .ref ref p) (hfit : p + s.len.toNat ≤ bytes.size) :
    ∃ s', OkOn h (cwhile (fun s => pure (decide (s.len ≥ 16), s))
        (fun s => do
          let s ← do16 { adler := s.adler, sum2 := s.sum2, buf := s.buf, len := s.len - 16, n := s.n }
          let __do_lift ← s.buf.add 16
          pure { adler := s.adler, sum2 := s.sum2, buf := __do_lift, len := s.len, n := s.n }) s) s' ∧
      s'.buf = .ref ref (p + 16 * (s.len.toNat / 16)) ∧ s'.len.toNat = s.len.toNat % 16 ∧
      s'.n = s.n ∧ AccFrom s s' (seg bytes p (16 * (s.len.toNat / 16))) := by
  have hk := fuel_gt s.len
  generalize hrdef : s.len.toNat = r at hfit hk ⊢
  let P : Nat → Locals → Prop := fun j t => ∃ i, i + j = r / 16 ∧
    t.buf = .ref ref (p + 16 * i) ∧
    t.len.toNat = r - 16 * i ∧ t.n = s.n ∧ AccFrom s t (seg bytes p (16 * i))
  let Q : Locals → Prop := fun t => t.buf = .ref ref (p + 16 * (r / 16)) ∧
    t.len.toNat = r % 16 ∧ t.n = s.n ∧ AccFrom s t (seg bytes p (16 * (r / 16)))
  refine cwhile_ok (h := h) P Q ?_ ?_ (k := r / 16)
    ⟨0, by omega, by simpa using hbuf, by simp [hrdef], rfl, AccFrom.refl s⟩ (by omega)
  · intro j t ⟨i, hi, htb, htl, htn, hacc⟩
    have hge : decide (t.len ≥ 16) = true := by
      simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le]; simp; omega
    let t1 : Locals := { adler := t.adler, sum2 := t.sum2, buf := t.buf, len := t.len - 16, n := t.n }
    have ht1 : t1.buf = .ref ref (p + 16 * i) := htb
    refine ⟨t, { updL t1 (seg bytes (p + 16 * i) 16) with
        buf := .ref ref (p + 16 * i + 16) }, ?_, ?_, ?_⟩
    · show OkOn h (pure (decide (t.len ≥ 16), t)) _
      rw [hge]; exact OkOn.pure _ _
    · refine OkOn.bind (do16_ok_any (ref := ref) hb t1 (p + 16 * i) ht1 (by omega)) ?_
      exact bufAdd16_ok_any (ref := ref) hb _ (p + 16 * i) ht1 (by omega)
    · refine ⟨i + 1, by omega, by simp [Nat.mul_add, Nat.add_assoc], ?_, htn, ?_⟩
      · show (t.len - 16).toNat = r - 16 * (i + 1)
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      · rw [show 16 * (i + 1) = 16 * i + 16 by omega, seg_add]
        exact ((hacc.congr rfl rfl : AccFrom s t1 _).updL _).congr rfl rfl
  · intro t ⟨i, hi, htb, htl, htn, hacc⟩
    have hlt : decide (t.len ≥ 16) = false := by
      simp only [decide_eq_false_iff_not, ge_iff_le, UInt64.le_iff_toNat_le]; simp; omega
    refine ⟨t, ?_, ?_, ?_, htn, ?_⟩
    · show OkOn h (pure (decide (t.len ≥ 16), t)) _
      rw [hlt]; exact OkOn.pure _ _
    · simpa [show i = r / 16 by omega] using htb
    · rw [htl]; omega
    · exact (show i = r / 16 by omega) ▸ hacc

theorem nmaxBlock_ok_any (hb : Space.get h ref = some bytes) (t : Locals) (p : Nat)
    (hbuf : t.buf = .ref ref p) (hfit : p + 5552 ≤ bytes.size) (ht : t.n = 347) :
    ∃ u, OkOn h (cdoWhile
        (fun s => do
          let s ← do16 s
          let __do_lift ← s.buf.add 16
          pure { adler := s.adler, sum2 := s.sum2, buf := __do_lift, len := s.len, n := s.n })
        (fun s => pure (s.n - 1 != 0, { adler := s.adler, sum2 := s.sum2, buf := s.buf, len := s.len, n := s.n - 1 }))
        t) u ∧
      u.buf = .ref ref (p + 5552) ∧ u.len = t.len ∧ AccFrom t u (seg bytes p 5552) := by
  let P : Nat → Locals → Prop := fun m u => ∃ i, i + m = 346 ∧ u.n.toNat = m + 1 ∧
    u.buf = .ref ref (p + 16 * i) ∧ u.len = t.len ∧ AccFrom t u (seg bytes p (16 * i))
  let Q : Locals → Prop := fun u => u.buf = .ref ref (p + 5552) ∧ u.len = t.len ∧
    AccFrom t u (seg bytes p 5552)
  refine cdoWhile_ok (h := h) P Q ?_ ?_ (k := 346)
    ⟨0, rfl, by rw [ht]; rfl, by simpa using hbuf, rfl, AccFrom.refl t⟩ (by simp [fuel])
  · intro m u ⟨i, hi, hn, hub, hul, hacc⟩
    let u1 : Locals := { updL u (seg bytes (p + 16 * i) 16) with buf := .ref ref (p + 16 * i + 16) }
    have hne : (u1.n - 1 != 0) = true := by
      have : u1.n = u.n := rfl
      simp only [bne_iff_ne, ne_eq, this]
      intro h0
      have := congrArg UInt32.toNat h0
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)] at this
      simp at this; omega
    refine ⟨u1, { u1 with n := u1.n - 1 }, ?_, ?_, ?_⟩
    · refine OkOn.bind (do16_ok_any (ref := ref) hb u (p + 16 * i) hub (by omega)) ?_
      exact bufAdd16_ok_any (ref := ref) hb _ (p + 16 * i) hub (by omega)
    · show OkOn h (pure (u1.n - 1 != 0, { u1 with n := u1.n - 1 })) _
      rw [hne]; exact OkOn.pure _ _
    · refine ⟨i + 1, by omega, ?_, ?_, hul, ?_⟩
      · show (u.n - 1).toNat = m + 1
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
        simp; omega
      · show Ptr.ref ref (p + 16 * i + 16) = _
        rw [show p + 16 * i + 16 = p + 16 * (i + 1) by omega]
      · rw [show 16 * (i + 1) = 16 * i + 16 by omega, seg_add]
        exact (hacc.updL _).congr rfl rfl
  · intro u ⟨i, hi, hn, hub, hul, hacc⟩
    let u1 : Locals := { updL u (seg bytes (p + 16 * i) 16) with buf := .ref ref (p + 16 * i + 16) }
    have he : (u1.n - 1 != 0) = false := by
      have : u1.n = u.n := rfl
      simp only [bne_eq_false_iff_eq, this]
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
      simp; omega
    refine ⟨u1, { u1 with n := u1.n - 1 }, ?_, ?_, ?_⟩
    · refine OkOn.bind (do16_ok_any (ref := ref) hb u (p + 16 * i) hub (by omega)) ?_
      exact bufAdd16_ok_any (ref := ref) hb _ (p + 16 * i) hub (by omega)
    · show OkOn h (pure (u1.n - 1 != 0, { u1 with n := u1.n - 1 })) _
      rw [he]; exact OkOn.pure _ _
    · refine ⟨by simp [u1]; omega, hul, ?_⟩
      have hi' : i = 346 := by omega
      subst hi'
      rw [show 5552 = 16 * 346 + 16 by rfl, seg_add]
      exact (hacc.updL _).congr rfl rfl


theorem adler32_z_long_any (hb : Space.get h ref = some bytes) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) (h16 : 16 ≤ L) :
    ∃ r, OkOn h (adler32_z a (.ref ref off) L.toUInt64) r ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off L) := by
  have hLn : L.toUInt64.toNat = L := by simp; omega
  have hne1 : (L.toUInt64 == 1) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
  have hnull : (Ptr.ref ref off == (Ptr.null : BPtr)) = false := by simp
  have hn16 : ¬ (L.toUInt64 < 16) := by rw [UInt64.lt_iff_toNat_lt, hLn]; simp; omega
  unfold adler32_z
  rw [ite_eq_right_of_eq_false _ _ (by simp [hne1]), ite_eq_right_of_eq_false _ _ (by simp [hnull]),
    ite_eq_right_of_eq_false _ _ (by simp [hn16])]
  let lo := (a &&& 65535).toNat % 65521
  let hi := (a >>> 16 &&& 65535).toNat % 65521
  let q := L / 5552
  let r := L % 5552
  let s0 : Locals := { adler := a &&& 65535, sum2 := a >>> 16 &&& 65535, buf := .ref ref off, len := L.toUInt64, n := 0 }
  let P : Nat → Locals → Prop := fun k t => ∃ i, i + k = q ∧ t.buf = .ref ref (off + 5552 * i) ∧
    t.len.toNat = L - 5552 * i ∧
    Rel 0 t.adler t.sum2 (sums lo hi (seg bytes off (5552 * i))).1 (sums lo hi (seg bytes off (5552 * i))).2 ∧
    (1 ≤ i → t.adler.toNat < 65521 ∧ t.sum2.toNat < 65521)
  let Q : Locals → Prop := fun t => t.buf = .ref ref (off + 5552 * q) ∧ t.len.toNat = r ∧
    Rel 0 t.adler t.sum2 (sums lo hi (seg bytes off (5552 * q))).1 (sums lo hi (seg bytes off (5552 * q))).2 ∧
    (1 ≤ q → t.adler.toNat < 65521 ∧ t.sum2.toNat < 65521)
  have hinit : P q s0 := ⟨0, by omega, by simp [s0], by simp [s0, hLn], rel_init a, by omega⟩
  refine OkOn.bind_ex (cwhile_ok (h := h) P Q ?_ ?_ hinit (by simp [fuel]; omega)) ?_
  · -- one NMAX block
    rintro k t ⟨i, hi_, htb, htl, hrel, -⟩
    have hge : decide (t.len ≥ NMAX) = true := by
      simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le, htl]; simp [NMAX]; omega
    let t0 : Locals := { adler := t.adler, sum2 := t.sum2, buf := t.buf, len := t.len - NMAX, n := (NMAX / 16).toUInt32 }
    obtain ⟨u, hu, hub, hul, hacc⟩ := nmaxBlock_ok_any (ref := ref) hb t0 (off + 5552 * i) htb (by omega) nmax_div
    refine ⟨t, { adler := u.adler % BASE, sum2 := u.sum2 % BASE, buf := u.buf, len := u.len, n := u.n }, ?_, ?_, ?_⟩
    · show OkOn h (pure (decide (t.len ≥ NMAX), t)) _
      rw [hge]; exact OkOn.pure _ _
    · exact OkOn.bind hu (OkOn.pure _ _)
    · have hacc' := acc_list (seg bytes (off + 5552 * i) 5552) 0 t0.adler t0.sum2 _ _ hrel (by simp [seg_length])
      rw [seg_length] at hacc'
      have hmod := rel_mod _ _ _ _ _ hacc'
      refine ⟨i + 1, by omega, ?_, ?_, ?_, ?_⟩
      · rw [hub, show off + 5552 * i + 5552 = off + 5552 * (i + 1) by omega]
      · show u.len.toNat = _
        rw [hul]; show (t.len - NMAX).toNat = _
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, htl]; simp [NMAX]; omega), htl]
        simp [NMAX]; omega
      · rw [show 5552 * (i + 1) = 5552 * i + 5552 by omega, seg_add, sums_append]
        obtain ⟨ha, hs⟩ := hacc
        simp only [updL] at ha hs
        show Rel 0 (u.adler % 65521) (u.sum2 % 65521) _ _
        rw [ha, hs]
        exact hmod
      · intro _
        simp only [UInt64.toNat_mod, BASE]
        exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
  · -- loop exit
    rintro t ⟨i, hi_, htb, htl, hrel, hred⟩
    have hlt : decide (t.len ≥ NMAX) = false := by
      simp only [decide_eq_false_iff_not, ge_iff_le, UInt64.le_iff_toNat_le, htl]; simp [NMAX]; omega
    refine ⟨t, ?_, ?_⟩
    · show OkOn h (pure (decide (t.len ≥ NMAX), t)) _
      rw [hlt]; exact OkOn.pure _ _
    · have : i = q := by omega
      subst this
      exact ⟨htb, by rw [htl]; omega, hrel, hred⟩
  · -- remainder
    rintro t ⟨htb, htl, hrel, hred⟩
    by_cases hr0 : r = 0
    · have hz : (t.len != 0) = false := by
        simp only [bne_eq_false_iff_eq]; exact UInt64.toNat_inj.mp (by simp [htl, hr0])
      rw [hz]
      simp only [Bool.false_eq_true, ite_false]
      have hq : 1 ≤ q := by omega
      obtain ⟨ha, hs⟩ := hred hq
      obtain ⟨ea, es⟩ := rel_exact hrel ha hs
      refine ⟨_, OkOn.bind (OkOn.pure _ _) (OkOn.pure _ _), ?_⟩
      have hseg : seg bytes off L = seg bytes off (5552 * q) := by
        rw [show 5552 * q = L by omega]
      rw [hseg]
      exact result_value a t.adler t.sum2 _ ea es
    · have hnz : (t.len != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; intro e; have := congrArg UInt64.toNat e; simp [htl] at this; omega
      rw [hnz]
      simp only [ite_true]
      obtain ⟨c, hc, hcb, hcl, -, hcacc⟩ := chunkLoop_ok_any (ref := ref) hb t (off + 5552 * q) htb (by rw [htl]; omega)
      rw [htl] at hcb hcl hcacc
      obtain ⟨d, hd, hdb, hdacc⟩ := byteLoop_ok_any (ref := ref) hb c _ hcb (by rw [hcl]; omega)
      rw [hcl] at hdb hdacc
      have hall := hcacc.trans hdacc
      have hlen : (seg bytes (off + 5552 * q) (16 * (r / 16)) ++ seg bytes (off + 5552 * q + 16 * (r / 16)) (r % 16)).length = r := by
        simp [seg_length]; omega
      have hrel' := acc_list _ 0 t.adler t.sum2 _ _ hrel (by rw [hlen]; omega)
      rw [hlen] at hrel'
      obtain ⟨hda, hds⟩ := hall
      simp only [updL] at hda hds
      refine ⟨_, OkOn.bind hc (OkOn.bind hd (OkOn.bind (OkOn.pure _ _) (OkOn.pure _ _))), ?_⟩
      have hseg : seg bytes off L = seg bytes off (5552 * q) ++
          (seg bytes (off + 5552 * q) (16 * (r / 16)) ++ seg bytes (off + 5552 * q + 16 * (r / 16)) (r % 16)) := by
        rw [← seg_add, ← seg_add]; congr 1; omega
      rw [hseg]
      apply result_value
      · rw [sums_append, show (d.adler % BASE).toNat = d.adler.toNat % 65521 by simp [BASE], hda]
        exact hrel'.1
      · rw [sums_append, show (d.sum2 % BASE).toNat = d.sum2.toNat % 65521 by simp [BASE], hds]
        exact hrel'.2.1


theorem adler32_z_short_any (hb : Space.get h ref = some bytes) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (h16 : L < 16) (h1 : L ≠ 1) :
    ∃ r, OkOn h (adler32_z a (.ref ref off) L.toUInt64) r ∧
      r.toNat = Spec.adler32 a.toNat (seg bytes off L) := by
  have hLn : L.toUInt64.toNat = L := by simp; omega
  have hne1 : (L.toUInt64 == 1) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
  have hnull : (Ptr.ref ref off == (Ptr.null : BPtr)) = false := by simp
  have hy16 : L.toUInt64 < 16 := by rw [UInt64.lt_iff_toNat_lt, hLn]; simp; omega
  unfold adler32_z
  rw [ite_eq_right_of_eq_false _ _ (by simp [hne1]), ite_eq_right_of_eq_false _ _ (by simp [hnull]),
    ite_eq_left hy16]
  let s0 : Locals := { adler := a &&& 65535, sum2 := a >>> 16 &&& 65535, buf := .ref ref off, len := L.toUInt64, n := 0 }
  obtain ⟨d, hd, -, hacc⟩ := byteLoop_ok_any (ref := ref) hb s0 off rfl (by simp [s0, hLn]; omega)
  have hrel := acc_list (seg bytes off s0.len.toNat) 0 s0.adler s0.sum2 _ _ (rel_init a)
    (by simp [seg_length, s0, hLn]; omega)
  obtain ⟨hda, hds⟩ := hacc
  simp only [updL] at hda hds
  rw [← hda, ← hds] at hrel
  obtain ⟨r1, r2, rb1, -⟩ := hrel
  simp only [seg_length, s0, hLn] at r1 r2 rb1
  refine OkOn.bind_ex (R := fun x => x = d) ⟨d, hd, rfl⟩ ?_
  intro x hx
  rw [hx]
  dsimp only
  have hres := result_value a (if d.adler ≥ BASE then d.adler - BASE else d.adler) (d.sum2 % BASE)
    (seg bytes off L) ?_ ?_
  · split
    · next hge => exact ⟨_, OkOn.pure _ _, by simpa [hge] using hres⟩
    · next hlt => exact ⟨_, OkOn.pure _ _, by simpa [hlt] using hres⟩
  · split
    · next hge =>
      rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat] at hge
      rw [sub_small _ _ (by rw [base_toNat]; omega), base_toNat, ← r1]; omega
    · next hlt =>
      rw [ge_iff_le, UInt64.le_iff_toNat_le, base_toNat] at hlt
      rw [← r1]; omega
  · rw [UInt64.toNat_mod, base_toNat, r2]


theorem adler32_z_short_format_any (hb : Space.get h ref = some bytes) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (h16 : L < 16) (h1 : L ≠ 1) :
    C.run (adler32_z a (.ref ref off) L.toUInt64) h =
      .ok ((ZlibF.Spec.adler32Update (canonicalStart a) (seg bytes off L)).toUInt64, h) := by
  obtain ⟨r, hr, hv⟩ := adler32_z_short_any hb a off L hfit h16 h1
  change C.run (adler32_z a (.ref ref off) L.toUInt64) h = .ok (r, h) at hr
  rw [hr]
  congr 2
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, adler_format_seed, UInt32.toNat_ofNat', hv]
  have hs := sums_lt (a.toNat % 65536 % 65521) (a.toNat / 65536 % 65536 % 65521)
    (seg bytes off L) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  change (sums _ _ _).1 < 65521 ∧ (sums _ _ _).2 < 65521 at hs
  have he : Zlib.Adler32.Spec.adler32 a.toNat (seg bytes off L) < 2 ^ 32 := by
    unfold Zlib.Adler32.Spec.adler32
    simp only [Zlib.Adler32.Spec.BASE]
    omega
  exact (Nat.mod_eq_of_lt he).symm


theorem adler32_z_any_format (hb : Space.get h ref = some bytes) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) (h1 : L ≠ 1) :
    C.run (adler32_z a (.ref ref off) L.toUInt64) h =
      .ok ((ZlibF.Spec.adler32Update (canonicalStart a) (seg bytes off L)).toUInt64, h) := by
  by_cases h16 : L < 16
  · exact adler32_z_short_format_any hb a off L hfit h16 h1
  · obtain ⟨r, hr, hv⟩ := adler32_z_long_any hb a off L hfit hL (by omega)
    change C.run (adler32_z a (.ref ref off) L.toUInt64) h = .ok (r, h) at hr
    rw [hr]
    congr 2
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, adler_format_seed, UInt32.toNat_ofNat', hv]
    have hs := sums_lt (a.toNat % 65536 % 65521) (a.toNat / 65536 % 65536 % 65521)
      (seg bytes off L) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    change (sums _ _ _).1 < 65521 ∧ (sums _ _ _).2 < 65521 at hs
    have he : Zlib.Adler32.Spec.adler32 a.toNat (seg bytes off L) < 2 ^ 32 := by
      unfold Zlib.Adler32.Spec.adler32
      simp only [Zlib.Adler32.Spec.BASE]
      omega
    exact (Nat.mod_eq_of_lt he).symm

/-- `uLong adler32(uLong adler, const Bytef *buf, uInt len)`: the
32-bit entry preserves the full general-reference format result. -/
theorem adler32_any_format (hb : Space.get h ref = some bytes) (a : UInt64)
    (off : Nat) (len : UInt32) (hfit : off + len.toNat ≤ bytes.size)
    (h1 : len.toNat ≠ 1) :
    C.run (Zlib.Adler32.adler32 a (.ref ref off) len) h =
      .ok ((ZlibF.Spec.adler32Update (canonicalStart a) (seg bytes off len.toNat)).toUInt64, h) := by
  simpa [Zlib.Adler32.adler32, UInt32.toNat_toUInt64, UInt64.ofNat_toNat] using
    (adler32_z_any_format hb a off len.toNat hfit (by have := len.toNat_lt; omega) h1)

#print axioms adler32_z_any_format
#print axioms adler32_any_format
end Zlib.Adler32.Proofs
