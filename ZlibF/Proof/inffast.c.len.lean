import ZlibF.Proof.«inffast.c.lp»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

variable {e : Env} {c : Ctx}

/-- `dodist:` reached from the length block: look up the distance code and run the distance block. -/
def dolenDist (c : Ctx) (l : L) : M L := do
  let __do_lift ← Ptr.add c.dcode ↑(l.hold &&& c.dmask.toUInt64).toNat
  let l : L := { l with here := __do_lift }
  cdoWhile (dodist c) (fun l => pure (l.againD, l)) l

theorem dolenDist_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat))
    (hfr : e.InputFrame A i) :
    Wp (dolenDist c l) (e.heap A msg m) (fun l' h' =>
      ∃ E cb, cb ≤ 15 ∧ DistLook e l.hold.toNat (l.hold.toNat % 2 ^ e.s0.distbits.toNat) E cb ∧
        DistEnd e A msg m ((Sg e l.hold.toNat l.bits.toNat i).drop cb) i o l.len.toNat E l' h') := by
  unfold dolenDist
  have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
  have hR : e.s0.distbits.toNat < 32 := by have := hts.1; omega
  have hmask : c.dmask.toUInt64.toNat = 2 ^ e.s0.distbits.toNat - 1 := by
    rw [hc.dmask, UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hR
  have hidx := u64_and_mask (x := l.hold) hmask
  have hmod : l.hold.toNat % 2 ^ e.s0.distbits.toNat < 2 ^ e.s0.distbits.toNat :=
    Nat.mod_lt _ (Nat.pow_pos (by omega))
  refine Wp.bindO (x := Ptr.ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat)) ?_ ?_
  · rw [hdc, hidx]
    exact Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (by have := hts.2.1; omega)
  · exact Wp.mono (dodistLoop_wp hc A msg m { l with here := Ptr.ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) }
      i o _ hts hmod (LS.congr hls rfl rfl rfl rfl) hA ho hAb hbroke hlen rfl hb15 hpull (hfr.mono (by omega))) (fun _ _ h => h)


/-- The refill before the distance lookup (`if (bits < 15) { two bytes }`) and the distance block. -/
def dolenRefill (c : Ctx) (l : L) : M L :=
  if l.bits < 15 then do
    let __x ← pull l
    let __x ← pull __x
    dolenDist c __x
  else dolenDist c l

/-- What follows the refill: the stream, and the lookup and the end of the distance block. -/
def RefillPost (e : Env) (A : Array UInt8) (msg : BPtr) (m : UInt32) (S : List Bool) (i o len : Nat)
    (l' : L) (h' : Heap) : Prop :=
  ∃ i3 H3 b3 E cb, i ≤ i3 ∧ i3 ≤ i + 2 ∧ Sg e H3 b3 i3 = S ∧ H3 < 2 ^ b3 ∧ 15 ≤ b3 ∧ b3 ≤ 30 ∧ cb ≤ 15 ∧
    DistLook e H3 (H3 % 2 ^ e.s0.distbits.toNat) E cb ∧ DistEnd e A msg m (S.drop cb) i3 o len E l' h'

theorem dolenRefill_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3) (hT3 : i = s + 3 → 4 ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (dolenRefill c l) (e.heap A msg m) (fun l' h' =>
      RefillPost e A msg m (Sg e l.hold.toNat l.bits.toNat i) i o l.len.toNat l' h') := by
  unfold dolenRefill
  by_cases h1 : l.bits < 15
  · simp only [h1, ite_true]
    have h1' : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl3 := hls.pullL (by omega) hiin
    have hs3 := Sg_pullL hls (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
    have hb3' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at hb3 ⊢; omega
    refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl4 := hl3.pullL hb3' hi2
    have hs4 := Sg_pullL hl3 hb3' hi2
    have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0)
      (.ref (BRef.blk e.ib) (i + 1 + 1)) hl3.hb
    simp only [pullL] at hb3 hb4
    refine Wp.mono (dolenDist_wp hc A msg m _ (i + 1 + 1) o hts hl4 hA ho hAb hbroke hlen (by simp only [pullL]; omega) ?_ (hfr.mono (by omega))) ?_
    · by_cases hc3 : i = s + 3
      · right; have := hT3 hc3; simp only [pullL]; omega
      · left; omega
    · intro l' h' hq
      obtain ⟨E, cb, hcb, hlk, hend⟩ := hq
      refine ⟨i + 1 + 1, (pullL (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0) (.ref (BRef.blk e.ib) (i + 1 + 1))).hold.toNat,
        (pullL (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0) (.ref (BRef.blk e.ib) (i + 1 + 1))).bits.toNat,
        E, cb, by omega, by omega, ?_, ?_, ?_, ?_, hcb, hlk, ?_⟩
      · exact hs4.trans hs3
      · exact hl4.hH
      · simp only [pullL]; omega
      · exact hl4.hb
      · rw [hs4, hs3] at hend; exact hend
  · simp only [h1, ite_false]
    have h1' : 15 ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < 15) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
      omega
    refine Wp.mono (dolenDist_wp hc A msg m l i o hts hls hA ho hAb hbroke hlen h1' (Or.inl (by omega)) (hfr.mono (by omega))) ?_
    intro l' h' hq
    obtain ⟨E, cb, hcb, hlk, hend⟩ := hq
    exact ⟨i, l.hold.toNat, l.bits.toNat, E, cb, by omega, by omega, rfl, hls.hH, h1', hls.hb, hcb, hlk, hend⟩


/-- The extra bits of a length are read and added to the base, then the refill and the distance block follow. -/
def dolenExt (c : Ctx) (l : L) : M L := do
  let m ← shl32 1 l.op
  let l : L := { l with len := l.len + (l.hold.toUInt32 &&& m - 1) }
  let __do_lift ← shr64 l.hold l.op.toUInt64
  let l : L := { l with hold := __do_lift }
  let l : L := { l with bits := l.bits - l.op }
  dolenRefill c l

theorem dolenExt_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5) (hxb : l.op.toNat ≤ l.bits.toNat)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3)
    (hT3 : i = s + 3 → 4 + l.op.toNat ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (dolenExt c l) (e.heap A msg m) (fun l' h' =>
      ∃ lx S1, readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (lx, S1) ∧
        RefillPost e A msg m S1 i o (l.len.toNat + lx) l' h') := by
  unfold dolenExt
  have hxs : l.op.toNat < 32 := by omega
  refine Wp.bindO (shl32_ok hxs) ?_
  dsimp only
  have hlow := hold_low32 (x := l.hold) (k := l.op) hxs
  have hlowlt : l.hold.toNat % 2 ^ l.op.toNat < 2 ^ l.op.toNat := Nat.mod_lt _ (Nat.pow_pos (by omega))
  have hpow : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
  have hlen' : (l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1)).toNat = l.len.toNat + l.hold.toNat % 2 ^ l.op.toNat := by
    rw [u32_toNat_add (by rw [hlow]; omega), hlow]
  refine Wp.bindO (shr64_ok (x := l.hold) (n := l.op.toUInt64) (by rw [UInt32.toNat_toUInt64]; omega)) ?_
  have hls1 : LS e (dropL l l.op) i o := hls.dropL l.op hxb (by omega)
  have hbn := dropL_bits l l.op hxb
  have hrb := readBits_bitsOfNat l.op.toNat l.bits.toNat l.hold.toNat (inBits e i) hxb
  have hsg := Sg_dropL (e := e) l l.op i hxb (by omega)
  refine Wp.mono (dolenRefill_wp hc A msg m
    { in_ := l.in_, out := l.out, hold := l.hold >>> l.op.toUInt64, bits := l.bits - l.op, here := l.here, op := l.op,
      len := l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1), dist := l.dist, from_ := l.from_, broke := l.broke,
      againL := l.againL, againD := l.againD } i o s hts (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb hbroke
    (by rw [hlen']; omega) hs6 hT (by intro h3; have := hT3 h3; show 4 ≤ (l.bits - l.op).toNat; simp only [dropL] at hbn; omega) (hfr.mono (by omega))) ?_
  intro l' h' hq
  refine ⟨l.hold.toNat % 2 ^ l.op.toNat, Sg e (dropL l l.op).hold.toNat (dropL l l.op).bits.toNat i, ?_, ?_⟩
  · unfold Sg; rw [hrb, dropL_hold l l.op (by omega), dropL_bits l l.op hxb]
  · simp only [hlen'] at hq
    exact hq


/-- After `op &= 15`: the extra bits of the length (read after at most one more byte), then `dolenExt`. -/
def dolenLen (c : Ctx) (l : L) : M L :=
  if l.op != 0 then
    if l.bits < l.op then do
      let __x ← pull l
      dolenExt c __x
    else dolenExt c l
  else dolenRefill c l

theorem dolenLen_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 2) (hb2 : i = s + 2 → 1 ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (dolenLen c l) (e.heap A msg m) (fun l' h' =>
      ∃ i2 lx S1, i ≤ i2 ∧ i2 ≤ i + 1 ∧ readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (lx, S1) ∧
        RefillPost e A msg m S1 i2 o (l.len.toNat + lx) l' h') := by
  unfold dolenLen
  by_cases h0 : l.op != 0
  · simp only [h0, ite_true]
    have h0' : l.op.toNat ≠ 0 := by
      intro h; apply (by simpa using h0 : l.op ≠ 0); exact UInt32.toNat_inj.mp (by simpa using h)
    by_cases h1 : l.bits < l.op
    · simp only [h1, ite_true]
      have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
      have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
      refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
      have hl3 := hls.pullL (by omega) hiin
      have hs3 := Sg_pullL hls (by omega) hiin
      have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
      refine Wp.mono (dolenExt_wp hc A msg m _ (i + 1) o s hts hl3 hA ho hAb hbroke (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 ⊢; omega) (by simp only [pullL]; omega) hs6 (by omega)
        (by intro h3; simp only [pullL] at hb3 ⊢; have := hb2 (by omega); omega) (hfr.mono (by omega))) ?_
      intro l' h' hq
      obtain ⟨lx, S1, hr, hrp⟩ := hq
      refine ⟨i + 1, lx, S1, by omega, by omega, ?_, ?_⟩
      · simp only [pullL] at hr hs3 ⊢; rw [hs3] at hr; exact hr
      · simp only [pullL] at hrp ⊢; exact hrp
    · simp only [h1, ite_false]
      have h1' : l.op.toNat ≤ l.bits.toNat := by
        have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (dolenExt_wp hc A msg m l i o s hts hls hA ho hAb hbroke hx h1' hlen hs6 (by omega)
        (by intro h3; omega) (hfr.mono (by omega))) ?_
      intro l' h' hq
      obtain ⟨lx, S1, hr, hrp⟩ := hq
      exact ⟨i, lx, S1, by omega, by omega, hr, hrp⟩
  · simp only [h0, ite_false]
    have h0' : l.op.toNat = 0 := by
      have : l.op = 0 := by simpa using h0
      rw [this]; rfl
    refine Wp.mono (dolenRefill_wp hc A msg m l i o s hts hls hA ho hAb hbroke ⟨hlen.1, by
      have : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
      omega⟩ hs6 (by omega) (by intro h3; omega) (hfr.mono (by omega))) ?_
    intro l' h' hq
    refine ⟨i, 0, Sg e l.hold.toNat l.bits.toNat i, by omega, by omega, ?_, ?_⟩
    · rw [h0']; rfl
    · simpa using hq

end Zlib.Inffast.Proofs
