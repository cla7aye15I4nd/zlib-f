import ZlibF.Proof.«trees.c.inv»

/-!
# trees.c: the bit writers (`put_byte`, `put_short`, `send_bits`, `bi_reverse`, `bi_flush`, `bi_windup`)
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

theorem put_byte_run {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hroom : d.pending.toNat < buf.size) (c : UInt8) :
    put_byte (some (.tab id)) c h =
      .ok ((), setD (setB h b (buf.set! d.pending.toNat c)) id { d with pending := d.pending + 1 }) := by
  have hg : Space.get h (BRef.blk b) = some buf := hb.bytes
  have e1 := Ptr.add_nat_ok (off := 0) (n := d.pending.toNat) hg (by omega)
  have e2 := Ptr.store_ok (v := c) (off := 0 + d.pending.toNat) hg hb.rw (by omega)
  unfold OkOn at e1
  unfold put_byte
  rw [bind_app, rd_run hb.dstate]
  simp only [hb.pbuf]
  rw [bind_app, e1]
  simp only []
  rw [bind_app]
  unfold store8
  rw [e2]
  simp only []
  have hd : (Space.put h (BRef.blk b) (buf.set! (0 + d.pending.toNat) c)).dstates id = some d := hb.dstate
  rw [md_run hd]
  simp [setD, Space.put, setB]
  rw [hb.pbuf]


@[simp] theorem setB_setB (h : Heap) (b : Nat) (a a' : Array UInt8) : setB (setB h b a) b a' = setB h b a' := by
  simp [setB, upd_upd]

theorem TreesBase.step {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (buf' : Array UInt8) (hsz : buf'.size = buf.size) (d' : DeflateState)
    (hw : d'.WellFormed) (h1 : d'.pending_buf = d.pending_buf) (h2 : d'.pending_buf_size = d.pending_buf_size)
    (h3 : d'.sym_buf = d.sym_buf) (h4 : d'.lit_bufsize = d.lit_bufsize) (h5 : d'.sym_end = d.sym_end)
    (h6 : d'.pending.toNat ≤ d'.pending_buf_size.toNat) :
    TreesBase (setD (setB h b buf') id d') id d' b buf' where
  dstate := by simp
  wf := hw
  static := by simpa using hb.static
  pbuf := by rw [h1]; exact hb.pbuf
  bytes := by simp
  rw := by simpa using hb.rw
  size := by rw [hsz, h4]; exact hb.size
  psize := by rw [hsz, h2]; exact hb.psize
  sym := by rw [h3, h4]; exact hb.sym
  lit_lo := by rw [h4]; exact hb.lit_lo
  lit_hi := by rw [h4]; exact hb.lit_hi
  sym_end := by rw [h5, h4]; exact hb.sym_end
  pending_le := h6

theorem toNat_add_one_u64 {x : UInt64} (hx : x.toNat < 2 ^ 20) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

theorem toNat_add_two_u64 {x : UInt64} (hx : x.toNat < 2 ^ 20) : (x + 2).toNat = x.toNat + 2 := by
  rw [UInt64.toNat_add]; simp; omega

theorem TreesBase.pending_small {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) : d.pending.toNat < 2 ^ 20 := by
  have := hb.pending_le; have := hb.psize; have := hb.size; have := hb.lit_hi; omega

theorem put_short_run {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hroom : d.pending.toNat + 2 ≤ buf.size) (w : UInt16) :
    put_short (some (.tab id)) w h =
      .ok ((), setD (setB h b ((buf.set! d.pending.toNat (w &&& 0xff).toUInt8).set! (d.pending.toNat + 1)
          (w >>> 8).toUInt8)) id { d with pending := d.pending + 2 }) := by
  have hp := hb.pending_small
  have hp1 := toNat_add_one_u64 hp
  have hs1 := hb.size
  have hs2 := hb.lit_hi
  unfold put_short
  rw [bind_app, put_byte_run hb (by omega)]
  simp only []
  have hb1 := hb.step (buf.set! d.pending.toNat (w &&& 0xff).toUInt8) (by simp) { d with pending := d.pending + 1 }
    hb.wf rfl rfl rfl rfl rfl (by simp only []; rw [hp1]; have := hb.psize; omega)
  rw [put_byte_run hb1 (by simp only []; rw [hp1]; simp; omega)]
  simp only [setD_setB, setD_setD, setB_setB]
  have e2 : d.pending + 1 + 1 = d.pending + 2 := by
    apply UInt64.toNat_inj.mp
    rw [toNat_add_one_u64 (by rw [hp1]; omega), hp1, toNat_add_two_u64 hp]
  simp only [e2, hp1]


theorem Buf_size_toInt : Buf_size.toInt = 16 := by decide

/-- `(ush)value` as a natural number. -/
def v16 (value : Int32) : Nat := (i2us value).toNat

theorem v16_lt (value : Int32) : v16 value < 65536 := by
  unfold v16; exact UInt16.toNat_lt _

theorem shlUs_eq (value c : Int32) (h0 : 0 ≤ c.toInt) (h1 : c.toInt ≤ 31)
    (h2 : v16 value * 2 ^ c.toInt.toNat < 2147483648) : shlUs value c = pure (v16 value * 2 ^ c.toInt.toNat) := by
  funext h
  have : ¬ (c.toInt < 0 ∨ 31 < c.toInt) := by omega
  have h3 : ¬ ((i2us value).toNat * 2 ^ c.toInt.toNat ≥ 2147483648) := by unfold v16 at h2; omega
  simp only [shlUs, this, h3, ite_false]
  rfl

theorem shrUs_eq (value c : Int32) (h0 : 0 ≤ c.toInt) (h1 : c.toInt ≤ 31) :
    shrUs value c = pure (UInt16.ofNat (v16 value >>> c.toInt.toNat)) := by
  funext h
  have : ¬ (c.toInt < 0 ∨ 31 < c.toInt) := by omega
  simp only [shrUs, this, ite_false]
  rfl

theorem i32_lt_iff {a b : Int32} : a < b ↔ a.toInt < b.toInt := Int32.lt_iff_toInt_lt


theorem pow_mul_lt (v n m : Nat) (hv : v < 2 ^ n) : v * 2 ^ m < 2 ^ (n + m) := by
  rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hv (Nat.pow_pos (by omega))

theorem send_bits_B {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hr : TreesRun id d) (value len : Int32)
    (hl0 : 0 ≤ len.toInt) (hl1 : len.toInt ≤ 15) (hv : v16 value < 2 ^ len.toInt.toNat)
    (hcase : d.bi_valid.toInt + len.toInt ≤ 16) :
    send_bits (some (.tab id)) value len h =
      .ok ((), setD h id { d with
        bi_buf := UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat),
        bi_valid := Int32.ofInt (d.bi_valid.toInt + len.toInt) }) := by
  have hbl := hr.bi_lo
  have hbh := hr.bi_hi
  have hlt := pow_mul_lt _ _ d.bi_valid.toInt.toNat hv
  have hpow : 2 ^ (len.toInt.toNat + d.bi_valid.toInt.toNat) ≤ 2 ^ 16 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hsh := shlUs_eq value d.bi_valid hr.bi_lo (by have := hr.bi_hi; omega) (by omega)
  have hsub := isub_eq (a := Buf_size) (b := len) (by rw [Buf_size_toInt]; omega) (by rw [Buf_size_toInt]; omega)
  have hnc : ¬ (d.bi_valid > Int32.ofInt (Buf_size.toInt - len.toInt)) := by
    rw [gt_iff_lt, i32_lt_iff, i32_ofInt_toInt (by rw [Buf_size_toInt]; omega) (by rw [Buf_size_toInt]; omega),
      Buf_size_toInt]
    omega
  unfold send_bits
  rw [bind_app, rd_run hb.dstate]
  simp only []
  rw [bind_app, hsub]
  simp only [pure_app, hnc, ite_false]
  rw [bind_app, hsh]
  simp only [pure_app]
  rw [bind_app, md_run hb.dstate]
  simp only []
  have hd1 : (setD h id { d with bi_buf := UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat) }).dstates id
      = some _ := setD_dstates_same _ _ _
  rw [bind_app, rd_run hd1]
  simp only []
  have hadd := iadd_eq (a := d.bi_valid) (b := len) (by omega) (by omega)
  rw [bind_app, hadd]
  simp only [pure_app]
  rw [md_run hd1]
  simp


theorem TreesBase.stepD {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (d' : DeflateState)
    (hw : d'.WellFormed) (h1 : d'.pending_buf = d.pending_buf) (h2 : d'.pending_buf_size = d.pending_buf_size)
    (h3 : d'.sym_buf = d.sym_buf) (h4 : d'.lit_bufsize = d.lit_bufsize) (h5 : d'.sym_end = d.sym_end)
    (h6 : d'.pending.toNat ≤ d'.pending_buf_size.toNat) :
    TreesBase (setD h id d') id d' b buf where
  dstate := by simp
  wf := hw
  static := by simpa using hb.static
  pbuf := by rw [h1]; exact hb.pbuf
  bytes := by simpa using hb.bytes
  rw := by simpa using hb.rw
  size := by rw [h4]; exact hb.size
  psize := by rw [h2]; exact hb.psize
  sym := by rw [h3, h4]; exact hb.sym
  lit_lo := by rw [h4]; exact hb.lit_lo
  lit_hi := by rw [h4]; exact hb.lit_hi
  sym_end := by rw [h5, h4]; exact hb.sym_end
  pending_le := h6

theorem send_bits_A {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hr : TreesRun id d) (value len : Int32)
    (hl0 : 0 ≤ len.toInt) (hl1 : len.toInt ≤ 15) (hv : v16 value < 2 ^ len.toInt.toNat)
    (hcase : 16 < d.bi_valid.toInt + len.toInt) (hroom : d.pending.toNat + 2 ≤ buf.size) :
    send_bits (some (.tab id)) value len h =
      .ok ((), setD (setB h b ((buf.set! d.pending.toNat
            (UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat) &&& 0xff).toUInt8).set!
            (d.pending.toNat + 1) (UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat) >>> 8).toUInt8))
        id { d with
          pending := d.pending + 2,
          bi_buf := UInt16.ofNat (v16 value >>> (16 - d.bi_valid.toInt).toNat),
          bi_valid := Int32.ofInt (d.bi_valid.toInt + len.toInt - 16) }) := by
  have hbl := hr.bi_lo
  have hbh := hr.bi_hi
  have hlt := pow_mul_lt _ _ d.bi_valid.toInt.toNat hv
  have hpow : 2 ^ (len.toInt.toNat + d.bi_valid.toInt.toNat) ≤ 2 ^ 31 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hsh := shlUs_eq value d.bi_valid hr.bi_lo (by omega) (by omega)
  have hsub := isub_eq (a := Buf_size) (b := len) (by rw [Buf_size_toInt]; omega) (by rw [Buf_size_toInt]; omega)
  have hc : d.bi_valid > Int32.ofInt (Buf_size.toInt - len.toInt) := by
    rw [gt_iff_lt, i32_lt_iff, i32_ofInt_toInt (by rw [Buf_size_toInt]; omega) (by rw [Buf_size_toInt]; omega),
      Buf_size_toInt]
    omega
  have hb1 : TreesBase (setD h id { d with bi_buf := (UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat)) }) id { d with bi_buf := (UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat)) } b buf := hb.stepD _ hb.wf rfl rfl rfl rfl rfl hb.pending_le
  have hd1 : (setD h id { d with bi_buf := (UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat)) }).dstates id = some { d with bi_buf := (UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat)) } := setD_dstates_same _ _ _
  have hsr : isub Buf_size d.bi_valid = pure (Int32.ofInt (16 - d.bi_valid.toInt)) :=
    isub_eq (by rw [Buf_size_toInt]; omega) (by rw [Buf_size_toInt]; omega) |>.trans (by rw [Buf_size_toInt])
  have hrr := shrUs_eq value (Int32.ofInt (16 - d.bi_valid.toInt)) (by rw [i32_ofInt_toInt (by omega) (by omega)]; omega)
    (by rw [i32_ofInt_toInt (by omega) (by omega)]; omega)
  rw [i32_ofInt_toInt (by omega) (by omega)] at hrr
  have hsl : isub len Buf_size = pure (Int32.ofInt (len.toInt - 16)) :=
    isub_eq (by rw [Buf_size_toInt]; omega) (by rw [Buf_size_toInt]; omega) |>.trans (by rw [Buf_size_toInt])
  unfold send_bits
  rw [bind_app, rd_run hb.dstate]
  simp only []
  rw [bind_app, hsub]
  simp only [pure_app, hc, ite_true]
  rw [bind_app, hsh]
  simp only [pure_app]
  rw [bind_app, md_run hb.dstate]
  simp only []
  -- put_short s (← rd s).bi_buf
  rw [bind_app, rd_run hd1]
  simp only []
  rw [bind_app, put_short_run hb1 (by simpa using hroom)]
  simp only [setD_setB, setD_setD]
  have hadd : iadd d.bi_valid (Int32.ofInt (len.toInt - 16)) =
      pure (Int32.ofInt (d.bi_valid.toInt + len.toInt - 16)) := by
    rw [iadd_eq (by rw [i32_ofInt_toInt (by omega) (by omega)]; omega)
      (by rw [i32_ofInt_toInt (by omega) (by omega)]; omega), i32_ofInt_toInt (by omega) (by omega)]
    simp only [Int.add_sub_assoc]
  simp (disch := simp [hb.dstate]) only [bind_app, rd_run', md_run', hsr, hrr, hsl, hadd, pure_app, rdD_setD_same,
    rdD_setB, setD_setD, setD_setB]
  done


theorem setB_self {h : Heap} {b : Nat} {buf : Array UInt8} (e : h.bytes b = some buf) : setB h b buf = h := by
  have := upd_self h.bytes b buf e
  cases h; simp only [setB] at *; simp_all

theorem natBits_or_shift (old w n m : Nat) (ho : old < 2 ^ n) :
    natBits (old ||| w * 2 ^ n) (n + m) = natBits old n ++ natBits w m := by
  have hor : old ||| w * 2 ^ n = old + w * 2 ^ n := by
    rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt ho, Nat.add_comm]
  rw [hor, natBits_add]
  congr 1
  · apply natBits_congr
    rw [Nat.add_mul_mod_self_right]
  · rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)),
      Nat.div_eq_of_lt ho, Nat.zero_add]

theorem natBits_shr_lt (v n k : Nat) (hv : v < 2 ^ n) (hk : k ≤ n) : v >>> k < 2 ^ (n - k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← Nat.pow_add]
  have : n - k + k = n := by omega
  rw [this]; exact hv

theorem toNat_lo (bb : UInt16) : ((bb &&& 0xff).toUInt8).toNat = bb.toNat % 256 := by
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_and]
  rw [show (0xff : UInt16).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem natBits_word (W : UInt16) :
    natBits (((W &&& 0xff).toUInt8).toNat) 8 ++ natBits (((W >>> 8).toUInt8).toNat) 8 = natBits W.toNat 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, natBits_add]
  congr 1
  · apply natBits_congr
    rw [toNat_lo]; show W.toNat % 256 % 2 ^ 8 = W.toNat % 2 ^ 8; simp
  · apply natBits_congr
    simp [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]


theorem u16_toNat_ofNat_mod (x : Nat) : (UInt16.ofNat x).toNat = x % 65536 := by
  first | exact UInt16.toNat_ofNat x | simp | (simp [UInt16.toNat, UInt16.ofNat, BitVec.toNat_ofNat])

theorem u16_toNat_ofNat_lt {x : Nat} (hx : x < 65536) : (UInt16.ofNat x).toNat = x := by
  first | exact UInt16.toNat_ofNat_of_lt' hx | exact UInt16.toNat_ofNat_of_lt hx | (simp [UInt16.toNat_ofNat]; omega) | (simp; omega)

theorem send_bits_spec_B {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (value len : Int32)
    (hl0 : 0 ≤ len.toInt) (hl1 : len.toInt ≤ 15) (hv : v16 value < 2 ^ len.toInt.toNat)
    (hcase : d.bi_valid.toInt + len.toInt ≤ 16) :
    ∃ d', send_bits (some (.tab id)) value len h = .ok ((), setD h id d') ∧
      TreesInvAt (setD h id d') id d' b buf ∧
      outBits buf d' = outBits buf d ++ natBits (v16 value) len.toInt.toNat ∧
      d'.pending = d.pending ∧ (∃ a v, d' = { d with bi_buf := a, bi_valid := v }) := by
  obtain ⟨hb, hr⟩ := hI
  have hbl := hr.bi_lo
  have hbh := hr.bi_hi
  have hbb := hr.bi_buf
  have hlt := pow_mul_lt _ _ d.bi_valid.toInt.toNat hv
  have hpow : 2 ^ (len.toInt.toNat + d.bi_valid.toInt.toNat) ≤ 2 ^ 16 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hor : d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat < 2 ^ (d.bi_valid.toInt.toNat + len.toInt.toNat) := by
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_lt_of_le hbb (Nat.pow_le_pow_right (by omega) (by omega))
    · rw [Nat.add_comm]; exact hlt
  have hx : d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat < 65536 := by
    have : 2 ^ (d.bi_valid.toInt.toNat + len.toInt.toNat) ≤ 2 ^ 16 := by rw [Nat.add_comm]; exact hpow
    omega
  have hnv : (Int32.ofInt (d.bi_valid.toInt + len.toInt)).toInt = d.bi_valid.toInt + len.toInt :=
    i32_ofInt_toInt (by omega) (by omega)
  refine ⟨_, send_bits_B hb hr value len hl0 hl1 hv hcase, ?_, ?_, rfl, _, _, rfl⟩
  · refine ⟨hb.stepD _ hb.wf rfl rfl rfl rfl rfl hb.pending_le, ?_⟩
    refine ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, ?_, ?_, ?_, hr.sym_next_le, hr.sym_next_mod⟩
    · show 0 ≤ (Int32.ofInt _).toInt; rw [hnv]; omega
    · show (Int32.ofInt _).toInt ≤ 16; rw [hnv]; omega
    · show (UInt16.ofNat _).toNat < 2 ^ (Int32.ofInt _).toInt.toNat
      rw [hnv, u16_toNat_ofNat_lt hx]
      have : (d.bi_valid.toInt + len.toInt).toNat = d.bi_valid.toInt.toNat + len.toInt.toNat := by omega
      rw [this]; exact hor
  · unfold outBits
    show bytesBits buf d.pending.toNat ++ natBits (UInt16.ofNat _).toNat (Int32.ofInt _).toInt.toNat = _
    rw [hnv, u16_toNat_ofNat_lt hx]
    have : (d.bi_valid.toInt + len.toInt).toNat = d.bi_valid.toInt.toNat + len.toInt.toNat := by omega
    rw [this, natBits_or_shift _ _ _ _ hbb, List.append_assoc]


theorem getD_set_u8 (a : Array UInt8) (i j : Nat) (v : UInt8) :
    (a.set! i v).getD j 0 = if i = j ∧ i < a.size then v else a.getD j 0 := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < a.size <;> simp [h2]
  · simp [h1]

/-- Two bytes appended at `p`: the bits of the pending bytes grow by those of the two bytes. -/
theorem bytesBits_two {buf : Array UInt8} {p : Nat} (v0 v1 : UInt8) (hp : p + 2 ≤ buf.size) :
    bytesBits ((buf.set! p v0).set! (p + 1) v1) (p + 2) = bytesBits buf p ++ natBits v0.toNat 8 ++ natBits v1.toNat 8 := by
  have e1 : ((buf.set! p v0).set! (p + 1) v1).getD (p + 1) 0 = v1 := by
    rw [getD_set_u8]; simp; omega
  have e0 : ((buf.set! p v0).set! (p + 1) v1).getD p 0 = v0 := by
    rw [getD_set_u8, getD_set_u8]; simp
    intro h; omega
  rw [show p + 2 = (p + 1) + 1 from rfl, bytesBits_succ, bytesBits_succ, bytesBits_set _ (by omega),
    bytesBits_set _ (by omega), e1, e0]


theorem send_bits_spec_A {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (value len : Int32)
    (hl0 : 0 ≤ len.toInt) (hl1 : len.toInt ≤ 15) (hv : v16 value < 2 ^ len.toInt.toNat)
    (hcase : 16 < d.bi_valid.toInt + len.toInt) (hroom : d.pending.toNat + 2 ≤ buf.size) :
    ∃ buf' d', send_bits (some (.tab id)) value len h = .ok ((), setD (setB h b buf') id d') ∧
      TreesInvAt (setD (setB h b buf') id d') id d' b buf' ∧
      outBits buf' d' = outBits buf d ++ natBits (v16 value) len.toInt.toNat ∧
      buf'.size = buf.size ∧
      (∀ i, (i < d.pending.toNat ∨ d.pending.toNat + 2 ≤ i) → buf'.getD i 0 = buf.getD i 0) ∧
      d'.pending = d.pending + 2 ∧ (∃ a v, d' = { d with pending := d.pending + 2, bi_buf := a, bi_valid := v }) := by
  obtain ⟨hb, hr⟩ := hI
  have hbl := hr.bi_lo
  have hbh := hr.bi_hi
  have hbb := hr.bi_buf
  have hp := hb.pending_small
  have hp2 := toNat_add_two_u64 hp
  have hs1 := hb.size
  have hs2 := hb.lit_hi
  have hpsz := hb.psize
  have hvl := v16_lt value
  obtain ⟨W, hW⟩ : ∃ W, W = UInt16.ofNat (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat) := ⟨_, rfl⟩
  have hA := send_bits_A hb hr value len hl0 hl1 hv hcase hroom
  rw [← hW] at hA
  have hnv : (Int32.ofInt (d.bi_valid.toInt + len.toInt - 16)).toInt = d.bi_valid.toInt + len.toInt - 16 :=
    i32_ofInt_toInt (by omega) (by omega)
  have hshr : v16 value >>> (16 - d.bi_valid.toInt).toNat < 2 ^ (d.bi_valid.toInt + len.toInt - 16).toNat := by
    have := natBits_shr_lt (v16 value) len.toInt.toNat (16 - d.bi_valid.toInt).toNat hv (by omega)
    have e : len.toInt.toNat - (16 - d.bi_valid.toInt).toNat = (d.bi_valid.toInt + len.toInt - 16).toNat := by omega
    rwa [e] at this
  have hsr : v16 value >>> (16 - d.bi_valid.toInt).toNat ≤ v16 value := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  have hbuf2 : ((buf.set! d.pending.toNat (W &&& 0xff).toUInt8).set! (d.pending.toNat + 1) (W >>> 8).toUInt8).size
      = buf.size := by simp
  refine ⟨_, _, hA, ?_, ?_, hbuf2, ?_, ?_, _, _, rfl⟩
  · refine ⟨hb.step _ hbuf2 _ hb.wf rfl rfl rfl rfl rfl (by simp only []; rw [hp2]; omega), ?_⟩
    refine ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, ?_, ?_, ?_, hr.sym_next_le, hr.sym_next_mod⟩
    · show 0 ≤ (Int32.ofInt _).toInt; rw [hnv]; omega
    · show (Int32.ofInt _).toInt ≤ 16; rw [hnv]; omega
    · show (UInt16.ofNat _).toNat < 2 ^ (Int32.ofInt _).toInt.toNat
      rw [hnv, u16_toNat_ofNat_lt (by omega)]
      exact hshr
  · unfold outBits
    show bytesBits _ (d.pending + 2).toNat ++ natBits (UInt16.ofNat _).toNat (Int32.ofInt _).toInt.toNat = _
    rw [hp2, bytesBits_two _ _ (by omega), hnv, u16_toNat_ofNat_lt (by omega)]
    have hw16 : natBits (((W &&& 0xff).toUInt8).toNat) 8 ++ natBits (((W >>> 8).toUInt8).toNat) 8
        = natBits d.bi_buf.toNat d.bi_valid.toInt.toNat ++ natBits (v16 value) (16 - d.bi_valid.toInt).toNat := by
      rw [natBits_word]
      have : natBits W.toNat 16
          = natBits (d.bi_buf.toNat ||| v16 value * 2 ^ d.bi_valid.toInt.toNat) 16 := by
        apply natBits_congr
        rw [hW, u16_toNat_ofNat_mod]; simp
      rw [this, show (16 : Nat) = d.bi_valid.toInt.toNat + (16 - d.bi_valid.toInt).toNat by omega,
        natBits_or_shift _ _ _ _ hbb]
    have hsplit : natBits (v16 value) len.toInt.toNat =
        natBits (v16 value) (16 - d.bi_valid.toInt).toNat ++
          natBits (v16 value >>> (16 - d.bi_valid.toInt).toNat) (d.bi_valid.toInt + len.toInt - 16).toNat := by
      rw [← natBits_add]; congr 1; omega
    rw [hsplit]
    have := congrArg (· ++ natBits (v16 value >>> (16 - d.bi_valid.toInt).toNat)
      (d.bi_valid.toInt + len.toInt - 16).toNat) hw16
    simp only [List.append_assoc] at this ⊢
    rw [this]
  · intro i hi
    have h1 : ¬ (d.pending.toNat + 1 = i) := by omega
    have h2 : ¬ (d.pending.toNat = i) := by omega
    rw [getD_set_u8, getD_set_u8]
    simp [h1, h2]
  · rfl


/-- **`send_bits`, safety and specification.** `send_bits(s, value, length)` appends the `length` low bits of `value`
(least significant first) to the output bit stream `outBits`: the bits of the pending bytes followed by those of
`bi_buf`. Preconditions: `TreesInvAt` (so `bi_valid <= 16`, no stray bits in `bi_buf`); `0 <= length <= 15` (every
caller in `trees.c` sends at most 15 bits: codes have length at most 15, extra bits at most 13);
`(ush)value < 2^length` (the value has no bits above its length: true for the codes of `gen_codes`, for the extra
bits, and for the block header); and room: the bits already written plus `length` fit in `pending_buf`
(`8 * pending + bi_valid + length <= 8 * pending_buf_size`; `deflate.c` establishes this by the overlay lemma F9).
Afterwards: no fault, `TreesInvAt` again for the same byte block `b`, the stream grew by exactly the bits, at most
two bytes were written at `pending_buf[pending]` and the bytes outside `[pending, pending')` are unchanged. -/
theorem send_bits_spec {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (value len : Int32)
    (hl0 : 0 ≤ len.toInt) (hl1 : len.toInt ≤ 15) (hv : v16 value < 2 ^ len.toInt.toNat)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + len.toInt.toNat ≤ 8 * buf.size) :
    ∃ buf' d', send_bits (some (.tab id)) value len h = .ok ((), setD (setB h b buf') id d') ∧
      TreesInvAt (setD (setB h b buf') id d') id d' b buf' ∧
      outBits buf' d' = outBits buf d ++ natBits (v16 value) len.toInt.toNat ∧
      buf'.size = buf.size ∧
      (∀ i, (i < d.pending.toNat ∨ d'.pending.toNat ≤ i) → buf'.getD i 0 = buf.getD i 0) ∧
      d.pending.toNat ≤ d'.pending.toNat ∧ d'.pending.toNat ≤ d.pending.toNat + 2 ∧
      (∃ p a v, d' = { d with pending := p, bi_buf := a, bi_valid := v }) := by
  have hbl := hI.run.bi_lo
  have hbh := hI.run.bi_hi
  by_cases hcase : d.bi_valid.toInt + len.toInt ≤ 16
  · obtain ⟨d', e, hinv, hbits, hpend, a, v, hd'⟩ := send_bits_spec_B hI value len hl0 hl1 hv hcase
    refine ⟨buf, d', ?_, ?_, hbits, rfl, fun _ _ => rfl, by rw [hpend]; exact Nat.le_refl _,
      by rw [hpend]; omega, ?_⟩
    · rw [setB_self hI.base.bytes]; exact e
    · rw [setB_self hI.base.bytes]; exact hinv
    · exact ⟨d.pending, a, v, by rw [hd']⟩
  · have hcase' : 16 < d.bi_valid.toInt + len.toInt := by omega
    have hpe := hI.base.pending_small
    obtain ⟨buf', d', e, hinv, hbits, hsz, hfr, hpend, a, v, hd'⟩ :=
      send_bits_spec_A hI value len hl0 hl1 hv hcase' (by omega)
    have hp2 := toNat_add_two_u64 hpe
    refine ⟨buf', d', e, hinv, hbits, hsz, ?_, by rw [hpend, hp2]; omega, by rw [hpend, hp2]; omega,
      ⟨_, a, v, hd'⟩⟩
    intro i hi
    apply hfr
    rw [hpend, hp2] at hi
    omega


theorem i32_beq_toInt (a b : Int32) : (a == b) = decide (a.toInt = b.toInt) := by
  by_cases h : a = b
  · subst h; simp
  · have : a.toInt ≠ b.toInt := fun e => h (Int32.toInt_inj.mp e)
    simp [h, this]

theorem i32_le_toInt {a b : Int32} : a ≤ b ↔ a.toInt ≤ b.toInt := Int32.le_iff_toInt_le

theorem i32_16 : (16 : Int32).toInt = 16 := by decide
theorem i32_8 : (8 : Int32).toInt = 8 := by decide
theorem i32_0 : (0 : Int32).toInt = 0 := by decide

theorem u16_shr8_toNat (w : UInt16) : (w >>> 8).toNat = w.toNat / 256 := by
  simp [Nat.shiftRight_eq_div_pow]

theorem bi_flush_16 {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hv : d.bi_valid.toInt = 16) (hroom : d.pending.toNat + 2 ≤ buf.size) :
    bi_flush (some (.tab id)) h =
      .ok ((), setD (setB h b ((buf.set! d.pending.toNat (d.bi_buf &&& 0xff).toUInt8).set! (d.pending.toNat + 1)
          (d.bi_buf >>> 8).toUInt8)) id { d with pending := d.pending + 2, bi_buf := 0, bi_valid := 0 }) := by
  have hc : (d.bi_valid == 16) = true := by rw [i32_beq_toInt, i32_16]; simp [hv]
  unfold bi_flush
  rw [bind_app, rd_run hb.dstate]
  simp only [hc, ite_true]
  rw [bind_app, rd_run hb.dstate]
  simp only []
  rw [bind_app, put_short_run hb hroom]
  simp (disch := simp [hb.dstate]) only [setD_setB, setD_setD, bind_app, rd_run', md_run', rdD_setD_same, rdD_setB,
    setD_setB]


theorem bi_flush_mid {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hv8 : 8 ≤ d.bi_valid.toInt) (hv16 : d.bi_valid.toInt < 16)
    (hroom : d.pending.toNat + 1 ≤ buf.size) :
    bi_flush (some (.tab id)) h =
      .ok ((), setD (setB h b (buf.set! d.pending.toNat d.bi_buf.toUInt8)) id
        { d with pending := d.pending + 1, bi_buf := d.bi_buf >>> 8,
                 bi_valid := Int32.ofInt (d.bi_valid.toInt - 8) }) := by
  have hc : (d.bi_valid == 16) = false := by rw [i32_beq_toInt, i32_16]; simp; omega
  have hge : d.bi_valid ≥ 8 := by
    show 8 ≤ d.bi_valid
    rw [i32_le_toInt, i32_8]; exact hv8
  have hsub : isub d.bi_valid 8 = pure (Int32.ofInt (d.bi_valid.toInt - 8)) :=
    (isub_eq (a := d.bi_valid) (b := 8) (by rw [i32_8]; omega) (by rw [i32_8]; omega)).trans (by rw [i32_8])
  have hp := hb.pending_small
  have hs1 := hb.size
  have hs2 := hb.lit_hi
  have hp1 := toNat_add_one_u64 hp
  unfold bi_flush
  rw [bind_app, rd_run hb.dstate]
  simp only [hc, hge, ite_true, ite_false, Bool.false_eq_true]
  rw [bind_app, rd_run hb.dstate]
  simp only []
  rw [bind_app, put_byte_run hb hroom]
  simp (disch := simp [hb.dstate]) only [setD_setB, setD_setD, bind_app, rd_run', md_run', rdD_setD_same, rdD_setB,
    hsub, pure_app]

theorem bi_flush_low {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d)
    (hv8 : d.bi_valid.toInt < 8) : bi_flush (some (.tab id)) h = .ok ((), h) := by
  have hc : (d.bi_valid == 16) = false := by rw [i32_beq_toInt, i32_16]; simp; omega
  have hge : ¬ d.bi_valid ≥ 8 := by
    show ¬ 8 ≤ d.bi_valid
    rw [i32_le_toInt, i32_8]; omega
  unfold bi_flush
  rw [bind_app, rd_run hd]
  simp only [hc, hge, ite_true, ite_false, Bool.false_eq_true]
  rfl


theorem setD_self {h : Heap} {id : Nat} {d : DeflateState} (e : h.dstates id = some d) : setD h id d = h := by
  have := upd_self h.dstates id d e
  cases h; simp only [setD] at *; simp_all

theorem bytesBits_one {buf : Array UInt8} {p : Nat} (v : UInt8) (hp : p < buf.size) :
    bytesBits (buf.set! p v) (p + 1) = bytesBits buf p ++ natBits v.toNat 8 := by
  rw [bytesBits_succ, bytesBits_set _ (Nat.le_refl _)]
  rw [show (buf.set! p v).getD p 0 = v by rw [getD_set_u8]; simp; omega]

theorem natBits_byte (w : UInt16) : natBits (w.toUInt8).toNat 8 = natBits w.toNat 8 := by
  apply natBits_congr
  rw [UInt16.toNat_toUInt8]; simp

theorem TreesRun.with_bi {id : Nat} {d : DeflateState} (hr : TreesRun id d) (d' : DeflateState)
    (h1 : d'.l_desc = d.l_desc) (h2 : d'.d_desc = d.d_desc) (h3 : d'.bl_desc = d.bl_desc)
    (h4 : 0 ≤ d'.bi_valid.toInt) (h5 : d'.bi_valid.toInt ≤ 16)
    (h6 : d'.bi_buf.toNat < 2 ^ d'.bi_valid.toInt.toNat) (h7 : d'.sym_next = d.sym_next)
    (h8 : d'.sym_end = d.sym_end) : TreesRun id d' where
  ldyn := by rw [h1]; exact hr.ldyn
  lstat := by rw [h1]; exact hr.lstat
  ddyn := by rw [h2]; exact hr.ddyn
  dstat := by rw [h2]; exact hr.dstat
  bldyn := by rw [h3]; exact hr.bldyn
  blstat := by rw [h3]; exact hr.blstat
  bi_lo := h4
  bi_hi := h5
  bi_buf := h6
  sym_next_le := by rw [h7, h8]; exact hr.sym_next_le
  sym_next_mod := by rw [h7]; exact hr.sym_next_mod

/-- **`bi_flush`, safety and specification.** Writes the complete bytes of `bi_buf` to the pending output: the
output bit stream `outBits` is unchanged and `bi_valid < 8` afterwards. Precondition: `TreesInvAt` and the bits
already written fit in `pending_buf` (`8 * pending + bi_valid <= 8 * pending_buf_size`, from the overlay
lemma F9; `bi_valid = 16` needs 2 bytes, `bi_valid >= 8` needs 1). Called by `_tr_flush_bits` (from
`flush_pending`) and `_tr_align`. -/
theorem bi_flush_spec {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    ∃ buf' d', bi_flush (some (.tab id)) h = .ok ((), setD (setB h b buf') id d') ∧
      TreesInvAt (setD (setB h b buf') id d') id d' b buf' ∧
      outBits buf' d' = outBits buf d ∧ d'.bi_valid.toInt < 8 ∧
      buf'.size = buf.size ∧
      (∀ i, (i < d.pending.toNat ∨ d'.pending.toNat ≤ i) → buf'.getD i 0 = buf.getD i 0) ∧
      d.pending.toNat ≤ d'.pending.toNat ∧ d'.pending.toNat ≤ d.pending.toNat + 2 ∧
      (∃ p a v, d' = { d with pending := p, bi_buf := a, bi_valid := v }) := by
  obtain ⟨hb, hr⟩ := hI
  have hbl := hr.bi_lo
  have hbh := hr.bi_hi
  have hbb := hr.bi_buf
  have hp := hb.pending_small
  have hs1 := hb.size
  have hs2 := hb.lit_hi
  have hp1 := toNat_add_one_u64 hp
  have hpsz := hb.psize
  by_cases h16 : d.bi_valid.toInt = 16
  · have hroom2 : d.pending.toNat + 2 ≤ buf.size := by
      have : d.bi_valid.toInt.toNat = 16 := by omega
      omega
    have hp2 := toNat_add_two_u64 hp
    have hbuf2 : ((buf.set! d.pending.toNat (d.bi_buf &&& 0xff).toUInt8).set! (d.pending.toNat + 1)
        (d.bi_buf >>> 8).toUInt8).size = buf.size := by simp
    refine ⟨_, _, bi_flush_16 hb h16 hroom2, ?_, ?_, ?_, hbuf2, ?_, ?_, ?_, ⟨_, _, _, rfl⟩⟩
    · refine ⟨hb.step _ hbuf2 _ hb.wf rfl rfl rfl rfl rfl (by simp only []; rw [hp2]; omega), ?_⟩
      refine hr.with_bi _ rfl rfl rfl ?_ ?_ ?_ rfl rfl
      · show 0 ≤ (0 : Int32).toInt; rw [i32_0]; omega
      · show (0 : Int32).toInt ≤ 16; rw [i32_0]; omega
      · show (0 : UInt16).toNat < 2 ^ (0 : Int32).toInt.toNat; rw [i32_0]; simp
    · unfold outBits
      show bytesBits _ (d.pending + 2).toNat ++ natBits (0 : UInt16).toNat (0 : Int32).toInt.toNat = _
      rw [hp2, bytesBits_two _ _ (by omega), i32_0, List.append_assoc (bytesBits _ _), natBits_word, h16]
      simp [natBits]
    · show (0 : Int32).toInt < 8; rw [i32_0]; omega
    · intro i hi
      have h1 : ¬ (d.pending.toNat + 1 = i) := by simp only [] at hi; rw [hp2] at hi; omega
      have h2 : ¬ (d.pending.toNat = i) := by simp only [] at hi; rw [hp2] at hi; omega
      rw [getD_set_u8, getD_set_u8]
      simp [h1, h2]
    · show d.pending.toNat ≤ (d.pending + 2).toNat; rw [hp2]; omega
    · show (d.pending + 2).toNat ≤ _; rw [hp2]; exact Nat.le_refl _
  · by_cases h8 : 8 ≤ d.bi_valid.toInt
    · have hlt16 : d.bi_valid.toInt < 16 := by omega
      have hroom1 : d.pending.toNat + 1 ≤ buf.size := by
        have : 8 ≤ d.bi_valid.toInt.toNat := by omega
        omega
      have hbuf1 : (buf.set! d.pending.toNat d.bi_buf.toUInt8).size = buf.size := by simp
      have hnv : (Int32.ofInt (d.bi_valid.toInt - 8)).toInt = d.bi_valid.toInt - 8 :=
        i32_ofInt_toInt (by omega) (by omega)
      refine ⟨_, _, bi_flush_mid hb h8 hlt16 hroom1, ?_, ?_, ?_, hbuf1, ?_, ?_, ?_, ⟨_, _, _, rfl⟩⟩
      · refine ⟨hb.step _ hbuf1 _ hb.wf rfl rfl rfl rfl rfl (by simp only []; rw [hp1]; omega), ?_⟩
        refine hr.with_bi _ rfl rfl rfl ?_ ?_ ?_ rfl rfl
        · show 0 ≤ (Int32.ofInt _).toInt; rw [hnv]; omega
        · show (Int32.ofInt _).toInt ≤ 16; rw [hnv]; omega
        · show (d.bi_buf >>> 8).toNat < 2 ^ (Int32.ofInt _).toInt.toNat
          rw [hnv, u16_shr8_toNat]
          have := natBits_shr_lt d.bi_buf.toNat d.bi_valid.toInt.toNat 8 hbb (by omega)
          rw [Nat.shiftRight_eq_div_pow] at this
          have e : (d.bi_valid.toInt - 8).toNat = d.bi_valid.toInt.toNat - 8 := by omega
          rw [e]; simpa using this
      · unfold outBits
        show bytesBits _ (d.pending + 1).toNat ++ natBits (d.bi_buf >>> 8).toNat (Int32.ofInt _).toInt.toNat = _
        rw [hp1, bytesBits_one _ (by omega), hnv, natBits_byte, u16_shr8_toNat, List.append_assoc]
        congr 1
        have e : d.bi_valid.toInt.toNat = 8 + (d.bi_valid.toInt - 8).toNat := by omega
        conv => rhs; rw [e, natBits_add]
        rw [Nat.shiftRight_eq_div_pow]
      · show (Int32.ofInt _).toInt < 8; rw [hnv]; omega
      · intro i hi
        have h2 : ¬ (d.pending.toNat = i) := by simp only [] at hi; rw [hp1] at hi; omega
        rw [getD_set_u8]
        simp [h2]
      · show d.pending.toNat ≤ (d.pending + 1).toNat; rw [hp1]; omega
      · show (d.pending + 1).toNat ≤ _; rw [hp1]; omega
    · have hlt8 : d.bi_valid.toInt < 8 := by omega
      refine ⟨buf, d, ?_, ?_, rfl, hlt8, rfl, fun _ _ => rfl, Nat.le_refl _, by omega, ⟨_, _, _, rfl⟩⟩
      · rw [setB_self hb.bytes, setD_self hb.dstate]; exact bi_flush_low hb.dstate hlt8
      · rw [setB_self hb.bytes, setD_self hb.dstate]; exact ⟨hb, hr⟩


/-- The last part of `bi_windup`: `bi_used = ((bi_valid - 1) & 7) + 1`, then clear the bit buffer. -/
def windupTail (s : DeflateStatePtr) : M Unit := do
  let t ← isub (← rd s).bi_valid 1
  let u ← iadd (t &&& 7) 1
  md s fun d => { d with bi_used := u }
  md s fun d => { d with bi_buf := 0 }
  md s fun d => { d with bi_valid := 0 }

/-- `bi_used` as `bi_windup` computes it, for `0 <= bi_valid <= 16`. -/
def usedOf (bv : Int) : Int := if bv = 0 then 8 else (bv - 1) % 8 + 1

theorem usedOf_key : ∀ k : Fin 17, ((Int32.ofInt ((k : Int) - 1)) &&& 7).toInt + 1 = usedOf (k : Int) := by decide

theorem i32_1 : (1 : Int32).toInt = 1 := by decide

theorem windupTail_run {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d)
    (hl : 0 ≤ d.bi_valid.toInt) (hh : d.bi_valid.toInt ≤ 16) :
    windupTail (some (.tab id)) h =
      .ok ((), setD h id { d with bi_used := Int32.ofInt (usedOf d.bi_valid.toInt), bi_buf := 0, bi_valid := 0 }) := by
  have hne : h.dstates id ≠ none := by simp [hd]
  have hsub : isub d.bi_valid 1 = pure (Int32.ofInt (d.bi_valid.toInt - 1)) :=
    (isub_eq (a := d.bi_valid) (b := 1) (by rw [i32_1]; omega) (by rw [i32_1]; omega)).trans (by rw [i32_1])
  obtain ⟨n, hn⟩ : ∃ n : Nat, (n : Int) = d.bi_valid.toInt := ⟨d.bi_valid.toInt.toNat, Int.toNat_of_nonneg hl⟩
  have hkey := usedOf_key ⟨n, by omega⟩
  simp only [] at hkey
  rw [hn] at hkey
  have h1 : usedOf d.bi_valid.toInt ≤ 8 := by unfold usedOf; split <;> omega
  have h2 : 1 ≤ usedOf d.bi_valid.toInt := by unfold usedOf; split <;> omega
  have hadd : iadd (Int32.ofInt (d.bi_valid.toInt - 1) &&& 7) 1 = pure (Int32.ofInt (usedOf d.bi_valid.toInt)) := by
    rw [iadd_eq (a := Int32.ofInt (d.bi_valid.toInt - 1) &&& 7) (b := 1) (by rw [i32_1]; omega)
      (by rw [i32_1]; omega), i32_1, hkey]
  have hrd : rdD h id = d := by simp [rdD, hd]
  unfold windupTail
  simp (disch := simp [hd]) only [bind_app, rd_run', md_run', rdD_setD_same, hrd, hsub, hadd, pure_app, setD_setD]
  done


theorem i32_gt_toInt {a b : Int32} : a > b ↔ a.toInt > b.toInt := by
  rw [gt_iff_lt, Int32.lt_iff_toInt_lt]

theorem bi_windup_big {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hl : 0 ≤ d.bi_valid.toInt) (hh : d.bi_valid.toInt ≤ 16)
    (h8 : 8 < d.bi_valid.toInt) (hroom : d.pending.toNat + 2 ≤ buf.size) :
    bi_windup (some (.tab id)) h =
      .ok ((), setD (setB h b ((buf.set! d.pending.toNat (d.bi_buf &&& 0xff).toUInt8).set! (d.pending.toNat + 1)
          (d.bi_buf >>> 8).toUInt8)) id
        { d with pending := d.pending + 2, bi_used := Int32.ofInt (usedOf d.bi_valid.toInt), bi_buf := 0,
                 bi_valid := 0 }) := by
  have hc : d.bi_valid > 8 := by rw [i32_gt_toInt, i32_8]; exact h8
  unfold bi_windup
  rw [bind_app, rd_run hb.dstate]
  simp only [hc, ite_true]
  rw [bind_app, rd_run hb.dstate]
  simp only []
  rw [bind_app, put_short_run hb hroom]
  simp only []
  have hd' : (setD (setB h b ((buf.set! d.pending.toNat (d.bi_buf &&& 0xff).toUInt8).set! (d.pending.toNat + 1)
          (d.bi_buf >>> 8).toUInt8)) id { d with pending := d.pending + 2 }).dstates id
        = some { d with pending := d.pending + 2 } := by simp
  exact (windupTail_run hd' hl hh).trans (by simp only [setD_setD])

theorem bi_windup_small {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hb : TreesBase h id d b buf) (hl : 0 ≤ d.bi_valid.toInt) (hh : d.bi_valid.toInt ≤ 16)
    (h8 : d.bi_valid.toInt ≤ 8) (h0 : 0 < d.bi_valid.toInt) (hroom : d.pending.toNat + 1 ≤ buf.size) :
    bi_windup (some (.tab id)) h =
      .ok ((), setD (setB h b (buf.set! d.pending.toNat d.bi_buf.toUInt8)) id
        { d with pending := d.pending + 1, bi_used := Int32.ofInt (usedOf d.bi_valid.toInt), bi_buf := 0,
                 bi_valid := 0 }) := by
  have hc : ¬ d.bi_valid > 8 := by rw [i32_gt_toInt, i32_8]; omega
  have hc2 : d.bi_valid > 0 := by rw [i32_gt_toInt, i32_0]; exact h0
  unfold bi_windup
  rw [bind_app, rd_run hb.dstate]
  simp only [hc, hc2, ite_true, ite_false]
  rw [bind_app, rd_run hb.dstate]
  simp only []
  rw [bind_app, put_byte_run hb hroom]
  simp only []
  have hd' : (setD (setB h b (buf.set! d.pending.toNat d.bi_buf.toUInt8)) id { d with pending := d.pending + 1 }).dstates id
        = some { d with pending := d.pending + 1 } := by simp
  exact (windupTail_run hd' hl hh).trans (by simp only [setD_setD])

theorem bi_windup_zero {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d)
    (hl : d.bi_valid.toInt = 0) :
    bi_windup (some (.tab id)) h =
      .ok ((), setD h id { d with bi_used := Int32.ofInt (usedOf d.bi_valid.toInt), bi_buf := 0, bi_valid := 0 }) := by
  have hc : ¬ d.bi_valid > 8 := by rw [i32_gt_toInt, i32_8]; omega
  have hc2 : ¬ d.bi_valid > 0 := by rw [i32_gt_toInt, i32_0]; omega
  unfold bi_windup
  rw [bind_app, rd_run hd]
  simp only [hc, hc2, ite_false]
  exact windupTail_run hd (by omega) (by omega)


theorem natBits_pad (w bv k : Nat) (hw : w < 2 ^ bv) : natBits w (bv + k) = natBits w bv ++ List.replicate k false := by
  rw [natBits_add, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hw, natBits_zero]

/-- **`bi_windup`, safety and specification.** Flushes the bit buffer to a byte boundary: the output bit stream
gets `(8 - bi_valid % 8) % 8` zero bits appended (the padding), `bi_buf = bi_valid = 0` and
`bi_used = ((bi_valid - 1) & 7) + 1` (`usedOf`). Precondition: `TreesInvAt` and room for the pending bits
(`8 * pending + bi_valid <= 8 * pending_buf_size`, F9). Called by `_tr_stored_block` and `_tr_flush_block`. -/
theorem bi_windup_spec {h : Heap} {id : Nat} {d : DeflateState} {b : Nat} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    ∃ buf' d', bi_windup (some (.tab id)) h = .ok ((), setD (setB h b buf') id d') ∧
      TreesInvAt (setD (setB h b buf') id d') id d' b buf' ∧
      outBits buf' d' = outBits buf d ++ List.replicate ((8 - d.bi_valid.toInt.toNat % 8) % 8) false ∧
      d'.bi_valid.toInt = 0 ∧ d'.bi_buf = 0 ∧ d'.bi_used.toInt = usedOf d.bi_valid.toInt ∧
      buf'.size = buf.size ∧
      (∀ i, (i < d.pending.toNat ∨ d'.pending.toNat ≤ i) → buf'.getD i 0 = buf.getD i 0) ∧
      d.pending.toNat ≤ d'.pending.toNat ∧ d'.pending.toNat ≤ d.pending.toNat + 2 ∧
      (∃ p u, d' = { d with pending := p, bi_used := u, bi_buf := 0, bi_valid := 0 }) := by
  obtain ⟨hb, hr⟩ := hI
  have hbl := hr.bi_lo
  have hbh := hr.bi_hi
  have hbb := hr.bi_buf
  have hp := hb.pending_small
  have hs1 := hb.size
  have hs2 := hb.lit_hi
  have hp1 := toNat_add_one_u64 hp
  have hpsz := hb.psize
  have hu : (Int32.ofInt (usedOf d.bi_valid.toInt)).toInt = usedOf d.bi_valid.toInt := by
    have h1 : usedOf d.bi_valid.toInt ≤ 8 := by unfold usedOf; split <;> omega
    have h2 : 1 ≤ usedOf d.bi_valid.toInt := by unfold usedOf; split <;> omega
    exact i32_ofInt_toInt (by omega) (by omega)
  have hrun : ∀ (d' : DeflateState), d'.l_desc = d.l_desc → d'.d_desc = d.d_desc → d'.bl_desc = d.bl_desc →
      d'.bi_valid = 0 → d'.bi_buf = 0 → d'.sym_next = d.sym_next → d'.sym_end = d.sym_end → TreesRun id d' := by
    intro d' h1 h2 h3 h4 h5 h7 h8
    refine hr.with_bi d' h1 h2 h3 ?_ ?_ ?_ h7 h8
    · rw [h4, i32_0]; omega
    · rw [h4, i32_0]; omega
    · rw [h4, h5, i32_0]; simp
  by_cases h8 : 8 < d.bi_valid.toInt
  · have hroom2 : d.pending.toNat + 2 ≤ buf.size := by
      have : 8 < d.bi_valid.toInt.toNat := by omega
      omega
    have hp2 := toNat_add_two_u64 hp
    have hbuf2 : ((buf.set! d.pending.toNat (d.bi_buf &&& 0xff).toUInt8).set! (d.pending.toNat + 1)
        (d.bi_buf >>> 8).toUInt8).size = buf.size := by simp
    refine ⟨_, _, bi_windup_big hb hbl hbh h8 hroom2, ?_, ?_, ?_, ?_, ?_, hbuf2, ?_, ?_, ?_, ⟨_, _, rfl⟩⟩
    · exact ⟨hb.step _ hbuf2 _ hb.wf rfl rfl rfl rfl rfl (by simp only []; rw [hp2]; omega), hrun _ rfl rfl rfl rfl rfl rfl rfl⟩
    · unfold outBits
      show bytesBits _ (d.pending + 2).toNat ++ natBits (0 : UInt16).toNat (0 : Int32).toInt.toNat = _
      rw [hp2, bytesBits_two _ _ (by omega), i32_0, List.append_assoc (bytesBits _ _), natBits_word]
      have e : (16 : Nat) = d.bi_valid.toInt.toNat + (16 - d.bi_valid.toInt.toNat) := by omega
      rw [e, natBits_pad _ _ _ hbb]
      have e2 : 16 - d.bi_valid.toInt.toNat = (8 - d.bi_valid.toInt.toNat % 8) % 8 := by omega
      rw [e2]; simp [natBits]
    · exact i32_0
    · rfl
    · show Int32.toInt (Int32.ofInt _) = _; exact hu
    · intro i hi
      have h1 : ¬ (d.pending.toNat + 1 = i) := by simp only [] at hi; rw [hp2] at hi; omega
      have h2 : ¬ (d.pending.toNat = i) := by simp only [] at hi; rw [hp2] at hi; omega
      rw [getD_set_u8, getD_set_u8]
      simp [h1, h2]
    · show d.pending.toNat ≤ (d.pending + 2).toNat; rw [hp2]; omega
    · show (d.pending + 2).toNat ≤ _; rw [hp2]; omega
  · by_cases h0 : 0 < d.bi_valid.toInt
    · have hroom1 : d.pending.toNat + 1 ≤ buf.size := by
        have : 0 < d.bi_valid.toInt.toNat := by omega
        omega
      have hbuf1 : (buf.set! d.pending.toNat d.bi_buf.toUInt8).size = buf.size := by simp
      refine ⟨_, _, bi_windup_small hb hbl hbh (by omega) h0 hroom1, ?_, ?_, ?_, ?_, ?_, hbuf1, ?_, ?_, ?_, ⟨_, _, rfl⟩⟩
      · exact ⟨hb.step _ hbuf1 _ hb.wf rfl rfl rfl rfl rfl (by simp only []; rw [hp1]; omega), hrun _ rfl rfl rfl rfl rfl rfl rfl⟩
      · unfold outBits
        show bytesBits _ (d.pending + 1).toNat ++ natBits (0 : UInt16).toNat (0 : Int32).toInt.toNat = _
        rw [hp1, bytesBits_one _ (by omega), i32_0, natBits_byte]
        have hpad := natBits_pad d.bi_buf.toNat d.bi_valid.toInt.toNat (8 - d.bi_valid.toInt.toNat) hbb
        rw [show d.bi_valid.toInt.toNat + (8 - d.bi_valid.toInt.toNat) = 8 by omega] at hpad
        have e2 : 8 - d.bi_valid.toInt.toNat = (8 - d.bi_valid.toInt.toNat % 8) % 8 := by omega
        rw [hpad, e2]; simp [natBits]
      · exact i32_0
      · rfl
      · show Int32.toInt (Int32.ofInt _) = _; exact hu
      · intro i hi
        have h2 : ¬ (d.pending.toNat = i) := by simp only [] at hi; rw [hp1] at hi; omega
        rw [getD_set_u8]
        simp [h2]
      · show d.pending.toNat ≤ (d.pending + 1).toNat; rw [hp1]; omega
      · show (d.pending + 1).toNat ≤ _; rw [hp1]; omega
    · have hz : d.bi_valid.toInt = 0 := by omega
      refine ⟨buf, { d with bi_used := Int32.ofInt (usedOf d.bi_valid.toInt), bi_buf := 0, bi_valid := 0 }, ?_, ?_, ?_, i32_0, rfl, ?_, rfl, fun _ _ => rfl, Nat.le_refl _, (by show d.pending.toNat ≤ d.pending.toNat + 2; omega), ⟨_, _, rfl⟩⟩
      · rw [setB_self hb.bytes]; exact bi_windup_zero hb.dstate hz
      · rw [setB_self hb.bytes]
        exact ⟨hb.stepD _ hb.wf rfl rfl rfl rfl rfl hb.pending_le, hrun _ rfl rfl rfl rfl rfl rfl rfl⟩
      · unfold outBits
        show bytesBits buf d.pending.toNat ++ natBits (0 : UInt16).toNat (0 : Int32).toInt.toNat = _
        rw [i32_0, hz]; simp [natBits]
      · show Int32.toInt (Int32.ofInt _) = _; exact hu

end Zlib.Trees.Proofs.Out
