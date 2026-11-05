import ZlibF.Proof.«inflate.c.start»

/-!
# inflate.c: `inflatePrime`, `inflateValidate`, `inflateUndermine`, `inflateMark`, `inflateCodesUsed`,
`inflateSyncPoint`, `inflateGetHeader`, `inflateInit_`

The integer lemmas (`mark_hi`, `u32_i64`) come from the earlier development, restated for these definitions.
-/

namespace Zlib.Inflate.Spec
open C

/-- `inflateValidate`: the wrapper bit 4 (check) is set or cleared in `wrap` and `reqwrap`. -/
def validateState (check : Int32) (st : InflateState) : InflateState :=
  { st with
    wrap := if check != 0 && st.wrap != 0 then st.wrap ||| 4 else st.wrap &&& ~~~4,
    reqwrap := if check != 0 && st.reqwrap != 0 then st.reqwrap ||| 4 else st.reqwrap &&& ~~~4 }

/-- `inflatePrime`: the `bits` low bits of `value`, as `(unsigned long)(value & ((1L << bits) - 1))`. -/
def primeBits (bits value : Int32) : UInt64 :=
  Zlib.Inflate.i2ul ((value.toInt64 &&& (((1 : Int64) <<< bits.toInt64) - 1)).toInt32)

/-- The state after `inflatePrime` inserted `bits` bits (`1 ≤ bits ≤ 16`, they fit): `hold += value << bits_in_hold`. -/
def primeState (bits value : Int32) (st : InflateState) : InflateState :=
  { st with hold := st.hold + (primeBits bits value <<< st.bits.toUInt64), bits := st.bits + Zlib.Inflate.i2u bits }

/-- The value `inflateMark` returns: `back << 16` plus the number of bytes of the current copy or match so far. -/
def markValue (st : InflateState) : Int :=
  st.back.toInt * 65536 + (if st.mode = COPY then st.length.toNat else if st.mode = MATCH then (st.was - st.length).toNat else 0)

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem mark_hi (b : Int32) :
    ((b.toInt64.toUInt64 <<< (16 : UInt64)).toInt64).toInt = b.toInt * 65536 := by
  have hb1 := b.le_toInt
  have hb2 := b.toInt_lt
  have : (b.toInt64.toUInt64 <<< (16 : UInt64)).toInt64 = b.toInt64 * 65536 := by
    apply Int64.toBitVec_inj.mp
    rw [UInt64.toBitVec_toInt64, UInt64.toBitVec_shiftLeft, Int64.toBitVec_mul, BitVec.shiftLeft_eq',
      BitVec.shiftLeft_eq_mul_twoPow]
    have e1 : ((16 : UInt64).toBitVec % 64).toNat = 16 := rfl
    rw [e1]
    have e2 : BitVec.twoPow 64 16 = (65536 : Int64).toBitVec := by decide
    rw [e2]
    rfl
  rw [this, Int64.toInt_mul]
  simp only [Int32.toInt_toInt64]
  rw [Int.bmod_eq_iff (by decide)]
  have e3 : (65536 : Int64).toInt = 65536 := by decide
  have e4 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  rw [e3, e4]
  refine ⟨by omega, by omega, by simp⟩

theorem u32_i64 (x : UInt32) : (x.toUInt64.toInt64).toInt = x.toNat := by
  have := x.toNat_lt
  rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp; omega

theorem ZStreamRef.put_self {h : Heap} {r : ZStreamRef} {z : ZStream} (e : r.get h = some z) : r.put h z = h := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at e
    simp [ZStreamRef.put, e, upd_self _ _ _ e]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at e
    obtain ⟨g, hg, hgz⟩ := Option.map_eq_some_iff.mp e
    subst hgz
    simp [ZStreamRef.put, hg, upd_self _ _ _ hg]

theorem _root_.Zlib.Inflate.Spec.StInv.of_fields {h : Heap} {zs : Nat} {st st' : InflateState} (hI : StInv h zs st)
    (l : st'.lens = st.lens) (w : st'.work = st.work) (c : st'.codes = st.codes)
    (a : st'.wbits = st.wbits) (b : st'.window = st.window) (c1 : st'.wsize = st.wsize) (d : st'.whave = st.whave)
    (e : st'.wnext = st.wnext) (f : st'.reqbits = st.reqbits) (g : st'.bits.toNat ≤ 39) (n : st'.next = st.next)
    (lc : st'.lencode = st.lencode) (dc : st'.distcode = st.distcode) : StInv h zs st' := by
  obtain ⟨⟨w1, w2, w3⟩, hw, hq, hb, ⟨hn, hp⟩⟩ := hI
  refine ⟨⟨by rw [l]; exact w1, by rw [w]; exact w2, by rw [c]; exact w3⟩,
    ⟨by rw [a]; exact hw.wbits, by rw [a, b]; exact hw.block, by rw [b, c1]; exact hw.nullws,
      by rw [a, c1]; exact hw.ws, by rw [c1, d]; exact hw.hv, by rw [c1, e]; exact hw.wn, by rw [c1, d, e]; exact hw.eq⟩,
    by rw [f]; exact hq, g, by unfold PtrInv; rw [n, lc, dc]; exact ⟨hn, hp⟩⟩

theorem good_state {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) {st' : InflateState} (hs : st'.strm = st.strm)
    (hm : HEAD ≤ st'.mode ∧ st'.mode ≤ SYNC) (hI : StInv h zs st') : Good (setI h zs st') r zs z st' := by
  have := hG.setZI (z' := z) rfl hG.live.zalloc hG.live.zfree hs hm hI
  rwa [ZStreamRef.put_self hG.live.hz] at this

/-! ### inflateValidate, inflateUndermine, inflateSyncPoint -/

/-- **inflateValidate, safety.** On an initialised stream the call returns `Z_OK`, changes only `wrap` and `reqwrap`
(`validateState`) and keeps the invariants. -/
theorem inflateValidate_safe {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) (check : Int32) :
    ∃ h', C.run (inflateValidate (some r) check) h = .ok (Z_OK, h') ∧ h' = setI h zs (validateState check st) ∧
      Good h' r zs z (validateState check st) ∧ (∀ b, h'.live b ↔ h.live b) := by
  have hL := hG.live
  have hrun : inflateValidate (some r) check h = .ok (Z_OK, setI h zs (validateState check st)) := by
    unfold inflateValidate
    isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, validateState]
  refine ⟨_, hrun, rfl, good_state hG (by simp [validateState]) (by simpa [validateState] using hL.mode)
    (hG.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hG.inv.bits rfl rfl rfl), ?_⟩
  exact fun b => (shape_setI hL.hs _).live b

/-- **inflateUndermine, safety.** The call (without `INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR`) sets `sane` to 1 and
returns `Z_DATA_ERROR`. -/
theorem inflateUndermine_safe {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) (subvert : Int32) :
    ∃ h', C.run (inflateUndermine (some r) subvert) h = .ok (Z_DATA_ERROR, h') ∧
      h' = setI h zs { st with sane := 1 } ∧ Good h' r zs z { st with sane := 1 } := by
  have hL := hG.live
  refine ⟨_, ?_, rfl, good_state hG rfl hL.mode (hG.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hG.inv.bits rfl rfl rfl)⟩
  show inflateUndermine (some r) subvert h = _
  unfold inflateUndermine
  isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs]

/-- **inflateSyncPoint, specification.** Returns 1 exactly when the mode is `STORED` and the bit buffer is empty;
nothing changes. -/
theorem inflateSyncPoint_spec {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) :
    C.run (inflateSyncPoint (some r)) h = .ok ((if st.mode = STORED ∧ st.bits = 0 then 1 else 0), h) := by
  show inflateSyncPoint (some r) h = _
  unfold inflateSyncPoint
  by_cases hc : st.mode = STORED ∧ st.bits = 0
  · isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hc.1, hc.2]
  · have : ¬ (st.mode = STORED ∧ st.bits = 0) := hc
    isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs]

theorem ofInt_toUInt64 (i : Nat) : (Int64.ofInt (i : Int)).toUInt64 = UInt64.ofNat i := by
  apply UInt64.toBitVec_inj.mp
  simp [Int64.toBitVec_ofInt]
  rfl

/-! ### inflateMark, inflateCodesUsed -/

/-- **inflateMark, specification.** The call returns `markValue st` (`back << 16` plus the length so far of a copy
or match) without a fault: no `long` overflow is possible. The heap is unchanged. -/
theorem inflateMark_spec {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) :
    ∃ v, C.run (inflateMark (some r)) h = .ok (v, h) ∧ v.toInt = markValue st := by
  have hb1 := st.back.le_toInt
  have hb2 := st.back.toInt_lt
  have hl := st.length.toNat_lt
  have hw := (st.was - st.length).toNat_lt
  have key : ∀ lo : UInt32, ∃ v, (do
      let hi : Int64 := ((st.back.toInt64.toUInt64) <<< 16).toInt64
      chkI64 (hi.toInt + lo.toNat) : M Int64) h = .ok (v, h) ∧ v.toInt = st.back.toInt * 65536 + lo.toNat := by
    intro lo
    have hlo := lo.toNat_lt
    have hm := mark_hi st.back
    have hr : -9223372036854775808 ≤ st.back.toInt * 65536 + (lo.toNat : Int) ∧
        st.back.toInt * 65536 + (lo.toNat : Int) < 9223372036854775808 := by omega
    refine ⟨Int64.ofInt (st.back.toInt * 65536 + lo.toNat), ?_, ?_⟩
    · simp only [bind_app, pure_app]
      have : (((st.back.toInt64.toUInt64) <<< 16).toInt64).toInt = st.back.toInt * 65536 := mark_hi st.back
      simp [chkI64, this, hr.1, hr.2]
    · rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have hrun : inflateMark (some r) h = (do
      let hi : Int64 := ((st.back.toInt64.toUInt64) <<< 16).toInt64
      let lo : UInt32 := if st.mode = COPY then st.length else if st.mode = MATCH then st.was - st.length else 0
      chkI64 (hi.toInt + lo.toNat) : M Int64) h := by
    unfold inflateMark
    isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs]
  rw [C.run, hrun]
  obtain ⟨v, hv, hv2⟩ := key (if st.mode = COPY then st.length else if st.mode = MATCH then st.was - st.length else 0)
  refine ⟨v, ?_, ?_⟩
  · simpa using hv
  · rw [hv2]; unfold markValue
    by_cases c1 : st.mode = COPY
    · simp [c1]
    · have hne : (MATCH : UInt32) ≠ COPY := by decide
      by_cases c2 : st.mode = MATCH
      · simp [c1, c2, hne]
      · simp [c1, c2]

/-- **inflateCodesUsed, specification.** For an initialised stream the call returns the offset of `next` in `codes`
(at most 1444) without a fault; nothing changes. -/
theorem inflateCodesUsed_spec {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) :
    ∃ i, i ≤ 1444 ∧ st.next = .ref (.istate_codes zs) i ∧
      C.run (inflateCodesUsed (some r)) h = .ok (UInt64.ofNat i, h) := by
  have hL := hG.live
  obtain ⟨i, hi, hi2⟩ := hG.inv.ptr.1
  refine ⟨i, hi2, hi, ?_⟩
  have hc : Space.get h (CodeRef.istate_codes zs) = some st.codes := by simp [Space.get, hL.hs]
  have hsz : st.codes.size = 1444 := hG.inv.wf.2.2
  have hd : OkOn h (Ptr.diff (Ptr.ref (CodeRef.istate_codes zs) i) (Ptr.ref (CodeRef.istate_codes zs) 0))
      (Int64.ofInt ((i : Int) - (0 : Nat))) :=
    Ptr.diff_ok hc (by omega) (by omega) (by omega)
  have hd' : Ptr.diff (Ptr.ref (CodeRef.istate_codes zs) i) (Ptr.ref (CodeRef.istate_codes zs) 0) h =
      .ok (Int64.ofInt ((i : Int) - (0 : Nat)), h) := hd
  rw [C.run]
  unfold inflateCodesUsed
  isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hi, codesP, hd']
  simp [ofInt_toUInt64]

end Zlib.Inflate.Proofs
