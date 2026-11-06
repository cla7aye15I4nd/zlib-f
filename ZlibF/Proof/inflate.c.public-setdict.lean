import ZlibF.Proof.«inflate.c.dict»
import ZlibF.Proof.«adler32.c.public-any»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Adler32.Proofs ZlibF.Spec

theorem adler32_dict_any {h : Heap} {ref : BRef} {off : Nat} {a : Array UInt8}
    (ha : Space.get h ref = some a) (len : UInt32) (hf : off + len.toNat ≤ a.size) :
    Zlib.Adler32.adler32 1 (.ref ref off) len h =
      .ok ((ZlibF.Spec.adler32 (seg a off len.toNat)).toUInt64, h) := by
  by_cases h1 : len.toNat = 1
  · have he : len = 1 := UInt32.toNat_inj.mp (by simpa using h1)
    subst len
    have hr := adler32_z_one_public (h := h) (r := ref) (off := off) (bytes := a) ha (by simpa using hf) 1
    change Zlib.Adler32.adler32 1 (.ref ref off) 1 h = .ok ((ZlibF.Spec.adler32 (seg a off 1)).toUInt64, h)
    rw [seg_one]
    unfold Zlib.Adler32.adler32
    change C.run (Zlib.Adler32.adler32_z 1 (.ref ref off) 1) h = _
    rw [hr]
    congr 2
    apply UInt64.toNat_inj.mp
    have hb := UInt8.toNat_lt a[off]!
    have hsmall : (1 + a[off]!.toNat) % 65521 = 1 + a[off]!.toNat := Nat.mod_eq_of_lt (by omega)
    have h32 : (1 + a[off]!.toNat) * 65536 + (1 + a[off]!.toNat) < 2 ^ 32 := by omega
    have h64 : (1 + a[off]!.toNat) + 65536 * (1 + a[off]!.toNat) < 2 ^ 64 := by omega
    simp [ZlibF.Spec.adler32, ZlibF.Spec.adler32Update, ZlibF.Spec.adlerStep,
      hsmall,
      Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, show ¬ 65521 ≤ 1 + a[off]!.toNat by omega]
    omega
  · have hr := adler32_any_format ha 1 off len hf h1
    simpa [C.run, canonicalStart, ZlibF.Spec.adler32] using hr

#print axioms adler32_dict_any
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Adler32.Proofs ZlibF.Spec

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`
rejects an incorrect dictionary without modifying the heap, for every represented
readable byte object. The stream must be in DICT mode. -/
theorem inflateSetDictionary_dataerr_any {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {ref : BRef} {off : Nat} {data : Array UInt8} {len : UInt32}
    (hl : Live H r zs z st) (hd : Space.get H ref = some data)
    (hf : off + len.toNat ≤ data.size) (hm : st.mode = DICT)
    (hbad : (ZlibF.Spec.adler32 (seg data off len.toNat)).toUInt64 ≠ st.check) :
    C.run (inflateSetDictionary (some r) (.ref ref off) len) H = .ok (Z_DATA_ERROR, H) := by
  have hnn : (Ptr.ref ref off == (Ptr.null : BPtr)) = false := by simp
  have hra := adler32_dict_any hd len hf
  have hne : ((ZlibF.Spec.adler32 (seg data off len.toNat)).toUInt64 != st.check) = true := by simpa using hbad
  show inflateSetDictionary (some r) (.ref ref off) len H = _
  unfold inflateSetDictionary
  simp only [bind_app, stateCheck_live hl, ldZ_eq, ldI_eq, hl.hz, hl.zst, castI, hl.hs, hnn, bne_self_eq_false,
    Bool.or_self, Bool.false_eq_true, ite_false, hm, beq_self_eq_true, Bool.and_false, ite_true]
  simp only [adler32_init, hra, hne, ite_true]
  rfl

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`
rejects a null source or a wrapped stream outside DICT mode before reading the source. -/
theorem inflateSetDictionary_refused_any {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hl : Live H r zs z st) (source : BPtr) (len : UInt32)
    (hn : source = .null ∨ (st.wrap ≠ 0 ∧ st.mode ≠ DICT)) :
    C.run (inflateSetDictionary (some r) source len) H = .ok (Z_STREAM_ERROR, H) := by
  show inflateSetDictionary (some r) source len H = _
  unfold inflateSetDictionary
  rcases hn with hn | ⟨hw, hm⟩
  · simp [bind_app, stateCheck_live hl, hn, pure_app]
  · by_cases he : source = .null
    · simp [bind_app, stateCheck_live hl, he, pure_app]
    · simp [bind_app, stateCheck_live hl, ldZ_eq, ldI_eq, hl.hz, hl.zst, castI, hl.hs, he, hw, hm, pure_app]

#print axioms inflateSetDictionary_dataerr_any
#print axioms inflateSetDictionary_refused_any
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Adler32.Proofs ZlibF.Spec

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`
returns a memory error and sets MEM when allocating the missing window fails.
The readable source can be any represented byte object. -/
theorem inflateSetDictionary_alloc_fail_any {H : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {st : InflateState} {ref : BRef} {off : Nat} {data : Array UInt8}
    {len : UInt32} (hG : Good H r zs z st) (hza : z.zalloc = .fn "zcalloc")
    (hd : Space.get H ref = some data) (hf : off + len.toNat ≤ data.size)
    (hwrap : st.wrap = 0 ∨ st.mode = DICT)
    (hcheck : st.mode = DICT → (ZlibF.Spec.adler32 (seg data off len.toNat)).toUInt64 = st.check)
    (hw : st.window = .null) (hok : ¬ H.allocOk H.nalloc = true) :
    C.run (inflateSetDictionary (some r) (.ref ref off) len) H =
      .ok (Z_MEM_ERROR, setI (setI { H with nalloc := H.nalloc + 1 } zs st) zs { st with mode := MEM }) := by
  have hl := hG.live
  have hadd : Ptr.add (Ptr.ref ref off) (len.toNat : Int) H =
      .ok (Ptr.ref ref (off + len.toNat), H) := Ptr.add_nat_ok hd hf
  have hrun := uw_alloc_fail hl hza hG.inv.win.wbits hw hok (.ref ref (off + len.toNat)) len
  have hs : (setI { H with nalloc := H.nalloc + 1 } zs st).istates zs = some st := by simp
  have hnn : (Ptr.ref ref off == (Ptr.null : BPtr)) = false := by simp
  show inflateSetDictionary (some r) (.ref ref off) len H = _
  unfold inflateSetDictionary
  simp only [bind_app, stateCheck_live hl, ldZ_eq, ldI_eq, hl.hz, hl.zst, castI, hl.hs, hnn,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  by_cases hm : st.mode = DICT
  · have hra := adler32_dict_any hd len hf
    have hck := hcheck hm
    simp only [hm, beq_self_eq_true, Bool.and_false, ite_true, adler32_init, hra, hck,
      bne_self_eq_false, Bool.false_eq_true, ite_false, hadd, hrun, bind_app, setMode, wrI_eq, hs, pure_app]
    simp only [show ((1 : Int32) != 0) = true by decide, ite_true, bind_app, wrI_eq, hs, pure_app]
  · have hw0 : st.wrap = 0 := hwrap.resolve_right hm
    have hmb : (st.mode == DICT) = false := by simpa using hm
    simp only [hmb, hw0, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Bool.and_false, hadd, hrun, bind_app, setMode, wrI_eq, hs, pure_app]
    simp only [show ((1 : Int32) != 0) = true by decide, ite_true, bind_app, wrI_eq, hs, pure_app]
    simp only [hw0]

#print axioms inflateSetDictionary_alloc_fail_any

/-- A failed window allocation leaves a valid stream in MEM mode. -/
theorem inflateSetDictionary_alloc_fail_good {H : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {st : InflateState} (hG : Good H r zs z st) :
    Good (setI (setI { H with nalloc := H.nalloc + 1 } zs st) zs { st with mode := MEM })
      r zs z { st with mode := MEM } := by
  have hL := hG.live
  have hI := hG.inv
  have hz' : r.get { H with nalloc := H.nalloc + 1 } = some z := by
    cases r <;> simpa [ZStreamRef.get] using hL.hz
  have hg : Good (setI { H with nalloc := H.nalloc + 1 } zs st) r zs z st := by
    have hs := good_set (h0 := { H with nalloc := H.nalloc + 1 }) (z0 := z) (z' := z)
      (s0 := st) (st' := st) hL.hz hL.hs hG.uniq hG.fresh hL.zst hL.zalloc hL.zfree
      hL.back hL.mode (StInv.congr (h := H) rfl rfl hI)
    rwa [ZStreamRef.put_self hz'] at hs
  exact good_state hg rfl mode_mem
    (hg.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hg.inv.bits rfl rfl rfl)

#print axioms inflateSetDictionary_alloc_fail_good
end Zlib.Inflate.Proofs
