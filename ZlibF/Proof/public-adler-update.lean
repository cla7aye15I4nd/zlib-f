import ZlibF.Spec.Public.Checksums
import ZlibF.Proof.«adler32.c.public-any»
import ZlibF.Spec.Functional.Checksums

open C Zlib.Adler32 Zlib.Adler32.Spec Zlib.Adler32.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.AdlerUpdateProof

theorem adler_z_any_public {h : Heap} {ref : BRef} {data : Array UInt8}
    (hg : Space.get h ref = some data) (seed : UInt64) (off : Nat) (len : UInt64)
    (hf : off + len.toNat ≤ data.size) :
    C.run (adler32_z seed (.ref ref off) len) h =
      .ok (adlerValue seed ((data.toList.drop off).take len.toNat), h) := by
  have he : UInt64.ofNat len.toNat = len := UInt64.ofNat_toNat
  by_cases h1 : len.toNat = 1
  · have hlen : len = 1 := by apply UInt64.toNat_inj.mp; simpa using h1
    subst len
    have hr := adler32_z_one_public (h := h) (r := ref) (off := off) (bytes := data) hg (by simpa using hf) seed
    have hs := seg_eq_slice data off 1 (by simpa using hf)
    rw [seg_one] at hs
    have hout : (data.toList.drop off).take 1 = [data[off]!] := hs.symm
    simpa [adlerValue, hout] using hr
  · have hr := adler32_z_any_format hg seed off len.toNat hf len.toNat_lt h1
    rw [seg_eq_slice data off len.toNat hf] at hr
    have hl : ((data.toList.drop off).take len.toNat).length = len.toNat := by
      simp only [List.length_take, List.length_drop, Array.length_toList]
      apply Nat.min_eq_left
      omega
    have hn : ((data.toList.drop off).take len.toNat).length ≠ 1 := by omega
    unfold adlerValue
    rw [ite_eq_right hn]
    change C.run (adler32_z seed (.ref ref off) len) h =
      .ok ((ZlibF.Spec.adler32Update (canonicalStart seed) ((data.toList.drop off).take len.toNat)).toUInt64, h)
    simpa only [he] using hr

/-- `uLong adler32_z(uLong adler, const Bytef *buf, z_size_t len)` updates the checksum. -/
theorem adler_z_public : Goal.adler32_z := by
  intro h seed pointer len bytes hb
  obtain ⟨hbuf, hnull⟩ := hb
  rcases hbuf with ⟨rfl, rfl⟩ | ⟨ref, off, data, rfl, hg, hf, rfl⟩
  · have hlen : len = 0 := UInt64.toNat_inj.mp (by simpa using hnull rfl)
    subst len
    rfl
  · simpa using adler_z_any_public hg seed off len hf

/-- `uLong adler32(uLong adler, const Bytef *buf, uInt len)` has the same update contract. -/
theorem adler_public : Goal.adler32 := by
  intro h seed pointer len bytes hb
  have hr := adler_z_public h seed pointer len.toUInt64 bytes (by simpa [AdlerBufferBytes] using hb)
  simpa [Zlib.Adler32.adler32] using hr

#print axioms adler_z_public
#print axioms adler_public
end ZlibF.Spec.Public.AdlerUpdateProof
