import ZlibF.Proof.«public-adler-update»
import ZlibF.Proof.«inflate.c.base»
import ZlibF.Proof.«crc32.c.views»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The checksum selected by the actual wrapper flag, for every seed. -/
def inflateChecksumValue (flags : Int32) (check : UInt64) (bytes : List UInt8) : UInt64 :=
  if flags = 0 then adlerValue check bytes else (ZlibF.Spec.crc32Update check.toUInt32 bytes).toUInt64

/-- Both actual checksum callees accept every represented readable byte
view. The static CRC premise is an internal library invariant. No wrapper
flag or canonical-Adler-seed restriction is needed. -/
theorem UPDATE_CHECK_all_views {h : Heap} {zs : Nat} {s : InflateState} {ref : BRef}
    {off : Nat} {array : Array UInt8} {len : UInt32}
    (statics : Zlib.Crc32.Proofs.StaticsOK h) (state : h.istates zs = some s)
    (get : Space.get h ref = some array) (fit : off + len.toNat ≤ array.size) (check : UInt64) :
    UPDATE_CHECK (some (.tab zs)) check (.ref ref off) len h =
      .ok (inflateChecksumValue s.flags check ((array.toList.drop off).take len.toNat), h) := by
  by_cases flags : s.flags = 0
  · have run := ZlibF.Spec.Public.AdlerUpdateProof.adler_z_any_public get check off len.toUInt64
      (by simpa only [UInt32.toNat_toUInt64] using fit)
    have update : Zlib.Adler32.adler32 check (.ref ref off) len h =
        .ok (adlerValue check ((array.toList.drop off).take len.toNat), h) := by
      simpa only [C.run, Zlib.Adler32.adler32, UInt32.toNat_toUInt64] using run
    unfold UPDATE_CHECK
    simp only [bind_app, rdS, ldInflateState_tab state, flags, pure_app, inflateChecksumValue, ↓reduceIte]
    change Zlib.Adler32.adler32 check (.ref ref off) len h = _
    with_reducible exact update
  · have update := Zlib.Crc32.Proofs.crc32_all_byte_views h statics check ref off array get len fit
    unfold C.run at update
    unfold UPDATE_CHECK
    simp only [bind_app, rdS, ldInflateState_tab state, pure_app, bne_iff_ne, flags, ne_eq,
      not_false_eq_true, ↓reduceIte, inflateChecksumValue]
    with_reducible exact update

end Zlib.Inflate.Proofs
