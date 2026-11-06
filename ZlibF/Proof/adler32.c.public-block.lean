import ZlibF.Proof.«public-adler-combine»
import ZlibF.Proof.«adler32.c.public-one»

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

def canonicalStart (a : UInt64) : UInt32 :=
  UInt32.ofNat (a.toNat % 65536 % 65521 + 65536 * (a.toNat / 65536 % 65536 % 65521))

theorem adler_format_seed (a : UInt64) (bs : List UInt8) :
    ZlibF.Spec.adler32Update (canonicalStart a) bs =
      UInt32.ofNat (Zlib.Adler32.Spec.adler32 a.toNat bs) := by
  have h := adler_fold_components bs (a.toNat % 65536 % 65521)
    (a.toNat / 65536 % 65536 % 65521) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  simpa [canonicalStart, Zlib.Adler32.Spec.adler32, Zlib.Adler32.Spec.BASE] using h

theorem adler32_z_block_format {h : Heap} {blk : Nat} {bytes : Array UInt8}
    (hb : h.bytes blk = some bytes) (a : UInt64) (off L : Nat)
    (hfit : off + L ≤ bytes.size) (hL : L < 2 ^ 64) (h1 : L ≠ 1) :
    C.run (adler32_z a (.ref (.blk blk) off) L.toUInt64) h =
      .ok ((ZlibF.Spec.adler32Update (canonicalStart a) (seg bytes off L)).toUInt64, h) := by
  obtain ⟨r, hr, hv⟩ := adler32_z_correct_ne_one h blk bytes hb a off L hfit hL h1
  rw [hr]
  congr 2
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, adler_format_seed, UInt32.toNat_ofNat', hv]
  have h := sums_lt (a.toNat % 65536 % 65521) (a.toNat / 65536 % 65536 % 65521)
    (seg bytes off L) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  change (sums _ _ _).1 < 65521 ∧ (sums _ _ _).2 < 65521 at h
  have he : Zlib.Adler32.Spec.adler32 a.toNat (seg bytes off L) < 2 ^ 32 := by
    unfold Zlib.Adler32.Spec.adler32
    simp only [Zlib.Adler32.Spec.BASE]
    omega
  exact (Nat.mod_eq_of_lt he).symm


theorem seg_eq_slice (bytes : Array UInt8) (off L : Nat) (hfit : off + L ≤ bytes.size) :
    seg bytes off L = (bytes.toList.drop off).take L := by
  apply List.ext_getElem
  · have hlen : L ≤ bytes.size - off := by omega
    simp [seg, List.length_take, List.length_drop, Nat.min_eq_left hlen]
  · intro i hi hj
    have hlen : i < L := by simpa [seg] using hi
    have hidx : off + i < bytes.size := by omega
    simp only [seg, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop, Array.getElem_toList]
    exact (getElem_eq_bang bytes (off+i) hidx).symm

#print axioms adler32_z_block_format
#print axioms seg_eq_slice
end Zlib.Adler32.Proofs
