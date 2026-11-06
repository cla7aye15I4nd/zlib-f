import ZlibF.Proof.«adler32.c»

/-! The public Adler-32 one-byte fast path, including noncanonical seeds. -/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

/-- One conditional subtraction suffices for the one-byte low component. -/
private theorem one_low (seed : UInt64) (byte : UInt8) :
    (csub ((seed &&& 65535) + byte.toUInt64) BASE).toNat =
      (seed.toNat % 65536 + byte.toNat) % 65521 := by
  have hlo : (seed &&& 65535).toNat < 65536 := by rw [low16]; omega
  have hb := byte.toNat_lt
  have hraw : ((seed &&& 65535) + byte.toUInt64).toNat =
      seed.toNat % 65536 + byte.toNat := by
    rw [add_small _ _ (by rw [UInt8.toNat_toUInt64]; omega), low16, UInt8.toNat_toUInt64]
  rw [csub_toNat, base_toNat, hraw]
  split <;> omega

/-- The high component uses one conditional subtraction, matching zlib even for
noncanonical initial checksums. -/
private theorem one_high (seed : UInt64) (byte : UInt8) :
    (csub ((seed >>> 16 &&& 65535) + csub ((seed &&& 65535) + byte.toUInt64) BASE) BASE).toNat =
      let lo := (seed.toNat % 65536 + byte.toNat) % 65521
      let total := seed.toNat / 65536 % 65536 + lo
      if 65521 ≤ total then total - 65521 else total := by
  have hhi : (seed >>> 16 &&& 65535).toNat < 65536 := by rw [high16]; omega
  have hlo : (csub ((seed &&& 65535) + byte.toUInt64) BASE).toNat < 65521 := by
    rw [one_low]; exact Nat.mod_lt _ (by decide)
  have hs : ((seed >>> 16 &&& 65535) + csub ((seed &&& 65535) + byte.toUInt64) BASE).toNat =
      seed.toNat / 65536 % 65536 + (seed.toNat % 65536 + byte.toNat) % 65521 := by
    rw [add_small _ _ (by omega), high16, one_low]
  rw [csub_toNat, base_toNat, hs]

/-- `uLong adler32_z(uLong adler, const Bytef *buf, z_size_t len)` with
`len = 1`: for every represented readable byte object and every seed, the
actual result matches the noncanonical-seed fast-path arithmetic. -/
theorem adler32_z_one_public {h : Heap} {r : BRef} {off : Nat} {bytes : Array UInt8}
    (hg : Space.get h r = some bytes) (hfit : off + 1 ≤ bytes.size) (seed : UInt64) :
    C.run (adler32_z seed (.ref r off) 1) h = .ok
      (UInt64.ofNat (let low := (seed.toNat % 65536 + bytes[off]!.toNat) % 65521
        let total := seed.toNat / 65536 % 65536 + low
        low + 65536 * (if 65521 ≤ total then total - 65521 else total)), h) := by
  have hi : off + 0 < bytes.size := by omega
  have hindex := Ptr.index_ok (h := h) (r := r) (a := bytes) (off := off) (i := 0) hg hi
  unfold OkOn at hindex
  have hindex' : index8 (.ref r off) 0 h = .ok (bytes[off]!, h) := by
    simpa [getElem_eq_bang bytes off (by omega)] using hindex
  have hr : (adler32_z seed (.ref r off) 1) h =
      .ok ((csub ((seed &&& 65535) + bytes[off]!.toUInt64) BASE |||
        (csub ((seed >>> 16 &&& 65535) + csub ((seed &&& 65535) + bytes[off]!.toUInt64) BASE) BASE <<< 16)), h) := by
    unfold adler32_z
    rw [ite_eq_left (by decide)]
    simp only [bind_app, hindex', csub]
    by_cases hlow : (seed &&& 65535) + bytes[off]!.toUInt64 ≥ BASE
    · rw [if_pos hlow]
      by_cases hhigh : (seed >>> 16 &&& 65535) + ((seed &&& 65535) + bytes[off]!.toUInt64 - BASE) ≥ BASE
      · simp [hlow, hhigh, pure_app]
      · simp [hlow, hhigh, pure_app]
    · rw [if_neg hlow]
      by_cases hhigh : (seed >>> 16 &&& 65535) + ((seed &&& 65535) + bytes[off]!.toUInt64) ≥ BASE
      · simp [hlow, hhigh, pure_app]
      · simp [hlow, hhigh, pure_app]
  unfold C.run
  rw [hr]
  have heq : (csub ((seed &&& 65535) + bytes[off]!.toUInt64) BASE |||
        (csub ((seed >>> 16 &&& 65535) + csub ((seed &&& 65535) + bytes[off]!.toUInt64) BASE) BASE <<< 16)) =
      UInt64.ofNat (let low := (seed.toNat % 65536 + bytes[off]!.toNat) % 65521
        let total := seed.toNat / 65536 % 65536 + low
        low + 65536 * (if 65521 ≤ total then total - 65521 else total)) := by
    apply UInt64.toNat_inj.mp
    have hl : (csub ((seed &&& 65535) + bytes[off]!.toUInt64) BASE).toNat < 65536 := by
      rw [one_low]; have := Nat.mod_lt (seed.toNat % 65536 + bytes[off]!.toNat) (by decide : 0 < 65521); omega
    have hh : (csub ((seed >>> 16 &&& 65535) + csub ((seed &&& 65535) + bytes[off]!.toUInt64) BASE) BASE).toNat < 65536 := by
      rw [one_high]
      have hlow := Nat.mod_lt (seed.toNat % 65536 + bytes[off]!.toNat) (by decide : 0 < 65521)
      have hhi : seed.toNat / 65536 % 65536 < 65536 := Nat.mod_lt _ (by decide)
      dsimp only
      split <;> omega
    rw [or_shift _ _ hl hh, one_low, one_high, UInt64.toNat_ofNat']
    dsimp only
    symm
    apply Nat.mod_eq_of_lt
    have hlow := Nat.mod_lt (seed.toNat % 65536 + bytes[off]!.toNat) (by decide : 0 < 65521)
    have hhi : seed.toNat / 65536 % 65536 < 65536 := Nat.mod_lt _ (by decide)
    split <;> omega
  rw [heq]

end Zlib.Adler32.Proofs
