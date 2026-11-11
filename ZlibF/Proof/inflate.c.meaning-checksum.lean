import ZlibF.Proof.«adler32.c.public-block»
import ZlibF.Spec.Format.Checksum

/-!
# inflate.c: the running check value continues over more output

Heap-free. `UPDATE_CHECK(check, buf, len)` continues the running checksum of
the output with the next bytes. When `check` is the Adler-32 (or CRC-32) of
the output so far, the zlib update over the new bytes gives the checksum of
the whole output (`adler_continue`, `crc_continue`).
-/

namespace Zlib.Inflate.Proofs.MeaningChecksum
open ZlibF.Spec
set_option autoImplicit false

theorem canonical_value {s1 s2 : Nat} (h1 : s1 < 65521) (h2 : s2 < 65521) :
    (UInt32.ofNat (s2 * 65536 + s1)).toNat % 65536 < 65521 ∧
      (UInt32.ofNat (s2 * 65536 + s1)).toNat / 65536 < 65521 := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show s2 * 65536 + s1 < 2 ^ 32 by omega)]
  omega

/-- Adler-32 values have both halves below 65521. -/
theorem adler32Update_canonical (a : UInt32) (canonical : a.toNat % 65536 < 65521 ∧ a.toNat / 65536 < 65521) :
    ∀ bs : List UInt8, (adler32Update a bs).toNat % 65536 < 65521 ∧
      (adler32Update a bs).toNat / 65536 < 65521 := by
  intro bs
  induction bs generalizing a with
  | nil => simpa [adler32Update] using canonical
  | cons b rest ih =>
    apply ih
    exact canonical_value (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

theorem adler32_canonical (bs : List UInt8) :
    (adler32 bs).toNat % 65536 < 65521 ∧ (adler32 bs).toNat / 65536 < 65521 :=
  adler32Update_canonical 1 (by decide) bs

/-- A canonical Adler-32 value is its own canonical start. -/
theorem canonicalStart_adler32 (bs : List UInt8) :
    Zlib.Adler32.Proofs.canonicalStart (adler32 bs).toUInt64 = adler32 bs := by
  have canonical := adler32_canonical bs
  apply UInt32.toNat_inj.mp
  simp only [Zlib.Adler32.Proofs.canonicalStart, UInt32.toNat_toUInt64, UInt32.toNat_ofNat']
  have lt := (adler32 bs).toNat_lt
  omega

/-- zlib's Adler-32 update continues the Adler-32 of the output so far. -/
theorem adler_continue (xs ys : List UInt8) :
    Zlib.Adler32.Spec.adler32 (adler32 xs).toUInt64.toNat ys = (adler32 (xs ++ ys)).toNat := by
  have seed := Zlib.Adler32.Proofs.adler_format_seed (adler32 xs).toUInt64 ys
  rw [canonicalStart_adler32, adler32, adler32Update_append] at seed
  have value := congrArg UInt32.toNat seed
  rw [UInt32.toNat_ofNat'] at value
  have small : Zlib.Adler32.Spec.adler32 (adler32 xs).toUInt64.toNat ys < 2 ^ 32 := by
    have := Zlib.Adler32.Spec.sums_lt ((adler32 xs).toUInt64.toNat % 65536 % 65521)
      ((adler32 xs).toUInt64.toNat / 65536 % 65536 % 65521) ys (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide))
    simp only [Zlib.Adler32.Spec.adler32, Zlib.Adler32.Spec.BASE] at this ⊢
    change (Zlib.Adler32.Spec.sums _ _ _).1 < 65521 ∧ (Zlib.Adler32.Spec.sums _ _ _).2 < 65521 at this
    omega
  rw [Nat.mod_eq_of_lt (by simpa [adler32] using small)] at value
  simpa [adler32] using value.symm

/-- zlib's CRC-32 update continues the CRC-32 of the output so far. -/
theorem crc_continue (xs ys : List UInt8) :
    crc32Update (crc32 xs) ys = crc32 (xs ++ ys) := by
  rw [crc32, crc32Update_append]
  rfl

#print axioms adler_continue
#print axioms crc_continue

end Zlib.Inflate.Proofs.MeaningChecksum
