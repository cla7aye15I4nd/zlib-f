import ZlibF.Spec.Public.Checksums
import ZlibF.Spec.Functional.Checksums

/-! # Canonical Adler values compose across real compressor reads -/

namespace ZlibF.Math.DeflateChecksum
open ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every byte step returns reduced Adler components, including when its
initial machine word was not canonical. -/
theorem adler_step_canonical (seed : UInt32) (byte : UInt8) :
    (adlerStep seed byte).toNat % 65536 < 65521 ∧
    (adlerStep seed byte).toNat / 65536 < 65521 := by
  have low : (seed.toNat % 65536 + byte.toNat) % 65521 < 65521 := Nat.mod_lt _ (by decide)
  have high : (seed.toNat / 65536 + (seed.toNat % 65536 + byte.toNat) % 65521) % 65521 < 65521 :=
    Nat.mod_lt _ (by decide)
  let lo := (seed.toNat % 65536 + byte.toNat) % 65521
  let hi := (seed.toNat / 65536 + lo) % 65521
  have packedBound : hi * 65536 + lo < 2 ^ 32 := by dsimp only [lo, hi]; omega
  change ((UInt32.ofNat (hi * 65536 + lo)).toNat % 65536 < 65521) ∧
    (UInt32.ofNat (hi * 65536 + lo)).toNat / 65536 < 65521
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt packedBound]
  change lo < 65521 at low
  change hi < 65521 at high
  have arithmetic (a b : Nat) (ha : a < 65521) (hb : b < 65521) :
      (b * 65536 + a) % 65536 < 65521 ∧ (b * 65536 + a) / 65536 < 65521 := by omega
  exact arithmetic lo hi low high

/-- Reduced component sums persist through an arbitrary byte sequence. -/
theorem adler_update_canonical (seed : UInt32) (bytes : List UInt8)
    (canonical : seed.toNat % 65536 < 65521 ∧ seed.toNat / 65536 < 65521) :
    (adler32Update seed bytes).toNat % 65536 < 65521 ∧
    (adler32Update seed bytes).toNat / 65536 < 65521 := by
  induction bytes generalizing seed with
  | nil => exact canonical
  | cons byte rest ih =>
    exact ih (adlerStep seed byte) (adler_step_canonical seed byte)

/-- Actual default checksums already have reduced components. -/
theorem adler_checksum_canonical (bytes : List UInt8) :
    (adler32 bytes).toNat % 65536 < 65521 ∧
    (adler32 bytes).toNat / 65536 < 65521 :=
  adler_update_canonical 1 bytes (by decide)

/-- Canonicalization is the identity on a reduced format checksum. -/
theorem adler_start_canonical (seed : UInt32)
    (canonical : seed.toNat % 65536 < 65521 ∧ seed.toNat / 65536 < 65521) :
    adlerStart seed.toUInt64 = seed := by
  apply UInt32.toNat_inj.mp
  have bound := seed.toNat_lt
  simp only [adlerStart, UInt32.toNat_toUInt64, UInt32.toNat_ofNat']
  omega

/-- The public exact Adler function agrees with the independent bytewise
recurrence for canonical seeds, including its special one-byte branch. -/
theorem adler_value_canonical (seed : UInt32) (bytes : List UInt8)
    (canonical : seed.toNat % 65536 < 65521 ∧ seed.toNat / 65536 < 65521) :
    adlerValue seed.toUInt64 bytes = (adler32Update seed bytes).toUInt64 := by
  by_cases one : bytes.length = 1
  · obtain ⟨byte, rfl⟩ := List.length_eq_one_iff.mp one
    apply UInt64.toNat_inj.mp
    have low : (seed.toNat % 65536 + byte.toNat) % 65521 < 65521 := Nat.mod_lt _ (by decide)
    have high : (seed.toNat / 65536 + (seed.toNat % 65536 + byte.toNat) % 65521) % 65521 < 65521 :=
      Nat.mod_lt _ (by decide)
    simp only [adlerValue, List.length_cons, List.length_nil, Nat.zero_add,
      ite_true, List.headD_cons, UInt32.toNat_toUInt64, UInt64.toNat_ofNat',
      adler32Update, List.foldl_cons, List.foldl_nil, adlerStep, UInt32.toNat_ofNat']
    have highReduced : seed.toNat / 65536 % 65536 = seed.toNat / 65536 := by omega
    rw [highReduced]
    let lo := (seed.toNat % 65536 + byte.toNat) % 65521
    let hi := (seed.toNat / 65536 + lo) % 65521
    have once : (if 65521 ≤ seed.toNat / 65536 + lo then
        seed.toNat / 65536 + lo - 65521 else seed.toNat / 65536 + lo) = hi := by
      dsimp only [hi, lo] at *
      split <;> omega
    change (lo + 65536 * (if 65521 ≤ seed.toNat / 65536 + lo then
        seed.toNat / 65536 + lo - 65521 else seed.toNat / 65536 + lo)) % 2 ^ 64 =
      (hi * 65536 + lo) % 2 ^ 32
    rw [once]
    change lo < 65521 at low
    change hi < 65521 at high
    rw [Nat.mod_eq_of_lt (show lo + 65536 * hi < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show hi * 65536 + lo < 2 ^ 32 by omega)]
    omega
  · simp only [adlerValue, ite_eq_right one, adler_start_canonical seed canonical]

/-- Consecutive actual Adler updates on accepted input have the checksum
of the combined logical input. This has no stream or callee premise. -/
theorem adler_value_append (before incoming : List UInt8) :
    adlerValue (adler32 before).toUInt64 incoming = (adler32 (before ++ incoming)).toUInt64 := by
  rw [adler_value_canonical _ _ (adler_checksum_canonical before)]
  exact congrArg UInt32.toUInt64 (adler32Update_append 1 before incoming)

end ZlibF.Math.DeflateChecksum
