import ZlibF.Spec.Public.Checksums

namespace Zlib.Uncompr.Proof.StoredWire
open C ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real Adler update from the zlib initial seed agrees with the
independent RFC checksum, including the one-byte fast path. -/
theorem initial_adler (payload : List UInt8) : adlerValue 1 payload = (adler32 payload).toUInt64 := by
  by_cases one : payload.length = 1
  · cases payload with
    | nil => simp at one
    | cons byte tail =>
      have tailEmpty : tail = [] := by simpa using one
      subst tail
      have small := byte.toNat_lt
      have low : (1 + byte.toNat) % 65521 = 1 + byte.toNat := Nat.mod_eq_of_lt (by omega)
      have low2 : (1 + byte.toNat) % 65536 = 1 + byte.toNat := Nat.mod_eq_of_lt (by omega)
      have bound : 1 + byte.toNat + 65536 * (1 + byte.toNat) < 2^32 := by omega
      apply UInt64.toNat_inj.mp
      simp [adlerValue,adler32,adler32Update,adlerStep,List.foldl,low,low2,
        UInt32.toNat_ofNat',UInt64.toNat_ofNat',Nat.mod_eq_of_lt bound,show ¬ 65521 ≤ 1 + byte.toNat by omega]
      rw [Nat.mod_eq_of_lt (show 1 + byte.toNat + 65536 * (1 + byte.toNat) < 18446744073709551616 by omega),
        Nat.mod_eq_of_lt (show (1 + byte.toNat) * 65536 + (1 + byte.toNat) < 4294967296 by omega)]
      omega
  · simp [adlerValue,one,adlerStart,adler32]

#print axioms initial_adler
end Zlib.Uncompr.Proof.StoredWire
