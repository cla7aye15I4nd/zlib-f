import ZlibF.Zlib.«inflate.c»

/-!
# infback.c: facts that do not mention the heap

Migrated from the earlier attempt (`TableCL`, `StoredSpec`) and restated against the present translation: the table `order`
of the code-length code lengths is a permutation of `0 .. 18`, and the check of a stored block header on a 32-bit `hold`.
-/

namespace Zlib.Infback.Proofs
open C Zlib.Inflate

/-- `order` has 19 entries, every one below 19. -/
theorem order_lt : ∀ j, j < 19 → ∃ v, order[j]? = some v ∧ v.toNat < 19 := by decide

/-- `order` is injective on `0 .. 18`. -/
theorem order_inj : ∀ i, i < 19 → ∀ j, j < 19 → order[i]? = order[j]? → i = j := by decide

/-- `order` hits every code length symbol `0 .. 18`: the loops of `case TABLE` that write `lens[order[have++]]` for
`have = 0 .. 18` write every one of `lens[0 .. 18]` exactly once. -/
theorem order_surj : ∀ k, k < 19 → ∃ j, j < 19 ∧ order[j]? = some k.toUInt16 := by decide

/-- For `x < 2^16`, `x ^^^ 0xffff` is `0xffff - x`. -/
theorem xor_ffff_blocks : ∀ a, a < 256 → ∀ b, b < 256 → (a * 256 + b) ^^^ 65535 = 65535 - (a * 256 + b) := by
  decide +kernel

theorem xor_ffff (x : Nat) (hx : x < 65536) : x ^^^ 65535 = 65535 - x := by
  have := xor_ffff_blocks (x / 256) (by omega) (x % 256) (Nat.mod_lt _ (by decide))
  have e : x / 256 * 256 + x % 256 = x := by omega
  rwa [e] at this

/-- **The stored block header check** (`if (hold & 0xffff) != ((hold >> 16) ^ 0xffff)`) on a bit buffer of at most 32 bits:
it passes exactly when the length field and the field after it add up to `0xffff` (RFC 1951, 3.2.4: `NLEN` is the one's
complement of `LEN`). -/
theorem stored_check (hold : UInt64) (hh : hold.toNat < 2 ^ 32) :
    ((hold &&& (0xffff : UInt64)) != ((hold >>> 16) ^^^ (0xffff : UInt64))) = false ↔ hold.toNat % 65536 + hold.toNat / 65536 = 65535 := by
  have e1 : (hold &&& (0xffff : UInt64)).toNat = hold.toNat % 65536 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod hold.toNat 16
  have e2 : (hold >>> 16).toNat = hold.toNat / 65536 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have e3 : ((hold >>> 16) ^^^ (0xffff : UInt64)).toNat = hold.toNat / 65536 ^^^ 65535 := by
    rw [UInt64.toNat_xor, e2]; rfl
  have hlt : hold.toNat / 65536 < 65536 := by omega
  have hx := xor_ffff _ hlt
  have hlo : hold.toNat % 65536 < 65536 := Nat.mod_lt _ (by decide)
  simp only [bne_eq_false_iff_eq]
  constructor
  · intro e
    have := congrArg UInt64.toNat e
    rw [e1, e3, hx] at this
    omega
  · intro e
    apply UInt64.toNat_inj.mp
    rw [e1, e3, hx]
    omega

/-- The length field of a stored block: the low 16 bits. -/
theorem stored_len_toNat (hold : UInt64) : (hold.toUInt32 &&& 0xffff).toNat = hold.toNat % 65536 := by
  rw [UInt32.toNat_and]
  simp only [UInt64.toNat_toUInt32]
  have : (0xffff : UInt32).toNat = 2 ^ 16 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 16 ∣ 2 ^ 32)]

end Zlib.Infback.Proofs
