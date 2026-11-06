import ZlibF.Spec.Api.Concrete

namespace ZlibF.Spec.Api.Proofs

/-- The concrete boundary exposes every fault of the translated computation.
This equivalence requires no hypothesis that the computation succeeds. -/
theorem execute_fault_iff {α : Type} (program : C.M α) (h : C.Heap) :
    Concrete.execute program h = .fault ↔ ∃ fault, C.run program h = .error fault := by
  cases hr : C.run program h with
  | error fault => simp [Concrete.execute, hr]
  | ok result => simp [Concrete.execute, hr]

/-- The actual translated `compressBound_z` equals the saturated natural-number
formula for every 64-bit input. The proof checks that the sum can wrap only once
and that its increment is less than the modulus, so the C overflow test is exact. -/
theorem compressBound_z_value (s : UInt64) :
    (Zlib.Compress.compressBound_z s).toNat = compressBound s.toNat := by
  have h12 : (s >>> 12).toNat = s.toNat / 4096 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  have h14 : (s >>> 14).toNat = s.toNat / 16384 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  have h25 : (s >>> 25).toNat = s.toNat / 33554432 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  have hs := s.toNat_lt
  have hsum : (s + (s >>> 12) + (s >>> 14) + (s >>> 25) + 13).toNat =
      (s.toNat + s.toNat / 4096 + s.toNat / 16384 + s.toNat / 33554432 + 13) % 2 ^ 64 := by
    simp only [UInt64.toNat_add, h12, h14, h25]
    rw [show (13 : UInt64).toNat = 13 from rfl]
    simp only [Nat.mod_add_mod]
  have hinc : s.toNat / 4096 + s.toNat / 16384 + s.toNat / 33554432 + 13 < 2 ^ 64 := by
    omega
  have hB2 : s.toNat + s.toNat / 4096 + s.toNat / 16384 + s.toNat / 33554432 + 13 <
      2 ^ 64 + 2 ^ 64 := by omega
  unfold Zlib.Compress.compressBound_z compressBound
  by_cases hB : s.toNat + s.toNat / 4096 + s.toNat / 16384 + s.toNat / 33554432 + 13 < 2 ^ 64
  · have hm : (s.toNat + s.toNat / 4096 + s.toNat / 16384 + s.toNat / 33554432 + 13) % 2 ^ 64 =
        s.toNat + s.toNat / 4096 + s.toNat / 16384 + s.toNat / 33554432 + 13 := Nat.mod_eq_of_lt hB
    have hnlt : ¬ s + (s >>> 12) + (s >>> 14) + (s >>> 25) + 13 < s := by
      rw [UInt64.lt_iff_toNat_lt, hsum, hm]
      omega
    rw [ite_eq_right hnlt, hsum, hm, ite_eq_right (by omega)]
  · have hm : (s.toNat + s.toNat / 4096 + s.toNat / 16384 + s.toNat / 33554432 + 13) % 2 ^ 64 =
        s.toNat + s.toNat / 4096 + s.toNat / 16384 + s.toNat / 33554432 + 13 - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hlt : s + (s >>> 12) + (s >>> 14) + (s >>> 25) + 13 < s := by
      rw [UInt64.lt_iff_toNat_lt, hsum, hm]
      omega
    rw [ite_eq_left hlt, ite_eq_left (by omega)]
    rfl

/-- Both actual translated bound functions satisfy the concrete API goal on LP64.
Unlike `compress_bound_adequate`, this theorem concerns the implementation's
numeric result rather than an implication already required by `Compress2`. -/
theorem compress_bound_value : Goal.compress_bound_value := by
  intro sourceLen
  exact ⟨compressBound_z_value sourceLen, compressBound_z_value sourceLen⟩

end ZlibF.Spec.Api.Proofs
