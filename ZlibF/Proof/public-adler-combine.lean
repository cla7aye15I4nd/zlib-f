import ZlibF.Proof.«adler32.c»
import ZlibF.Spec.Public.Checksums
import ZlibF.Spec.Functional.Checksums

/-! Bridging the bytewise format checksum to the component-sum proof. -/

namespace Zlib.Adler32.Proofs
open C Zlib.Adler32 Zlib.Adler32.Spec

private theorem adler_step_components (lo hi : Nat) (b : UInt8)
    (hl : lo < 65521) (hh : hi < 65521) :
    ZlibF.Spec.adlerStep (UInt32.ofNat (lo + 65536 * hi)) b =
      UInt32.ofNat ((step (lo, hi) b).1 + 65536 * (step (lo, hi) b).2) := by
  have hpack : (UInt32.ofNat (lo + 65536 * hi)).toNat = lo + 65536 * hi := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hlow : (lo + 65536 * hi) % 65536 = lo := by omega
  have hhigh : (lo + 65536 * hi) / 65536 = hi := by omega
  unfold ZlibF.Spec.adlerStep
  rw [hpack, hlow, hhigh]
  simp only [step, Zlib.Adler32.Spec.BASE]
  congr 1
  omega

/-- The format Adler recurrence agrees with the component-sum model on canonical states. -/
theorem adler_fold_components (bs : List UInt8) (lo hi : Nat)
    (hl : lo < 65521) (hh : hi < 65521) :
    ZlibF.Spec.adler32Update (UInt32.ofNat (lo + 65536 * hi)) bs =
      UInt32.ofNat ((sums lo hi bs).1 + 65536 * (sums lo hi bs).2) := by
  induction bs generalizing lo hi with
  | nil => rfl
  | cons b rest ih =>
    have hs := step_lt (lo, hi) b
    simp only [ZlibF.Spec.adler32Update, List.foldl_cons, sums, step] at *
    rw [adler_step_components lo hi b hl hh]
    exact ih _ _ hs.1 hs.2

/-- The two independent definitions of Adler-32 agree on every byte sequence. -/
theorem adler32_format_eq (bs : List UInt8) :
    ZlibF.Spec.adler32 bs = UInt32.ofNat (Zlib.Adler32.Spec.adler32 1 bs) := by
  have h := adler_fold_components bs 1 0 (by decide) (by decide)
  simpa [ZlibF.Spec.adler32, Zlib.Adler32.Spec.adler32, Zlib.Adler32.Spec.BASE] using h

private theorem format_halves (a : UInt64) (bs : List UInt8)
    (ha : a.toUInt32 = ZlibF.Spec.adler32 bs) :
    (a &&& 65535).toNat = (sums 1 0 bs).1 ∧
    (a >>> 16 &&& 65535).toNat = (sums 1 0 bs).2 := by
  have hb := sums_lt 1 0 bs (by decide) (by decide)
  change (sums 1 0 bs).1 < 65521 ∧ (sums 1 0 bs).2 < 65521 at hb
  have heq := congrArg UInt32.toNat ha
  rw [adler32_format_eq] at heq
  have hp : Zlib.Adler32.Spec.adler32 1 bs =
      (sums 1 0 bs).1 + 65536 * (sums 1 0 bs).2 := by
    simp [Zlib.Adler32.Spec.adler32, Zlib.Adler32.Spec.BASE]
  rw [hp, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), UInt64.toNat_toUInt32] at heq
  rw [low16, high16]
  omega

/-- Both Adler combine entries terminate for all values, reject negative lengths,
and combine genuine format checksums, even if the arguments carry upper bits. -/
theorem adler32_combine_public (h : Heap) (a1 a2 : UInt64) (len : Int64) :
    ∃ result, C.run (adler32_combine a1 a2 len) h = .ok (result, h) ∧
      (len.toInt < 0 → result = 0xffffffff) ∧
      (∀ xs ys : List UInt8,
        a1.toUInt32 = ZlibF.Spec.adler32 xs → a2.toUInt32 = ZlibF.Spec.adler32 ys →
        len.toInt = (ys.length : Int) → result = (ZlibF.Spec.adler32 (xs ++ ys)).toUInt64) := by
  obtain ⟨result, hr⟩ := adler32_combine_c_safe (h := h) a1 a2 len
  change C.run (adler32_combine a1 a2 len) h = .ok (result, h) at hr
  refine ⟨result, hr, ?_, ?_⟩
  · intro hn
    have hneg : len < 0 := Int64.lt_iff_toInt_lt.mpr (by simpa using hn)
    have hresult : C.run (adler32_combine a1 a2 len) h = .ok (0xffffffff, h) := by
      simp [C.run, adler32_combine, adler32_combine_, hneg]
    rw [hresult] at hr
    cases hr
    rfl
  · intro xs ys hxs hys hlen
    have hx := format_halves a1 xs hxs
    have hy := format_halves a2 ys hys
    have bx := sums_lt 1 0 xs (by decide) (by decide)
    have bys := sums_lt 1 0 ys (by decide) (by decide)
    change (sums 1 0 xs).1 < 65521 ∧ (sums 1 0 xs).2 < 65521 at bx
    change (sums 1 0 ys).1 < 65521 ∧ (sums 1 0 ys).2 < 65521 at bys
    have hpos : 0 ≤ len := Int64.le_iff_toInt_le.mpr (by simp [hlen])
    obtain ⟨out, hrun, hout⟩ := combine_value (h := h) a1 a2 len hpos
      (by simpa [hx.1] using bx.1) (by simpa [hx.2] using bx.2)
      (by simpa [hy.1] using bys.1) (by simpa [hy.2] using bys.2)
    have heq : out = result := by
      change C.run (adler32_combine a1 a2 len) h = .ok (out, h) at hrun
      rw [hr] at hrun
      cases hrun
      rfl
    subst out
    apply UInt64.toNat_inj.mp
    rw [hout, hx.1, hx.2, hy.1, hy.2, hlen, Int.toNat_natCast, adler32_format_eq,
      UInt32.toNat_toUInt64, UInt32.toNat_ofNat']
    have hab := sums_lt 1 0 (xs ++ ys) (by decide) (by decide)
    change (sums 1 0 (xs ++ ys)).1 < 65521 ∧ (sums 1 0 (xs ++ ys)).2 < 65521 at hab
    have e3 : Zlib.Adler32.Spec.adler32 1 (xs ++ ys) =
        (sums 1 0 (xs ++ ys)).1 + 65536 * (sums 1 0 (xs ++ ys)).2 := rfl
    have hb32 : (sums 1 0 (xs ++ ys)).1 + 65536 * (sums 1 0 (xs ++ ys)).2 < 2 ^ 32 := by omega
    rw [e3, Nat.mod_eq_of_lt hb32, sums_combine]
    rfl


/-- The 64-bit length entry has the same LP64 contract. -/
theorem adler32_combine64_public (h : Heap) (a1 a2 : UInt64) (len : Int64) :
    ∃ result, C.run (adler32_combine64 a1 a2 len) h = .ok (result, h) ∧
      (len.toInt < 0 → result = 0xffffffff) ∧
      (∀ xs ys : List UInt8,
        a1.toUInt32 = ZlibF.Spec.adler32 xs → a2.toUInt32 = ZlibF.Spec.adler32 ys →
        len.toInt = (ys.length : Int) → result = (ZlibF.Spec.adler32 (xs ++ ys)).toUInt64) :=
  adler32_combine_public h a1 a2 len

end Zlib.Adler32.Proofs

namespace ZlibF.Spec.Public.AdlerCombineProof

/-- `uLong adler32_combine(uLong adler1, uLong adler2, z_off_t len2)` combines checksums. -/
theorem combine_public : Goal.adler32_combine := Zlib.Adler32.Proofs.adler32_combine_public

/-- `uLong adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2)` combines checksums. -/
theorem combine64_public : Goal.adler32_combine64 := Zlib.Adler32.Proofs.adler32_combine64_public

#print axioms combine_public
#print axioms combine64_public
end ZlibF.Spec.Public.AdlerCombineProof
