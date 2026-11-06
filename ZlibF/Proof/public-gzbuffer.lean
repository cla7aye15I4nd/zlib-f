import ZlibF.Spec.Public.GzControl
import ZlibF.Proof.«gzlib.c.base»

namespace ZlibF.Spec.Public.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs

/-- `int gzbuffer(gzFile file, unsigned size)` checks the mode, existing
allocation and overflow before changing the requested size. -/
theorem gzbuffer_record {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s)
    (size : UInt32) :
    C.run (gzbuffer (hnd i) size) h =
      if (s.mode ≠ GZ_READ ∧ s.mode ≠ GZ_WRITE) ∨ s.size ≠ 0 ∨ 2 ^ 31 ≤ size.toNat then
        .ok (-1, h)
      else .ok (0, setS h i { s with want := UInt32.ofNat (max size.toNat 8) }) := by
  have heq : (if size < 8 then 8 else size) = UInt32.ofNat (max size.toNat 8) := by
    by_cases hs8 : size < 8
    · have hn : size.toNat < 8 := by simpa using (UInt32.lt_iff_toNat_lt.mp hs8)
      simp [hs8, Nat.max_eq_right (by omega : size.toNat ≤ 8)]
    · have hn : 8 ≤ size.toNat := by
        have hp : ¬ size.toNat < 8 := fun hp => hs8 (UInt32.lt_iff_toNat_lt.mpr (by simpa using hp))
        omega
      simp [hs8, Nat.max_eq_left hn]
  have hd : (size <<< 1) < size ↔ 2 ^ 31 ≤ size.toNat := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_shiftLeft]
    have := size.toNat_lt
    simp only [UInt32.toNat_ofNat, Nat.reducePow] at *
    rcases Nat.lt_or_ge size.toNat (2 ^ 31) with h1 | h1
    · have : (1 : UInt32).toNat % 32 = 1 := rfl
      simp [this]; omega
    · have : (1 : UInt32).toNat % 32 = 1 := rfl
      simp [this]; omega
  unfold C.run gzbuffer
  by_cases hm : s.mode ≠ GZ_READ ∧ s.mode ≠ GZ_WRITE
  · gsimp [hs, hm.1, hm.2]
  · have hm' : s.mode = GZ_READ ∨ s.mode = GZ_WRITE := by
      by_cases hr : s.mode = GZ_READ
      · exact Or.inl hr
      · exact Or.inr (Classical.byContradiction (fun hw => hm ⟨hr, hw⟩))
    by_cases hsize : s.size ≠ 0
    · rcases hm' with hm1 | hm1 <;> gsimp [hs, hm1, hsize, GZ_READ, GZ_WRITE]
    · by_cases hov : (size <<< 1) < size
      · have hn := hd.mp hov
        rcases hm' with hm1 | hm1 <;> gsimp [hs, hm1, hsize, hov, hn, GZ_READ, GZ_WRITE]
      · have hn : ¬ 2 ^ 31 ≤ size.toNat := fun x => hov (hd.mpr x)
        have hz : s.size = 0 := by simpa using hsize
        rcases hm' with hm1 | hm1 <;> gsimp [hs, hm1, hz, hov, hn, heq, GZ_READ, GZ_WRITE]

/-- `int gzbuffer(gzFile file, unsigned size)` satisfies the public goal. -/
theorem gzbuffer_public : Goal.gzbuffer := by
  constructor
  · intro h size
    rfl
  · intro h i s size hs
    simpa [hnd, setS, putGz] using gzbuffer_record hs size

#print axioms gzbuffer_record
#print axioms gzbuffer_public

end ZlibF.Spec.Public.Proofs
