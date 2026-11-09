import ZlibF.Math.«inflate-header-alphabet»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- When the first LENLENS entry has enough bits, its actual two loops
produce precisely the independent readCodeLenLens alphabet at the real
constructor continuation. This is an internal full-prefix branch. -/
theorem inflate_LENLENS_alphabet_prefix {c : Ctx} {l : IL} {h : Heap}
    {zs : Nat} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (start : s.«have» = 0) (bound : s.ncode.toNat ≤ 19)
    (B : BitInv h l bs) (enough : 3 * s.ncode.toNat ≤ (stream l bs).length) :
    ∃ regs used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      readCodeLenLens s.ncode.toNat (stream l bs) = some
        (Zlib.Inftrees.Proofs.lensOf (fun k => ((llDone s (stream l bs)).lens.getD k 0).toNat) 19,
         stream regs (bs.drop used)) ∧
      runX (inflate_LENLENS c) l h = runX (llTail c) regs (setI h zs (llDone s (stream l bs))) ∧
      (llDone s (stream l bs)).WellFormed ∧ Good3 (llDone s (stream l bs)).lens 19 := by
  have haveBound : s.«have».toNat ≤ s.ncode.toNat := by rw [start]; simp
  have full : min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) = s.ncode.toNat := by
    simp only [start, UInt32.toNat_zero, Nat.sub_zero]
    apply Nat.min_eq_left
    omega
  obtain ⟨outcome, regs, used, readRun, usedBound, inv, remaining, _shape, _wait, complete⟩ :=
    ll1_run hc hs wf.1 bound haveBound B
  have normal : outcome = .ok () := complete (by rw [full, start]; simp)
  rw [full] at readRun remaining
  have currentGet : (setI h zs (llSt s (stream l bs) s.ncode.toNat)).istates zs =
      some (llSt s (stream l bs) s.ncode.toNat) := by simp
  have currentCount := llSt_have s (stream l bs) s.ncode.toNat (by rw [start]; simp; exact bound)
  have currentSize : (llSt s (stream l bs) s.ncode.toNat).lens.size = 320 := by simp [llSt, lensRead_size, wf.1]
  have zeroRun := lz_run (c := c) (l := regs) hc currentGet currentSize (by rw [start] at currentCount; simp at currentCount; omega)
  have done : lzSt (llSt s (stream l bs) s.ncode.toNat)
      (19 - (llSt s (stream l bs) s.ncode.toNat).«have».toNat) = llDone s (stream l bs) := by
    unfold llDone
    simp only [start, UInt32.toNat_zero, Nat.sub_zero]
  have continuation : runX (inflate_LENLENS c) l h =
      runX (llTail c) regs (setI h zs (llDone s (stream l bs))) := by
    rw [inflate_LENLENS_eq, runX_bind, readRun, normal]
    simp only
    rw [runX_bind, zeroRun, done]
    simp only [setI_setI]
  have alphabet := llDone_code_length_alphabet wf.1 start bound (stream l bs) enough
  rw [← remaining] at alphabet
  have filled : Good3 (llDone s (stream l bs)).lens 19 := by
    rw [llDone_lens s (stream l bs) bound haveBound]
    have initial : Good3 s.lens s.«have».toNat := by rw [start]; intro i inside; simp at inside
    have read := lensRead_good (stream l bs) initial (s.ncode.toNat - s.«have».toNat) (by omega)
    rw [show s.«have».toNat + (s.ncode.toNat - s.«have».toNat) = s.ncode.toNat by omega] at read
    have zeros := lensZero_good read (19 - s.ncode.toNat) (by omega)
    simpa only [show s.ncode.toNat + (19 - s.ncode.toNat) = 19 by omega] using zeros
  refine ⟨regs, used, usedBound, inv, alphabet, continuation, ?_, filled⟩
  refine ⟨?_, wf.2.1, wf.2.2⟩
  rw [llDone_lens s (stream l bs) bound haveBound, lensZero_size, lensRead_size]
  exact wf.1

#print axioms inflate_LENLENS_alphabet_prefix
end Zlib.Inflate.Proofs
