import ZlibF.Proof.«inflate.c.code-length-repeat-contents»
import ZlibF.Proof.«inflate.c.code-length-repeat-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The real successful repeat-overrun check enters the real write loop and
appends precisely the selected repetition count. The nonwrapping comparison
is derived from the existing mode bounds and bounded repeat count. This is
the permitted branch; the original error-branch theorem remains unchanged. -/
theorem clRepeatFinish_contents {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat) (_copyBound : l.copy.toNat ≤ 138)
    (room : s.«have».toNat + l.copy.toNat ≤ s.nlen.toNat + s.ndist.toNat) :
    ∃ state,
      runX (clRepeatFinish c) l h = .ok ((.ok false, { l with copy := 0xffffffff }), setI h zs state) ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + l.copy.toNat ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate l.copy.toNat l.len.toUInt16.toNat := by
  have sum : (s.nlen + s.ndist).toNat = s.nlen.toNat + s.ndist.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have added : (s.«have» + l.copy).toNat = s.«have».toNat + l.copy.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have test : ¬ s.«have» + l.copy > s.nlen + s.ndist := by
    change ¬ s.nlen + s.ndist < s.«have» + l.copy
    rw [UInt32.lt_iff_toNat_lt, sum, added]
    omega
  obtain ⟨state, run, frame, stateSize, count, contents⟩ :=
    clRepeat_run_contents (l := l) hc hs size (by omega)
  refine ⟨state, ?_, frame, stateSize, count, contents⟩
  unfold clRepeatFinish
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, runX_get, test, run, runX_pure]

#print axioms clRepeatFinish_contents
end Zlib.Inflate.Proofs
