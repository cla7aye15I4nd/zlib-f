import ZlibF.Proof.«inflate.c.code-length-repeat-finish»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- A real normal repeat result derives its permitted range from the actual
check. An overrun executes BAD and returns true, so cannot satisfy this
normal-result observation. No successful-range hypothesis is assumed. -/
theorem clRepeatFinish_contents_of_run {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat) (copyBound : l.copy.toNat ≤ 138)
    (actual : runX (clRepeatFinish c) l h = .ok ((.ok false, regs), after)) :
    ∃ state, after = setI h zs state ∧ regs = { l with copy := 0xffffffff } ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + l.copy.toNat ∧
      s.«have».toNat + l.copy.toNat ≤ s.nlen.toNat + s.ndist.toNat ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate l.copy.toNat l.len.toUInt16.toNat := by
  by_cases room : s.«have».toNat + l.copy.toNat ≤ s.nlen.toNat + s.ndist.toNat
  · obtain ⟨state, run, frame, stateSize, count, contents⟩ :=
      clRepeatFinish_contents (l := l) hc hs size nlen ndist haveBound copyBound room
    rw [run] at actual
    cases actual
    exact ⟨state, rfl, rfl, frame, stateSize, count, room, contents⟩
  · have sum : (s.nlen + s.ndist).toNat = s.nlen.toNat + s.ndist.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have added : (s.«have» + l.copy).toNat = s.«have».toNat + l.copy.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have test : s.«have» + l.copy > s.nlen + s.ndist := by
      change s.nlen + s.ndist < s.«have» + l.copy
      rw [UInt32.lt_iff_toNat_lt, sum, added]
      omega
    obtain ⟨index, _literal, bad⟩ := tcBadMode_run (c := c) "invalid bit length repeat"
      lit_bit_length_repeat hr hc hz hs
    have rejected : runX (clRepeatFinish c) l h =
        .ok ((.ok true, l), tcBadHeap h r zs z s index) := by
      unfold clRepeatFinish
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, hs, runX_get, test, bad, runX_pure]
    rw [rejected] at actual
    cases actual

#print axioms clRepeatFinish_contents_of_run
end Zlib.Inflate.Proofs
