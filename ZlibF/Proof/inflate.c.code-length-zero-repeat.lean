import ZlibF.Proof.«inflate.c.code-length-repeat-outcome»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- A real completed zero-repeat branch appends exactly the count read
from its extra bits. Normal completion derives the range check, rather
than taking it or a callee contract as a precondition. -/
theorem clZeroRepeat_contents_of_run {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11)
    (actual : runX (do clZeroSetup here extra base; clRepeatFinish c) l h = .ok ((.ok false, regs), after)) :
    ∃ used state value, used ≤ bs.length ∧ after = setI h zs state ∧
      BitInv after regs (bs.drop used) ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + (base.toNat + value) ∧
      state.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat ∧
      readBits extra.toNat ((stream l bs).drop here.bits.toNat) = some (value, stream regs (bs.drop used)) ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate (base.toNat + value) 0 := by
  obtain ⟨result, prepared, used, setupRun, usedBound, preparedInv, _shape, _bitBound, counts, _cursor, _budget⟩ :=
    clZeroSetup_run_cursor B here extra base width extraBound baseLo baseHi
  obtain ⟨result2, prepared2, used2, setupRun2, usedBound2, preparedInv2, semantic⟩ :=
    clZeroSetup_read B here extra base width extraBound baseLo baseHi
  rw [setupRun] at setupRun2
  cases setupRun2
  have uses : used2 = used := by
    have a := preparedInv.have_eq
    have b := preparedInv2.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used2
  rw [runX_bind, setupRun] at actual
  cases result with
  | error exit => cases actual
  | ok done =>
    cases done
    obtain ⟨zero, _copyLo, copyHi⟩ := counts rfl
    obtain ⟨value, read, _zero2, count⟩ := semantic rfl
    obtain ⟨state, heapEq, regsEq, frame, stateSize, stateCount, room, contents⟩ :=
      clRepeatFinish_contents_of_run hr hc hz hs size nlen ndist haveBound copyHi actual
    have inv : BitInv after regs (bs.drop used) := by
      rw [heapEq, regsEq]
      exact (show BitInv h { prepared with copy := 0xffffffff } (bs.drop used) from
        ⟨preparedInv.have_eq, preparedInv.next, preparedInv.hold_lt⟩).setI zs state
    have sameStream : stream regs (bs.drop used) = stream prepared (bs.drop used) := by
      rw [regsEq]
      rfl
    rw [← sameStream] at read
    have newCount : state.«have».toNat = s.«have».toNat + (base.toNat + value) := by
      rw [stateCount, count]
    have stored : actualLengthPrefix state = actualLengthPrefix s ++ List.replicate (base.toNat + value) 0 := by
      rw [contents, count, zero]
      rfl
    exact ⟨used, state, value, usedBound, heapEq, inv, frame, stateSize, newCount, by omega, read, stored⟩

#print axioms clZeroRepeat_contents_of_run
end Zlib.Inflate.Proofs
