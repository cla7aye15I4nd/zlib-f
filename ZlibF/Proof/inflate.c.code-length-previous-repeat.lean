import ZlibF.Proof.«inflate.c.code-length-previous-prefix»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- A normal actual symbol-16 branch derives a nonempty prefix and a
permitted count, reads the preceding cell and the exact two extra bits,
and appends that value exactly 3+extra times. Waiting and BAD cannot be
mistaken for this normal result. -/
theorem clPreviousRepeat_contents_of_run {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (actual : runX (clRepeat16 c here) l h = .ok ((.ok false, regs), after)) :
    ∃ used state value, used ≤ bs.length ∧ after = setI h zs state ∧
      BitInv after regs (bs.drop used) ∧ 1 ≤ s.«have».toNat ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + (3 + value) ∧
      state.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat ∧
      readBits 2 ((stream l bs).drop here.bits.toNat) = some (value, stream regs (bs.drop used)) ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate (3 + value) ((actualLengthPrefix s).getLastD 0) := by
  obtain ⟨result, dropped, _oldUsed, prefixRun, _oldBound, _oldInv, _shape, _bits, _enough, _cursor, _budget⟩ :=
    clNeedDrop_run_cursor B here 2 width (by decide)
  cases result with
  | error exit =>
    have stopped : runX (clRepeat16 c here) l h = .ok ((.error exit, dropped), h) := by
      unfold clRepeat16
      rw [runX_bind, prefixRun]
    rw [stopped] at actual
    cases actual
  | ok done =>
    cases done
    obtain ⟨used, bound, inv, source, enough⟩ := clNeedDrop_stream_of_run B here 2 width (by decide) prefixRun
    by_cases empty : s.«have» = 0
    · obtain ⟨index, _literal, bad⟩ := tcBadMode_run (c := c) "invalid bit length repeat"
        lit_bit_length_repeat hr hc hz hs
      have rejected : runX (clRepeat16 c here) l h = .ok ((.ok true, dropped), tcBadHeap h r zs z s index) := by
        unfold clRepeat16
        rw [runX_bind, prefixRun, hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, empty, bad, runX_pure]
      rw [rejected] at actual
      cases actual
    · have nonempty : 1 ≤ s.«have».toNat := by
        have notZero : s.«have».toNat ≠ 0 := by intro zero; exact empty (UInt32.toNat_inj.mp zero)
        omega
      obtain ⟨prepared, value, previousRun, preparedInv, previous, read, count⟩ :=
        clPrevBits_read hc hs size nonempty (by omega) inv enough
      have cut : runX (clRepeat16 c here) l h = runX (do clPrevBits c s.«have»; clRepeatFinish c) dropped h := by
        unfold clRepeat16
        rw [runX_bind, prefixRun, hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, empty]
      rw [cut, runX_bind, previousRun] at actual
      change runX (clRepeatFinish c) prepared h = .ok ((.ok false, regs), after) at actual
      have low := readBits_held_stream dropped (bs.drop used) 2 enough
      have sameValue : value = dropped.hold.toNat % 4 :=
        congrArg Prod.fst (Option.some.inj (read.symm.trans low))
      have valueBound : value < 4 := by rw [sameValue]; exact Nat.mod_lt _ (by decide)
      have copyBound : prepared.copy.toNat ≤ 138 := by omega
      obtain ⟨state, heapEq, regsEq, frame, stateSize, stateCount, room, contents⟩ :=
        clRepeatFinish_contents_of_run hr hc hz hs size nlen ndist haveBound copyBound actual
      have outputInv : BitInv after regs (bs.drop used) := by
        rw [heapEq, regsEq]
        exact (show BitInv h { prepared with copy := 0xffffffff } (bs.drop used) from
          ⟨preparedInv.have_eq, preparedInv.next, preparedInv.hold_lt⟩).setI zs state
      have sameStream : stream regs (bs.drop used) = stream prepared (bs.drop used) := by rw [regsEq]; rfl
      rw [source, ← sameStream] at read
      have castValue : prepared.len.toUInt16.toNat = (actualLengthPrefix s).getLastD 0 := by
        rw [UInt32.toNat_toUInt16, previous, actualLengthPrefix_last nonempty,
          Nat.mod_eq_of_lt (UInt16.toNat_lt _)]
      have newCount : state.«have».toNat = s.«have».toNat + (3 + value) := by rw [stateCount, count]
      have newPrefix : actualLengthPrefix state = actualLengthPrefix s ++
          List.replicate (3 + value) ((actualLengthPrefix s).getLastD 0) := by rw [contents, count, castValue]
      exact ⟨used, state, value, bound, heapEq, outputInv, nonempty, frame, stateSize, newCount,
        by omega, read, newPrefix⟩

#print axioms clPreviousRepeat_contents_of_run
end Zlib.Inflate.Proofs
