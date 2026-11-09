import ZlibF.Proof.«inflate.c.code-length-wait-prefix»
import ZlibF.Proof.«inflate.c.codelens-loop»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

private theorem repeatFinish_boolean {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (copyLo : 1 ≤ l.copy.toNat) (copyHi : l.copy.toNat ≤ 138) (value : l.len.toNat ≤ 15)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15) :
    ∃ decision regs after, runX (clRepeatFinish c) l h = .ok ((.ok decision, regs), after) := by
  have outcomes := clRepeatFinish_run hr hc hz hs size nlen ndist haveBound copyLo copyHi value initialized
  by_cases overrun : s.«have».toNat + l.copy.toNat > s.nlen.toNat + s.ndist.toNat
  · obtain ⟨index, _literal, run⟩ := outcomes.1 overrun
    exact ⟨true, l, _, run⟩
  · obtain ⟨state, run, _rest⟩ := outcomes.2 (by omega)
    exact ⟨false, _, _, run⟩

private theorem zeroRepeat_wait_stream {c : Ctx} {l regs : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {exit : Ex}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7) (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11)
    (actual : runX (do clZeroSetup here extra base; clRepeatFinish c) l h = .ok ((.error exit, regs), h)) :
    ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs := by
  obtain ⟨result, prepared, _used, setupRun, _bound, _inv, _shape, _bits, counts, _cursor, _budget⟩ :=
    clZeroSetup_run_cursor B here extra base width extraBound baseLo baseHi
  rw [runX_bind, setupRun] at actual
  cases result with
  | error fault =>
    cases actual
    exact clZeroSetup_wait_stream B here extra base width extraBound setupRun
  | ok done =>
    cases done
    obtain ⟨zero, copyLo, copyHi⟩ := counts rfl
    obtain ⟨decision, final, after, finished⟩ := repeatFinish_boolean hr hc hz hs size nlen ndist haveBound
      (by omega) copyHi (by rw [zero]; decide) initialized
    change runX (clRepeatFinish c) prepared h = .ok ((.error exit, regs), h) at actual
    rw [finished] at actual
    cases actual

/-- An actual wait after lookup has consumed no code or extra bits. The
whole real bit stream is retained, even if refill advanced the byte cursor. -/
theorem clAfterLookup_wait_stream {c : Ctx} {l regs : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {exit : Ex}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7) (enough : here.bits.toNat ≤ l.bits.toNat)
    (actual : runX (clAfterLookup c here) l h = .ok ((.error exit, regs), h)) :
    ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs := by
  by_cases literal : here.val < 16
  · obtain ⟨run, _inv, _stream, _count, _values⟩ := clAfterLookup_literal_run hc hs size
      (by omega) (UInt16.lt_iff_toNat_lt.mp literal) width enough B initialized
    rw [run] at actual
    cases actual
  · by_cases previous : here.val = 16
    · rw [clAfterLookup_repeat16 c here previous] at actual
      obtain ⟨result, dropped, _used, prefixRun, _bound, inv, _shape, _bits, enoughExtra, _cursor, _budget⟩ :=
        clNeedDrop_run_cursor B here 2 width (by decide)
      cases result with
      | error fault =>
        have stopped : runX (clRepeat16 c here) l h = .ok ((.error fault, dropped), h) := by
          unfold clRepeat16
          rw [runX_bind, prefixRun]
        rw [stopped] at actual
        cases actual
        exact clNeedDrop_wait_stream B here 2 width (by decide) prefixRun
      | ok done =>
        cases done
        by_cases empty : s.«have» = 0
        · obtain ⟨index, _literal, bad⟩ := tcBadMode_run (c := c) "invalid bit length repeat" lit_bit_length_repeat hr hc hz hs
          have rejected : runX (clRepeat16 c here) l h = .ok ((.ok true, dropped), tcBadHeap h r zs z s index) := by
            unfold clRepeat16
            rw [runX_bind, prefixRun, hc]
            simp [runX_bind, runX_lift, ldI_eq, hs, empty, bad, runX_pure]
          rw [rejected] at actual
          cases actual
        · have nonempty : 1 ≤ s.«have».toNat := by
            have notZero : s.«have».toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
            omega
          obtain ⟨prepared, previousRun, _inv, _stream, _shape, _bits, value, copyLo, copyHi⟩ :=
            clPrevBits_run hc hs size nonempty (by omega) initialized inv (enoughExtra rfl)
          have cut : runX (clRepeat16 c here) l h = runX (clRepeatFinish c) prepared h := by
            unfold clRepeat16
            rw [runX_bind, prefixRun, hc]
            simp [runX_bind, runX_lift, ldI_eq, hs, empty, previousRun]
          obtain ⟨decision, final, after, finished⟩ := repeatFinish_boolean hr hc hz hs size nlen ndist
            (by omega) (by omega) (by omega) value initialized
          rw [cut, finished] at actual
          cases actual
    · by_cases zero17 : here.val = 17
      · rw [clAfterLookup_zero17 c here zero17] at actual
        exact zeroRepeat_wait_stream hr hc hz hs size nlen ndist (by omega) initialized B here 3 3
          width (by decide) (by decide) (by decide) actual
      · rw [clAfterLookup_zero18 c here literal previous zero17] at actual
        exact zeroRepeat_wait_stream hr hc hz hs size nlen ndist (by omega) initialized B here 7 11
          width (by decide) (by decide) (by decide) actual

#print axioms clAfterLookup_wait_stream
end Zlib.Inflate.Proofs
