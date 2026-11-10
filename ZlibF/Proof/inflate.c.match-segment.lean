import ZlibF.Proof.«inflate.c.match-source»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual source selection derives a positive in-bounds segment. The
history premise is the successful side of MATCH's own refusal check. -/
theorem matchSelect_segment {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (window : WinInv h s) {l : IL} {dest : BRef}
    {output : Array UInt8} {outOffset : Nat}
    (put : l.put = .ref dest outOffset) (outGet : Space.get h dest = some output)
    (left : 0 < l.left.toNat) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (history : s.offset > l.out_ - l.left → ¬ s.offset - (l.out_ - l.left) > s.whave) :
    ∃ copy source sourceOffset saved,
      0 < copy.toNat ∧ copy.toNat ≤ l.left.toNat ∧ copy.toNat ≤ s.length.toNat ∧
      outOffset + copy.toNat ≤ output.size ∧
      Space.get h source = some (if source = dest then output else saved) ∧
      sourceOffset + copy.toNat ≤ (if source = dest then output else saved).size ∧
      runX (matchSelect c) l h = runX (matchEmit c copy (.ref source sourceOffset)) l h := by
  have leftNe : l.left ≠ 0 := by intro zero; rw [zero] at left; contradiction
  have outSub : (l.out_ - l.left).toNat = l.out_.toNat - l.left.toNat :=
    UInt32.toNat_sub_of_le _ _ (by exact count)
  by_cases inWindow : s.offset > l.out_ - l.left
  · have inWindowNat : (l.out_ - l.left).toNat < s.offset.toNat := UInt32.lt_iff_toNat_lt.mp inWindow
    let distance := s.offset - (l.out_ - l.left)
    have distSub : distance.toNat = s.offset.toNat - (l.out_ - l.left).toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt inWindowNat))
    have distPositive : 0 < distance.toNat := by omega
    have hist : distance.toNat ≤ s.whave.toNat := by
      simpa only [UInt32.lt_iff_toNat_lt, Nat.not_lt] using history inWindow
    have wsPositive : 0 < s.wsize.toNat := by have := window.hv; omega
    have ws : s.wsize.toNat = 2 ^ s.wbits.toNat := by rcases window.ws with zero | eq; omega; exact eq
    obtain ⟨w, saved, winPtr, savedGet, _, savedSize⟩ :
        ∃ w saved, s.window = .ref (.blk w) 0 ∧ h.bytes w = some saved ∧ h.ro w = false ∧ saved.size = 2 ^ s.wbits.toNat := by
      rcases window.block with null | live
      · have zero := window.nullws null
        rw [zero] at wsPositive
        contradiction
      · exact live
    have distinct : (.blk w : BRef) ≠ dest := (separate w winPtr).symm
    have sourceGet : Space.get h (BRef.blk w) = some (if (.blk w : BRef) = dest then output else saved) := by
      simpa only [if_neg distinct, Space.get] using savedGet
    have wn : s.wnext.toNat < s.wsize.toNat := by rcases window.wn with lt | ⟨zero, _⟩; exact lt; omega
    have distSize : distance.toNat ≤ saved.size := by have := window.hv; omega
    by_cases wrap : distance > s.wnext
    · have wrapNat : s.wnext.toNat < distance.toNat := UInt32.lt_iff_toNat_lt.mp wrap
      let span := distance - s.wnext
      let start := s.wsize - span
      let capped := if span > s.length then s.length else span
      let copy := if capped > l.left then l.left else capped
      have spanNat : span.toNat = distance.toNat - s.wnext.toNat :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt wrapNat))
      have spanPositive : 0 < span.toNat := by omega
      have spanFit : span.toNat ≤ s.wsize.toNat := by have := window.hv; omega
      have startNat : start.toNat = s.wsize.toNat - span.toNat := UInt32.toNat_sub_of_le _ _ (by exact spanFit)
      have cappedBounds : 0 < capped.toNat ∧ capped.toNat ≤ span.toNat ∧ capped.toNat ≤ s.length.toNat := by
        unfold capped
        split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
      have bounds : 0 < copy.toNat ∧ copy.toNat ≤ capped.toNat ∧ copy.toNat ≤ l.left.toNat := by
        unfold copy
        split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
      have address : s.window.add (start.toNat : Int) h = .ok (.ref (.blk w) start.toNat, h) := by
        rw [winPtr]
        simpa only [OkOn, Nat.zero_add] using Ptr.add_nat_ok (r := BRef.blk w) (off := 0)
          (by exact savedGet) (by omega : 0 + start.toNat ≤ saved.size)
      refine ⟨copy, .blk w, start.toNat, saved, bounds.1, bounds.2.2,
        by omega, by omega, sourceGet, ?_, ?_⟩
      · simp only [if_neg distinct]
        omega
      · exact matchSelect_wrap_cut E l leftNe inWindow (history inWindow) wrap address
    · let start := s.wnext - distance
      let capped := if distance > s.length then s.length else distance
      let copy := if capped > l.left then l.left else capped
      have distNext : distance.toNat ≤ s.wnext.toNat := by simpa only [UInt32.lt_iff_toNat_lt, Nat.not_lt] using wrap
      have startNat : start.toNat = s.wnext.toNat - distance.toNat := UInt32.toNat_sub_of_le _ _ (by exact distNext)
      have cappedBounds : 0 < capped.toNat ∧ capped.toNat ≤ distance.toNat ∧ capped.toNat ≤ s.length.toNat := by
        unfold capped
        split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
      have bounds : 0 < copy.toNat ∧ copy.toNat ≤ capped.toNat ∧ copy.toNat ≤ l.left.toNat := by
        unfold copy
        split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
      have address : s.window.add (start.toNat : Int) h = .ok (.ref (.blk w) start.toNat, h) := by
        rw [winPtr]
        simpa only [OkOn, Nat.zero_add] using Ptr.add_nat_ok (r := BRef.blk w) (off := 0)
          (by exact savedGet) (by omega : 0 + start.toNat ≤ saved.size)
      refine ⟨copy, .blk w, start.toNat, saved, bounds.1, bounds.2.2,
        by omega, by omega, sourceGet, ?_, ?_⟩
      · simp only [if_neg distinct]
        omega
      · exact matchSelect_window_cut E l leftNe inWindow (history inWindow) wrap address
  · have inOutputNat : s.offset.toNat ≤ (l.out_ - l.left).toNat := by
      simpa only [UInt32.lt_iff_toNat_lt, Nat.not_lt] using inWindow
    let copy := if s.length > l.left then l.left else s.length
    have bounds : 0 < copy.toNat ∧ copy.toNat ≤ s.length.toNat ∧ copy.toNat ≤ l.left.toNat := by
      unfold copy
      split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
    have offFit : s.offset.toNat ≤ outOffset := by omega
    have address : l.put.add (-(s.offset.toNat : Int)) h = .ok (.ref dest (outOffset - s.offset.toNat), h) := by
      rw [put]
      exact Ptr.sub_nat_ok outGet offFit (by omega)
    refine ⟨copy, dest, outOffset - s.offset.toNat, output, bounds.1, bounds.2.2, bounds.2.1,
      by omega, by simpa only [ite_true] using outGet, ?_, ?_⟩
    · simp only [ite_true]
      omega
    · exact matchSelect_output_cut E l leftNe inWindow address

end Zlib.Inflate.Proofs
