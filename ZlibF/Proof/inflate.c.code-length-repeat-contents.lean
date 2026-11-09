import ZlibF.Proof.«inflate.c.code-length-literal-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inftrees.Proofs (lensOf)
set_option autoImplicit false

/-- The concrete length-array prefix below the actual have counter. -/
def actualLengthPrefix (s : InflateState) : List Nat :=
  lensOf (fun k => (s.lens.getD k 0).toNat) s.«have».toNat

/-- The previous length used by symbol 16 is the last value of the
independent prefix view. -/
theorem actualLengthPrefix_last {s : InflateState} (nonempty : 1 ≤ s.«have».toNat) :
    (actualLengthPrefix s).getLastD 0 = (s.lens.getD (s.«have».toNat - 1) 0).toNat := by
  have length : (actualLengthPrefix s).length = s.«have».toNat :=
    Zlib.Inftrees.Proofs.lensOf_length _ _
  have inside : (actualLengthPrefix s).length - 1 < (actualLengthPrefix s).length := by omega
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem inside, Option.getD_some]
  simp only [actualLengthPrefix, lensOf, List.getElem_map, List.getElem_range, List.length_map, List.length_range]

/-- Every actual repeat-loop store appends one exact length. -/
theorem clRepeat_run_contents {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (room : s.«have».toNat + l.copy.toNat ≤ 320) :
    ∃ state,
      runX (clRepeat c) l h = .ok ((.ok (), { l with copy := 0xffffffff }), setI h zs state) ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + l.copy.toNat ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate l.copy.toNat l.len.toUInt16.toNat := by
  let total := s.«have».toNat + l.copy.toNat
  let P : Nat → IL → Heap → Prop := fun k current heap => ∃ state,
    heap = setI h zs state ∧
    state = { s with lens := state.lens, «have» := state.«have» } ∧ state.lens.size = 320 ∧
    state.«have».toNat + k = total ∧
    current = { l with copy := current.copy } ∧ current.copy.toNat = k ∧
    actualLengthPrefix state = actualLengthPrefix s ++ List.replicate (l.copy.toNat - k) l.len.toUInt16.toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun result current heap => ∃ state,
    result = .ok () ∧ current = { l with copy := 0xffffffff } ∧ heap = setI h zs state ∧
    state = { s with lens := state.lens, «have» := state.«have» } ∧ state.lens.size = 320 ∧
    state.«have».toNat = total ∧
    actualLengthPrefix state = actualLengthPrefix s ++ List.replicate l.copy.toNat l.len.toUInt16.toNat
  have rule := xwhileBrk_run (cond := clRepeatCond) (body := do clRepeatBody c; pure false)
    P Q ?_ ?_ (k := l.copy.toNat) (l := l) (h := h) ?_ ?_
  · obtain ⟨result, current, after, run, state, rfl, rfl, rfl, frame, sz, count, prefixEq⟩ := rule
    exact ⟨state, run, frame, sz, count, prefixEq⟩
  · intro k current heap inv
    obtain ⟨state, heapEq, frame, sz, count, registers, remaining, prefixEq⟩ := inv
    subst heap
    have get : (setI h zs state).istates zs = some state := by simp
    have positive : current.copy ≠ 0 := by intro zero; rw [zero] at remaining; simp at remaining
    have copyCount : (current.copy - 1).toNat = k := by
      rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; simp; omega)]
      simp only [UInt32.toNat_one]
      omega
    have inside : state.«have».toNat < state.lens.size := by dsimp [total] at count; omega
    have body := clRepeatBody_run (l := { current with copy := current.copy - 1 }) hc get inside
    have countNext : (state.«have» + 1).toNat = state.«have».toNat + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
    have registers' : { current with copy := current.copy - 1 } = { l with copy := current.copy - 1 } := by rw [registers]
    refine ⟨{ current with copy := current.copy - 1 }, setI h zs state, ?_, .ok false,
      { current with copy := current.copy - 1 }, setI (setI h zs state) zs (clWrite state current.len.toUInt16), ?_, ?_⟩
    · rw [clRepeatCond_run]
      simp [positive]
    · rw [runX_bind, body]
      rfl
    · refine ⟨clWrite state current.len.toUInt16, by simp, ?_, ?_, ?_, registers', copyCount, ?_⟩
      · unfold clWrite
        rw [frame]
      · simp only [clWrite, Array.size_set!, sz]
      · simp only [clWrite, countNext]
        omega
      · have currentLen : current.len = l.len := by rw [registers]
        have written := clWrite_lens_prefix (value := current.len.toUInt16) (by omega : state.«have».toNat < 320) inside
        change actualLengthPrefix (clWrite state current.len.toUInt16) =
          actualLengthPrefix state ++ [current.len.toUInt16.toNat] at written
        rw [written, prefixEq, currentLen, List.append_assoc]
        have prefixLength := congrArg List.length prefixEq
        simp only [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf_length, List.length_append, List.length_replicate] at prefixLength
        have remainingBound : k + 1 ≤ l.copy.toNat := by dsimp [total] at count; omega
        rw [show l.copy.toNat - k = (l.copy.toNat - (k + 1)) + 1 by omega, List.replicate_succ']
  · intro current heap inv
    obtain ⟨state, heapEq, frame, sz, count, registers, remaining, prefixEq⟩ := inv
    have zero : current.copy = 0 := UInt32.toNat_inj.mp (by simpa using remaining)
    refine ⟨{ current with copy := current.copy - 1 }, heap, ?_, state, rfl, ?_, heapEq, frame, sz, by omega, ?_⟩
    · rw [clRepeatCond_run]
      simp [zero]
    · rw [registers, zero]
      rfl
    · simpa only [Nat.sub_zero] using prefixEq
  · refine ⟨s, (tcSetI_same hs).symm, rfl, size, rfl, rfl, rfl, ?_⟩
    simp
  · unfold fuel
    omega

#print axioms actualLengthPrefix_last
#print axioms clRepeat_run_contents
end Zlib.Inflate.Proofs
