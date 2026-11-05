import ZlibF.Zlib.«inftrees.c.proofs.math»
import ZlibF.Spec.Format.Huffman
import ZlibF.Runtime.Schema
import ZlibF.Zlib.«inftrees.c.spec»

namespace Zlib.Inftrees.Proofs
open ZlibF.Spec

/-- The list of lengths that the call looks at. -/
def lensOf (f : Nat → Nat) (n : Nat) : List Nat := (List.range n).map f

theorem count_lensOf (f : Nat → Nat) (n l : Nat) : ZlibF.Spec.count (lensOf f n) l = cnt f n l := by
  unfold ZlibF.Spec.count lensOf cnt fl
  rw [List.filter_map, List.length_map]
  rfl

theorem codeStart_lensOf (f : Nat → Nat) (n : Nat) : ∀ l, codeStart (lensOf f n) (l + 1) = 2 * Kc f n l
  | 0 => by simp [codeStart, Kc]
  | l + 1 => by
    rw [codeStart, codeStart_lensOf f n l]
    simp [count_lensOf, Kc]
    omega

theorem fits_iff (f : Nat → Nat) (n : Nat) : ZlibF.Spec.Fits (lensOf f n) ↔ Fits f n := by
  unfold ZlibF.Spec.Fits Zlib.Inftrees.Proofs.Fits
  constructor
  · intro h l hl1 hl2
    have hm : ZlibF.Spec.maxCodeLen = 15 := rfl
    have := h l (by simp [List.mem_range'_1, hm]; omega)
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [codeStart_lensOf, count_lensOf] at this
    simpa [Kc] using this
  · intro h l hl
    have hm : ZlibF.Spec.maxCodeLen = 15 := rfl
    simp only [List.mem_range'_1, hm] at hl
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have := h (l' + 1) (by omega) (by omega)
    rw [codeStart_lensOf, count_lensOf]
    simpa [Kc] using this

theorem complete_iff (f : Nat → Nat) (n : Nat) : ZlibF.Spec.Complete (lensOf f n) ↔ Kc f n 15 = 2 ^ 15 := by
  unfold ZlibF.Spec.Complete ZlibF.Spec.maxCodeLen
  rw [show (15 : Nat) = 14 + 1 from rfl, codeStart_lensOf, count_lensOf]
  simp [Kc]

theorem Tc_eq_len (f : Nat → Nat) :
    ∀ n, (∀ s, s < n → f s ≤ 15) → Tc f n 15 = ((List.range n).filter (fun s => decide (f s ≠ 0))).length
  | 0, _ => rfl
  | n + 1, hf => by
    rw [Tc_step, Tc_eq_len f n (fun s hs => hf s (by omega)), List.range_succ, List.filter_append]
    have := hf n (by omega)
    by_cases h : f n = 0
    · simp [h]
    · simp [h]; omega

/-- `inflate_table` accepts the lengths (the rule of `inftrees.c`, in the terms of the proofs). -/
def Acc (type : UInt32) (f : Nat → Nat) (n : Nat) : Prop :=
  Fits f n ∧ (Kc f n 15 = 2 ^ 15 ∨ Tc f n 15 = 0 ∨ (type ≠ C.CODES ∧ mxl f n = 1 ∧ Tc f n 15 = 1))

theorem zero_iff (f : Nat → Nat) (n : Nat) (hf : ∀ s, s < n → f s ≤ 15) :
    (∀ x ∈ lensOf f n, x = 0) ↔ Tc f n 15 = 0 := by
  rw [Tc_eq_len f n hf, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  simp [lensOf]

theorem single_iff (f : Nat → Nat) (n : Nat) (hf : ∀ s, s < n → f s ≤ 15) :
    (lensOf f n).filter (· != 0) = [1] ↔ (Tc f n 15 = 1 ∧ mxl f n = 1) := by
  have hI : (lensOf f n).filter (· != 0) = ((List.range n).filter (fun s => decide (f s ≠ 0))).map f := by
    unfold lensOf
    rw [List.filter_map]
    congr 1
  have hT := Tc_eq_len f n hf
  have hlen : (wsAux f n 15).length = Tc f n 15 := wsAux_length 15
  -- the first symbol of the sorted order
  have hw : Tc f n 15 = 1 →
      (wsAux f n 15).getD 0 0 ∈ (List.range n).filter (fun s => decide (f s ≠ 0)) := by
    intro h1
    have hlt : 0 < (wsAux f n 15).length := by omega
    have hm := List.getElem_mem hlt
    have := mem_wsAux.mp hm
    have hg : (wsAux f n 15).getD 0 0 = (wsAux f n 15)[0] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [hg]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨this.1, by omega⟩
  have hmx : Tc f n 15 = 1 → mxl f n = f ((wsAux f n 15).getD 0 0) := by
    intro h1; unfold mxl lenAt; rw [h1]
  rw [hI]
  constructor
  · intro h
    obtain ⟨s0, hs0, hf0⟩ := List.map_eq_singleton_iff.mp h
    have hT1 : Tc f n 15 = 1 := by rw [hT, hs0]; rfl
    refine ⟨hT1, ?_⟩
    have hmem := hw hT1
    rw [hs0] at hmem
    have : (wsAux f n 15).getD 0 0 = s0 := by simpa using hmem
    rw [hmx hT1, this]; exact hf0
  · rintro ⟨hT1, hm1⟩
    obtain ⟨s0, hs0⟩ := List.length_eq_one_iff.mp (by rw [← hT]; exact hT1)
    have hmem := hw hT1
    rw [hs0] at hmem
    have : (wsAux f n 15).getD 0 0 = s0 := by simpa using hmem
    rw [hs0]
    have : f s0 = 1 := by rw [← this, ← hmx hT1]; exact hm1
    simp [this]

theorem acc_iff (type : UInt32) (f : Nat → Nat) (n : Nat) (hf : ∀ s, s < n → f s ≤ 15) :
    Acc type f n ↔ ZlibF.Spec.Acceptable (Zlib.Inftrees.Spec.kindOf type) (lensOf f n) := by
  unfold Acc ZlibF.Spec.Acceptable
  have hk : Zlib.Inftrees.Spec.kindOf type ≠ ZlibF.Spec.CodeKind.codeLength ↔ type ≠ C.CODES := by
    unfold Zlib.Inftrees.Spec.kindOf
    by_cases h1 : type = C.CODES
    · simp [h1]
    · by_cases h2 : type = C.LENS <;> simp [h1, h2]
  have hb : ∀ x ∈ lensOf f n, x ≤ ZlibF.Spec.maxCodeLen := by
    intro x hx
    simp only [lensOf, List.mem_map, List.mem_range] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact hf s hs
  rw [fits_iff, complete_iff, zero_iff f n hf, hk]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hb, h1, ?_⟩
    rcases h2 with h | h | ⟨a, b, c⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨a, (single_iff f n hf).mpr ⟨c, b⟩⟩)
  · rintro ⟨_, h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases h2 with h | h | ⟨a, b⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨c, d⟩ := (single_iff f n hf).mp b
      exact Or.inr (Or.inr ⟨a, d, c⟩)

end Zlib.Inftrees.Proofs
