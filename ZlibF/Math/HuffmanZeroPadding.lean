import ZlibF.Spec.Format.Deflate
import Std.Tactic

/-! # Trailing unused symbols preserve independent Huffman decoding -/

namespace ZlibF.Spec.Proofs
open ZlibF.Spec

/-- An unused trailing symbol has the same default length as an absent one. -/
theorem getD_zeroPadding (ls : List Nat) (k i : Nat) :
    (ls ++ List.replicate k 0).getD i 0 = ls.getD i 0 := by
  induction ls generalizing i with
  | nil => simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

/-- Zero lengths do not contribute to any positive code-length count. -/
theorem count_zeroPadding (ls : List Nat) (k b : Nat) (hb : b ≠ 0) :
    count (ls ++ List.replicate k 0) b = count ls b := by
  simp [count, List.filter_append, Ne.symm hb]

/-- The canonical starting-code recurrence ignores length-zero counts. -/
theorem codeStart_zeroPadding (ls : List Nat) (k b : Nat) :
    codeStart (ls ++ List.replicate k 0) b = codeStart ls b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [codeStart, ih]
    by_cases hb : b = 0
    · simp [hb]
    · rw [ite_eq_right hb, ite_eq_right hb, count_zeroPadding ls k b hb]

/-- Every old canonical code has exactly the same bits after padding. -/
theorem codeOf_zeroPadding (ls : List Nat) (k s : Nat) :
    codeOf (ls ++ List.replicate k 0) s = codeOf ls s := by
  unfold codeOf
  rw [getD_zeroPadding]
  dsimp only
  rw [codeStart_zeroPadding]
  by_cases hz : ls.getD s 0 = 0
  · rw [hz]
    rfl
  · rw [List.take_append, List.filter_append, List.take_replicate]
    simp only [List.getD_eq_getElem?_getD] at hz ⊢
    simp [Ne.symm hz]

/-- Adding unused trailing symbols preserves the complete independent
symbol decoder on every bit sequence, including rejection. -/
theorem decodeSym_zeroPadding (ls : List Nat) (k : Nat) (inp : List Bool) :
    decodeSym (ls ++ List.replicate k 0) inp = decodeSym ls inp := by
  unfold decodeSym
  simp only [List.length_append, List.length_replicate, getD_zeroPadding, codeOf_zeroPadding]
  rw [List.range_add, List.find?_append]
  have hz : ((List.range k).map (fun x => ls.length + x)).find?
      (fun s => ls.getD s 0 != 0 && (codeOf ls s).isPrefixOf inp) = none := by
    apply List.find?_eq_none.mpr
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
    simp [List.getD_eq_getElem?_getD]
  rw [hz, Option.or_none]

/-- Code-length derivations are unchanged by unused trailing symbols. -/
theorem codeLens_zeroPadding {cl : List Nat} {total : Nat} {acc out : List Nat}
    {inp rest : List Bool} (k : Nat) (hc : CodeLens cl total acc inp rest out) :
    CodeLens (cl ++ List.replicate k 0) total acc inp rest out := by
  induction hc with
  | done h => exact CodeLens.done h
  | len h hd hs hc ih =>
    exact CodeLens.len h (by rw [decodeSym_zeroPadding]; exact hd) hs ih
  | rep16 h hd hn hr hb hc ih =>
    exact CodeLens.rep16 h (by rw [decodeSym_zeroPadding]; exact hd) hn hr hb ih
  | rep17 h hd hr hb hc ih =>
    exact CodeLens.rep17 h (by rw [decodeSym_zeroPadding]; exact hd) hr hb ih
  | rep18 h hd hr hb hc ih =>
    exact CodeLens.rep18 h (by rw [decodeSym_zeroPadding]; exact hd) hr hb ih

/-- Zero padding also preserves the independent code acceptance rules. -/
theorem acceptable_zeroPadding {kind : CodeKind} {ls : List Nat}
    (k : Nat) (ha : Acceptable kind ls) : Acceptable kind (ls ++ List.replicate k 0) := by
  obtain ⟨h15, hf, hc⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hl | hr
    · exact h15 x hl
    · have hx0 : x = 0 := List.eq_of_mem_replicate hr
      subst x
      decide +kernel
  · intro b hb
    have hb0 : b ≠ 0 := by
      have := List.mem_range'.mp hb
      omega
    rw [codeStart_zeroPadding, count_zeroPadding _ _ _ hb0]
    exact hf b hb
  · rcases hc with hfull | hzero | ⟨hkind, hsingle⟩
    · left
      rw [Complete, codeStart_zeroPadding, count_zeroPadding _ _ _ (by decide +kernel)]
      exact hfull
    · right; left
      intro x hx
      rcases List.mem_append.mp hx with hl | hr
      · exact hzero x hl
      · exact List.eq_of_mem_replicate hr
    · right; right
      refine ⟨hkind, ?_⟩
      simpa only [List.filter_append, List.filter_replicate, bne_self_eq_false,
        Bool.false_eq_true, ite_false, List.append_nil] using hsingle

end ZlibF.Spec.Proofs
