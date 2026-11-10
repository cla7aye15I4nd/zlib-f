import Init.Data.Array.Lemmas

namespace ZlibF.Math.InflateMatchCopy

/-- The source is the growing output when same is true, or fixed saved
bytes otherwise. A later read can observe a byte written earlier. -/
def copy (same : Bool) (saved : Array UInt8) : Nat → Nat → Nat → Array UInt8 → Array UInt8
  | 0, _, _, output => output
  | count + 1, sourceOffset, dest, output =>
      let source := if same then output else saved
      copy same saved count (sourceOffset + 1) (dest + 1) (output.set! dest (source.getD sourceOffset 0))

theorem copy_size (same : Bool) (saved : Array UInt8) :
    ∀ count sourceOffset dest output, (copy same saved count sourceOffset dest output).size = output.size
  | 0, _, _, _ => rfl
  | count + 1, sourceOffset, dest, output => by simp [copy, copy_size same saved count]

/-- Only the destination interval can change, even for overlapping copies. -/
theorem copy_get_outside (same : Bool) (saved : Array UInt8) :
    ∀ count sourceOffset dest output i, i < dest ∨ dest + count ≤ i →
      (copy same saved count sourceOffset dest output).getD i 0 = output.getD i 0
  | 0, _, _, _, _, _ => rfl
  | count + 1, sourceOffset, dest, output, i, outside => by
      rw [copy, copy_get_outside same saved count (sourceOffset + 1) (dest + 1) _ i (by omega)]
      have different : dest ≠ i := by omega
      simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_ne different]

/-- A disjoint caller input slice is unchanged by the complete copy. -/
theorem copy_slice (same : Bool) (saved : Array UInt8) (count sourceOffset dest : Nat)
    (output : Array UInt8) (start size : Nat)
    (fit : start + size ≤ output.size) (separate : start + size ≤ dest ∨ dest + count ≤ start) :
    ((copy same saved count sourceOffset dest output).toList.drop start).take size =
      (output.toList.drop start).take size := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Array.length_toList, copy_size]
  · intro i hi hj
    have iBound : i < size := by simp only [List.length_take] at hi; omega
    have originalBound : start + i < output.size := by omega
    have copiedBound : start + i < (copy same saved count sourceOffset dest output).size := by
      rw [copy_size]
      exact originalBound
    have eq := copy_get_outside same saved count sourceOffset dest output (start + i) (by omega)
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem originalBound,
      Array.getElem?_eq_getElem copiedBound, Option.getD_some] at eq
    simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList] using eq

end ZlibF.Math.InflateMatchCopy
