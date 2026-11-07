import ZlibF.Math.LZ77HistorySpec

/-!
# Chunked copies and retained independent history

Every step reads the same byte when the requested distance is inside the
retained suffix. Induction then preserves both complete and retained views.
-/

set_option autoImplicit false

namespace ZlibF.Math.LZ77History
open ZlibF.Spec

/-- A match appends exactly one byte at each step and never changes old
output, even when a caller supplies an invalid distance to the pure model. -/
theorem copy_back_extends_history : Goal.copy_back_extends_history := by
  intro dict history dist n
  induction n generalizing history with
  | zero => simp [copyBack]
  | succ n ih =>
    let value := (dict ++ history).getD ((dict ++ history).length - dist) 0
    have next := ih (history ++ [value])
    constructor
    · exact (List.prefix_append history [value]).trans next.1
    · simpa only [copyBack, value, List.length_append, List.length_singleton,
        Nat.add_assoc, Nat.add_comm 1 n] using next.2

/-- Splitting a match into physical chunks does not change its bytewise
independent result. -/
theorem copy_back_compose : Goal.copy_back_compose := by
  intro dict history dist n m
  induction n generalizing history with
  | zero => simp [copyBack]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [copyBack]
    exact ih _

private theorem retained_source (dict past current saved : List UInt8) (dist : Nat)
    (hs : saved <:+ (dict ++ past)) (hd : dist ≤ saved.length + current.length) :
    (dict ++ (past ++ current)).getD ((dict ++ (past ++ current)).length - dist) 0 =
      (saved ++ current).getD ((saved ++ current).length - dist) 0 := by
  obtain ⟨older, he⟩ := hs
  have hword : dict ++ (past ++ current) = older ++ (saved ++ current) := by
    rw [← List.append_assoc, ← he, List.append_assoc]
  rw [hword]
  have hr : older.length ≤ (older ++ (saved ++ current)).length - dist := by
    simp only [List.length_append] at *
    omega
  have hi : (older ++ (saved ++ current)).length - dist - older.length =
      (saved ++ current).length - dist := by
    simp only [List.length_append] at *
    omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hr, hi]

/-- Replacing complete prior history by a suffix preserves every newly
copied byte as long as the match reaches only retained history. -/
theorem retained_history_agrees : Goal.retained_history_agrees := by
  intro dict past current saved dist n hs hpositive hdist
  induction n generalizing current with
  | zero => simp [copyBack]
  | succ n ih =>
    have hvalue := retained_source dict past current saved dist hs hdist
    rw [copyBack, copyBack, hvalue]
    rw [List.append_assoc]
    exact ih (current ++ [(saved ++ current).getD ((saved ++ current).length - dist) 0])
      (by simp only [List.length_append, List.length_singleton]; omega)

/-- A complete retained window discards only history that a capacity-bounded
distance cannot reach, so the two invalid-distance tests coincide. -/
theorem window_distance_check_agrees : Goal.window_distance_check_agrees := by
  intro dict past current capacity dist hdist
  simp only [List.length_append, List.length_drop]
  omega

end ZlibF.Math.LZ77History
