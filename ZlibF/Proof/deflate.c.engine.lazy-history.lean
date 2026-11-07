import ZlibF.Proof.«deflate.c.engine.slow-defer»
import ZlibF.Proof.«deflate.c.engine.tally-match»

/-! # Matching history across the slow strategy's lazy step

Only an improving search establishes a new current match. A stale
position returned at the old length is never treated as such a witness.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- At loop entry a retained match belongs to the previous byte. -/
def WindowLazyHistory (d : DeflateState) (wa : Array UInt8) : Prop :=
  d.match_length.toNat ≤ 258 ∧
    (3 ≤ d.match_length.toNat →
      1 ≤ d.strstart.toNat ∧ d.match_available ≠ 0 ∧
      d.match_length.toNat ≤ d.lookahead.toNat + 1 ∧
      GoodMatch wa (d.strstart.toNat - 1) d.w_size.toNat d.match_start.toNat d.match_length.toNat)

/-- After lazy preparation the same witness is in prev_match/prev_length. -/
def WindowPreviousHistory (d : DeflateState) (wa : Array UInt8) : Prop :=
  d.prev_length.toNat ≤ 258 ∧
    (3 ≤ d.prev_length.toNat →
      1 ≤ d.strstart.toNat ∧ d.match_available ≠ 0 ∧
      d.prev_length.toNat ≤ d.lookahead.toNat + 1 ∧
      GoodMatch wa (d.strstart.toNat - 1) d.w_size.toNat d.prev_match.toNat d.prev_length.toNat)

theorem window_lazy_history_initial {d : DeflateState} (length : d.match_length = 2) (wa : Array UInt8) :
    WindowLazyHistory d wa := by
  refine ⟨by rw [length]; decide, ?_⟩
  intro large
  rw [length] at large
  change 3 ≤ 2 at large
  omega

theorem initialized_window_lazy_history {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d) (wa : Array UInt8) :
    WindowLazyHistory d wa := window_lazy_history_initial start.matchLength wa

theorem window_lazy_prepare_history {d : DeflateState} {wa : Array UInt8}
    (history : WindowLazyHistory d wa) (key : UInt32) :
    WindowPreviousHistory (lazyPrepare { d with ins_h := key }) wa := history

/-- The actual match-emission test has failed. A current match of length
at least MIN_MATCH must therefore improve the previous lazy length. -/
theorem literal_search_improves {d : DeflateState}
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (large : 3 ≤ d.match_length.toNat) : d.prev_length.toNat < d.match_length.toNat := by
  by_cases previous : MIN_MATCH_u ≤ d.prev_length
  · have notle : ¬ d.match_length ≤ d.prev_length := by
      intro le
      have same : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true := by
        simp only [previous, le, decide_true, Bool.true_and]
      rw [branch] at same
      contradiction
    rw [UInt32.le_iff_toNat_le] at notle
    omega
  · rw [UInt32.le_iff_toNat_le] at previous
    change ¬ 3 ≤ d.prev_length.toNat at previous
    omega

/-- Source consumption moves a verified current match to the previous
position and retains the remaining-length bound. -/
theorem window_lazy_history_defer {h : Heap} {ds : Nat} {d : DeflateState} {wa : Array UInt8}
    (inv : DStInv h ds d)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat) (length : d.match_length.toNat ≤ 258)
    (matching : 3 ≤ d.match_length.toNat →
      GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat) :
    WindowLazyHistory (deferOne d) wa := by
  have counts := advance_one_counts inv range (by omega)
  refine ⟨length, ?_⟩
  intro large
  have ss : (deferOne d).strstart.toNat = d.strstart.toNat + 1 := counts.1
  have la : (deferOne d).lookahead.toNat = d.lookahead.toNat - 1 := counts.2.1
  refine ⟨by rw [ss]; omega, by change (1 : Int32) ≠ 0; decide, ?_, ?_⟩
  · change d.match_length.toNat ≤ (deferOne d).lookahead.toNat + 1
    rw [la]
    omega
  · change GoodMatch wa ((deferOne d).strstart.toNat - 1) d.w_size.toNat
      d.match_start.toNat d.match_length.toNat
    rw [ss, Nat.add_sub_cancel]
    exact matching large

/-- The previous match gives both the mathematical distance used by the
symbol and all unsigned subtraction bounds needed by the actual macro. -/
theorem window_previous_match_tally_bounds {d : DeflateState} {wa : Array UInt8}
    (history : WindowPreviousHistory d wa) (selected : 3 ≤ d.prev_length.toNat)
    (window : d.w_size.toNat ≤ 32768) :
    let distance := d.strstart - 1 - d.prev_match
    let length := d.prev_length - MIN_MATCH_u
    distance.toNat = d.strstart.toNat - 1 - d.prev_match.toNat ∧
      1 ≤ distance.toNat ∧ distance.toNat ≤ 32768 ∧
      length.toNat = d.prev_length.toNat - 3 ∧ length.toNat ≤ 255 ∧
      d.prev_length.toNat - 1 ≤ d.lookahead.toNat := by
  obtain ⟨start, _, room, earlier, distance, _, _⟩ := history.2 selected
  have ss : (d.strstart - 1).toNat = d.strstart.toNat - 1 := u32_sub_one start
  have dist : (d.strstart - 1 - d.prev_match).toNat = d.strstart.toNat - 1 - d.prev_match.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, ss]; omega), ss]
  have len : (d.prev_length - MIN_MATCH_u).toNat = d.prev_length.toNat - 3 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact selected)]
    rfl
  have maximum := history.1
  exact ⟨dist, by rw [dist]; omega, by rw [dist]; omega, len, by rw [len]; omega, by omega⟩

end Zlib.Deflate.Engine.Proofs
