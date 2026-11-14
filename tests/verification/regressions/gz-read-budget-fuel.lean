import ZlibF.Proof.«gz.inv-model»

/-!
# gz: a finite read budget alone does not keep the reading loops within the fuel

**What this regression is.** It is the arithmetic core of the correction of `ReadsFinite` (commit 3683a982). It is
**not** a checked run of `gz_fetch` returning `outOfFuel`.

The old premise was what `HasBudget` says now: a non-negative descriptor with some read budget. A budget of `2^70`
bytes satisfies it. Such a source can deliver empty gzip members of 20 bytes each: a 10-byte header, a final fixed
block with only its end code (`03 00`), and an 8-byte trailer. Each empty member takes at least one round of
`gz_fetch`'s loop, a member end with no output, and the loop goes on while the input lasts. So one call needs more
than `2^70 / 20` rounds, more than the `2^64` trips of fuel of a loop of the model (`C.fuel`). The termination half
of `Goal.gz_sequence_safety` then fails for that world. The new `ReadsFinite` excludes it: the budget must be below
`2^61`.

The bound is a limit of the model (loop fuel `2^64`), not of zlib. It touches only the termination half of the goal.
-/

namespace GzReadBudgetFuelRegression
open C ZlibF.Spec.Public Zlib.GzFs

/-- A world whose descriptor 0 can still deliver `2^70` bytes. -/
def bigBudget : Fs := { (default : Fs) with readBudget := fun _ => some (2 ^ 70) }

/-- The bytes of one empty gzip member: header, final fixed block with only its end code, trailer. -/
def emptyMemberBytes : Nat := 10 + 2 + 8

/-- **The old premise admits a budget whose required rounds exceed the loop fuel**, and the new `ReadsFinite`
excludes that budget. -/
theorem old_premise_admits_budget_beyond_fuel :
    HasBudget bigBudget 0 ∧ ¬ ReadsFinite bigBudget 0 ∧ C.fuel < 2 ^ 70 / emptyMemberBytes := by
  refine ⟨⟨by decide, by simp [bigBudget]⟩, fun ⟨_, hlt⟩ => ?_, by decide⟩
  simp [bigBudget] at hlt

end GzReadBudgetFuelRegression
