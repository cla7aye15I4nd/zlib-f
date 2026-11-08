import Init.Tactics

namespace ZlibF.Math.InflateFastPullBudget

/-- The fast decoder's bit widths allow at most six input pulls in one
body pass. The variables describe the actual length and distance code
widths and their optional extra-bit reads. The caller must separately
establish these width and branch facts from the checked tables. -/
theorem at_most_six
    {entry lengthWidth lengthExtra distanceWidth distanceExtra : Nat}
    {initialPulls lengthPulls refillPulls distancePulls : Nat}
    {beforeLength afterLength afterExtra beforeDistance afterDistance : Nat}
    (initial : (initialPulls = 2 ∧ entry < 15) ∨
      (initialPulls = 0 ∧ 15 ≤ entry))
    (beforeLengthEq : beforeLength = entry + 8 * initialPulls)
    (lengthBound : lengthWidth ≤ 15 ∧ lengthWidth ≤ beforeLength)
    (afterLengthEq : afterLength = beforeLength - lengthWidth)
    (extraBound : lengthExtra ≤ 5)
    (extra : (lengthPulls = 1 ∧ afterLength < lengthExtra) ∨
      (lengthPulls = 0 ∧ lengthExtra ≤ afterLength))
    (afterExtraEq : afterExtra = afterLength + 8 * lengthPulls - lengthExtra)
    (refill : (refillPulls = 2 ∧ afterExtra < 15) ∨
      (refillPulls = 0 ∧ 15 ≤ afterExtra))
    (beforeDistanceEq : beforeDistance = afterExtra + 8 * refillPulls)
    (distanceBound : distanceWidth ≤ 15 ∧ distanceWidth ≤ beforeDistance)
    (afterDistanceEq : afterDistance = beforeDistance - distanceWidth)
    (distanceExtraBound : distanceExtra ≤ 13)
    (distance : (distancePulls = 0 ∧ distanceExtra ≤ afterDistance) ∨
      (distancePulls = 1 ∧ afterDistance < distanceExtra ∧
        distanceExtra ≤ afterDistance + 8) ∨
      (distancePulls = 2 ∧ afterDistance + 8 < distanceExtra)) :
    initialPulls + lengthPulls + refillPulls + distancePulls ≤ 6 := by
  rcases initial with ⟨_, _⟩ | ⟨_, _⟩ <;>
  rcases extra with ⟨_, _⟩ | ⟨_, _⟩ <;>
  rcases refill with ⟨_, _⟩ | ⟨_, _⟩ <;>
  rcases distance with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;>
  omega

/-- Once the checked code widths justify each nonwrapping bit drop,
the final held-bit count is bounded by the entry bits and actual pulls.
The same inequality applies to earlier broken exits by omitting later
nonnegative drops and pulls. -/
theorem final_bits_le
    {entry lengthWidth lengthExtra distanceWidth distanceExtra : Nat}
    {initialPulls lengthPulls refillPulls distancePulls : Nat}
    {beforeLength afterLength afterExtra beforeDistance afterDistance finalBits : Nat}
    (beforeLengthEq : beforeLength = entry + 8 * initialPulls)
    (lengthBound : lengthWidth ≤ beforeLength)
    (afterLengthEq : afterLength = beforeLength - lengthWidth)
    (extraBound : lengthExtra ≤ afterLength + 8 * lengthPulls)
    (afterExtraEq : afterExtra = afterLength + 8 * lengthPulls - lengthExtra)
    (beforeDistanceEq : beforeDistance = afterExtra + 8 * refillPulls)
    (distanceBound : distanceWidth ≤ beforeDistance)
    (afterDistanceEq : afterDistance = beforeDistance - distanceWidth)
    (distanceExtraBound : distanceExtra ≤ afterDistance + 8 * distancePulls)
    (finalEq : finalBits = afterDistance + 8 * distancePulls - distanceExtra) :
    finalBits ≤ entry + 8 *
      (initialPulls + lengthPulls + refillPulls + distancePulls) := by
  omega

#print axioms at_most_six
#print axioms final_bits_le
end ZlibF.Math.InflateFastPullBudget
