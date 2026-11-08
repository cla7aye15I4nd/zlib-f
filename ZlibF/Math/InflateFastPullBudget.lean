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

#print axioms at_most_six
end ZlibF.Math.InflateFastPullBudget
