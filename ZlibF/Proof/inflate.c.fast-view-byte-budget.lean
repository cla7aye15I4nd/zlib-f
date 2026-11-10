import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-invariant»

namespace Zlib.Inflate.Proofs

set_option autoImplicit false

/-- Once the fast body has pulled its first two bytes, a length and distance
pair can pull at most four more bytes. The branch structure follows the
translated length-extra, distance-refill and distance-extra tests. -/
theorem fast_four_byte_budget
    (held lenBits lenExtra distBits distExtra : Nat)
    (heldBound : 16 ≤ held)
    (lenCode : lenBits ≤ 15)
    (lenExtraBound : lenExtra ≤ 5)
    (distCode : distBits ≤ 15)
    (distExtraBound : distExtra ≤ 13) :
    let lenPull := if held - lenBits < lenExtra then 1 else 0
    let afterLen := held - lenBits + 8 * lenPull - lenExtra
    let refill := if afterLen < 15 then 2 else 0
    let afterDist := afterLen + 8 * refill - distBits
    let distPull :=
      if afterDist < distExtra then
        if afterDist + 8 < distExtra then 2 else 1
      else 0
    lenPull + refill + distPull ≤ 4 := by
  dsimp
  repeat' split
  all_goals omega

end Zlib.Inflate.Proofs
