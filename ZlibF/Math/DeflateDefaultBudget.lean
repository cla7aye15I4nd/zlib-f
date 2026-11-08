import ZlibF.Math.DeflateOverlay

/-! # Default-memory output room with the derived coarse tree-weight budget -/

namespace Zlib.Trees.Overlay
set_option autoImplicit false

/-- The source leaf budget allows at most two dummy units. The integer
cost certificates still give a sufficient excess bound with n+3, without
requiring an exact forced-weight formula for short alphabets. -/
theorem excess_from_coarse_weights {excess n literalWeight distanceWeight : Nat}
    (cost : 1000 * excess ≤ 400 * (n + 1) + 2776 * literalWeight + 1334 * n + 1747 * distanceWeight)
    (literal : literalWeight ≤ n + 3) (distance : distanceWeight ≤ n + 3) :
    1000 * excess ≤ 6257 * (n + 3) := by omega

/-- Every unread-symbol boundary retains fifteen output bits. The domain
includes default memLevel 8 and also memory levels 6, 7 and 9. The excess
and header are data premises to be established from actual construction. -/
theorem large_overlay_prefix_coarse (capacity start header : Nat) (costs : List Nat)
    (capacityMin : 4096 ≤ capacity) (startMax : start ≤ 7) (headerMax : header ≤ 2283)
    (symbolsFit : costs.length + 1 ≤ capacity)
    (excess : 1000 * bitExcess costs ≤ 6257 * (costs.length + 3)) (k : Nat) :
    start + 3 + header + (costs.take k).sum + 15 ≤ 8 * (capacity + 3 * k) := by
  have prefixBound := prefix_bits_le costs k
  omega

/-- Header, all payload symbols, end marker and final alignment fit within
31 bits per symbol slot. This is below the 32-bit total pending capacity. -/
theorem large_block_room_coarse (capacity start header : Nat) (costs : List Nat)
    (capacityMin : 4096 ≤ capacity) (startMax : start ≤ 7) (headerMax : header ≤ 2283)
    (symbolsFit : costs.length + 1 ≤ capacity)
    (excess : 1000 * bitExcess costs ≤ 6257 * (costs.length + 3)) :
    start + 3 + header + costs.sum + 15 + 7 ≤ 31 * capacity := by
  have total := prefix_bits_le costs costs.length
  rw [List.take_length] at total
  omega

/-- For default memLevel 8 the same sufficient caller output capacity as
the fixed-block path covers this dynamic budget. These are arithmetic
consequences, not by themselves a translated dynamic-branch theorem. -/
theorem default_block_room_coarse (start header : Nat) (costs : List Nat)
    (startMax : start ≤ 7) (headerMax : header ≤ 2283) (symbolsFit : costs.length + 1 ≤ 16384)
    (excess : 1000 * bitExcess costs ≤ 6257 * (costs.length + 3)) :
    start + 3 + header + costs.sum + 15 + 7 ≤ 8 * 63488 := by
  have bound := large_block_room_coarse 16384 start header costs (by decide) startMax headerMax symbolsFit excess
  omega

end Zlib.Trees.Overlay
