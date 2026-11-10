import ZlibF.Math.DeflateEncodingPrefix
import ZlibF.Math.DeflateFlushMarkers

/-! # Empty flush markers compose at the actual cumulative bit position -/

namespace ZlibF.Math.DeflateEncoding
open C ZlibF.Spec Zlib.Trees.Proofs.Out
set_option autoImplicit false

/-- An empty fixed PARTIAL marker changes no decoded input at any bit
position. It is a mathematical block prefix, not a C callee contract. -/
theorem partial_marker_block_prefix (offset : Nat) (history : List UInt8) :
    BlockPrefix [] offset history (natBits 2 3 ++ natBits 0 7) history := by
  intro suffix rest out _aligned parse
  exact partial_marker_continuation parse

/-- Actual stored-marker padding ends at a byte boundary when the
cumulative position agrees with the current held-bit count modulo eight. -/
theorem stored_header_zero_end_aligned (d : DeflateState) {offset : Nat}
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8) :
    (offset + (storedHeaderBits d 0 false).length) % 8 = 0 := by
  simp only [storedHeaderBits, List.length_append, natBits_length, List.length_replicate]
  omega

/-- Empty SYNC/FULL stored markers preserve independent block meaning.
Their necessary suffix alignment follows from the actual cumulative bit
position and the complete continuation's alignment. -/
theorem stored_header_zero_block_prefix (d : DeflateState) {offset : Nat}
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8) (history : List UInt8) :
    BlockPrefix [] offset history (storedHeaderBits d 0 false) history := by
  intro suffix rest out aligned parse
  have markerAligned := stored_header_zero_end_aligned d position
  have suffixAligned : suffix.length % 8 = 0 := by omega
  exact stored_header_zero_continuation d suffixAligned parse

end ZlibF.Math.DeflateEncoding
