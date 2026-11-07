import ZlibF.Math.DeflateRunDecode

/-! # A final independently decoded block is a complete raw stream -/

namespace Zlib.Trees.Proofs.Out
open C ZlibF.Spec
set_option autoImplicit false

/-- A byte-encoded final tag, independently decoded body and fewer than
eight trailing pad bits constitute a complete raw DEFLATE stream. -/
theorem terminal_block_valid {written out : List UInt8} {kind : Nat} {body padding : List Bool}
    (kindBound : kind < 4) (padBound : padding.length < 8)
    (wire : bytesToBits written = natBits 1 1 ++ natBits kind 2 ++ body ++ padding)
    (grammar : Body [] kind [] (body ++ padding) padding out) : Deflate.Valid out written := by
  refine ⟨padding, ?_, ?_⟩
  · rw [wire, List.append_assoc, List.append_assoc]
    exact Blocks.last (readBits_natBits 1 1 _ (by decide +kernel))
      (readBits_natBits 2 kind _ kindBound) grammar
  · rw [Nat.mod_eq_of_lt padBound, List.drop_length]
    rfl

end Zlib.Trees.Proofs.Out
