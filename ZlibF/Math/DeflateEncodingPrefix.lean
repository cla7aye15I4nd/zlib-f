import ZlibF.Math.DeflateBlockStream

/-! # Compose actual block encodings at their absolute bit positions -/

namespace ZlibF.Math.DeflateEncoding
open ZlibF.Spec Zlib.Trees.Proofs.Out
set_option autoImplicit false

/-- The independent format expands each byte to exactly eight bits. -/
theorem encoded_bytes_length (bytes : List UInt8) :
    (bytesToBits bytes).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    change (byteBits b ++ bytesToBits bs).length = 8 * (bs.length + 1)
    rw [List.length_append, ih]
    simp only [byteBits, List.length_map, List.length_range]
    omega

/-- A completed sequence of nonfinal blocks transforms the already decoded
history. The total stream is byte sized. The absolute starting bit position
keeps that condition meaningful after a preceding unaligned block. This is
a mathematical parser continuation, not a contract for any C function. -/
def BlockPrefix (dict : List UInt8) (offset : Nat) (history : List UInt8)
    (bits : List Bool) (next : List UInt8) : Prop :=
  ∀ suffix rest out, (offset + bits.length + suffix.length) % 8 = 0 →
    Blocks dict next suffix rest out → Blocks dict history (bits ++ suffix) rest out

/-- Before any blocks have been written the parser continuation is identity. -/
theorem block_prefix_empty (dict history : List UInt8) (offset : Nat) :
    BlockPrefix dict offset history [] history := by
  intro suffix rest out _aligned parse
  exact parse

/-- Consecutive already proved block prefixes compose without requiring
any fixed or dynamic block itself to end at a byte boundary. -/
theorem block_prefix_append {dict history middle next : List UInt8}
    {offset : Nat} {first second : List Bool}
    (left : BlockPrefix dict offset history first middle)
    (right : BlockPrefix dict (offset + first.length) middle second next) :
    BlockPrefix dict offset history (first ++ second) next := by
  intro suffix rest out aligned parse
  have alignedRight : (offset + first.length + second.length + suffix.length) % 8 = 0 := by
    simpa only [List.length_append, Nat.add_assoc] using aligned
  have parsedRight := right suffix rest out alignedRight parse
  have alignedLeft : (offset + first.length + (second ++ suffix).length) % 8 = 0 := by
    simpa only [List.length_append, Nat.add_assoc] using aligned
  simpa only [List.append_assoc] using left (second ++ suffix) rest out alignedLeft parsedRight

/-- Actual nonfinal block output has a composable parser meaning. Only a
stored block needs its ending absolute bit position to be byte aligned.
The condition is derived from the encoder's actual held-bit count. -/
theorem nonfinal_block_prefix {dict history next : List UInt8} {offset kind : Nat}
    {body : List Bool} (kindBound : kind < 4)
    (storedEnd : kind = 0 → (offset + 3 + body.length) % 8 = 0)
    (grammar : ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
      Body dict kind history (body ++ suffix) suffix next) :
    BlockPrefix dict offset history (natBits 0 1 ++ natBits kind 2 ++ body) next := by
  intro suffix rest out aligned parse
  have suffixAligned : kind = 0 → suffix.length % 8 = 0 := by
    intro stored
    have endAligned := storedEnd stored
    simp only [List.length_append, natBits_length] at aligned
    omega
  rw [List.append_assoc, List.append_assoc]
  exact Blocks.more (readBits_natBits 1 0 _ (by decide +kernel))
    (readBits_natBits 2 kind _ kindBound) (grammar suffix suffixAligned) parse

/-- A retained prefix followed by the actual final block and fewer than
one byte of padding forms a complete independent raw stream. -/
theorem block_prefix_terminal_valid {history written out : List UInt8} {completed body padding : List Bool}
    {kind : Nat} (prefixMeaning : BlockPrefix [] 0 [] completed history)
    (kindBound : kind < 4) (padBound : padding.length < 8)
    (wire : bytesToBits written = completed ++ natBits 1 1 ++ natBits kind 2 ++ body ++ padding)
    (grammar : Body [] kind history (body ++ padding) padding out) :
    Deflate.Valid out written := by
  refine ⟨padding, ?_, ?_⟩
  · have finalBlock : Blocks [] history
        (natBits 1 1 ++ natBits kind 2 ++ body ++ padding) padding out := by
      rw [List.append_assoc, List.append_assoc]
      exact Blocks.last (readBits_natBits 1 1 _ (by decide +kernel))
        (readBits_natBits 2 kind _ kindBound) grammar
    have totalAligned : (0 + completed.length +
        (natBits 1 1 ++ natBits kind 2 ++ body ++ padding).length) % 8 = 0 := by
      have exactLength := congrArg List.length wire
      rw [encoded_bytes_length] at exactLength
      simp only [List.length_append] at exactLength ⊢
      omega
    have allBlocks := prefixMeaning _ padding out totalAligned finalBlock
    rw [wire]
    simpa only [List.append_assoc] using allBlocks
  · rw [Nat.mod_eq_of_lt padBound, List.drop_length]
    rfl

end ZlibF.Math.DeflateEncoding
