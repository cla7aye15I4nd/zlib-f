import ZlibF.Proof.Format.Deflate
import ZlibF.Spec.Format.Wrapper
import ZlibF.Math.DeflateByteEncoding

/-! # Any independently valid raw stream admits its exact zlib trailer -/

namespace ZlibF.Math.DeflateEncoding
open ZlibF.Spec
set_option autoImplicit false

/-- Appending whole trailer bytes retains the actual raw parse and leaves
exactly those bytes after its ignored final-bit padding. Every block kind
and every number of blocks are included. -/
theorem raw_valid_trailer_prefix {input raw : List UInt8} (valid : Deflate.Valid input raw)
    (trailer : List UInt8) : Deflate.Prefix [] (raw ++ trailer) trailer input := by
  obtain ⟨rest, blocks, skipped⟩ := valid
  have length := Proofs.bytesToBits_len trailer
  have aligned : (bytesToBits trailer).length % 8 = 0 := by omega
  have blocksA := blocks.append (bytesToBits trailer) aligned
  refine ⟨rest ++ bytesToBits trailer, ?_, ?_⟩
  · simpa only [bytesToBits, List.flatMap_append] using blocksA
  · have padding : (rest ++ bytesToBits trailer).length % 8 = rest.length % 8 := by
      rw [List.length_append, length]
      omega
    rw [padding, List.drop_append_of_le_length (Nat.mod_le _ _), skipped]
    rfl

/-- Independent raw validity plus the default two-byte header and exact
Adler trailer gives independent zlib validity. This does not depend on the
encoder's final block choice or any C execution contract. -/
theorem raw_valid_zlib_grammar {input raw : List UInt8} (valid : Deflate.Valid input raw) :
    Zlib.Valid input ([120, 156] ++ raw ++ be32 (adler32 input).toNat) := by
  refine ⟨120, 156, [], raw ++ be32 (adler32 input).toNat, rfl, by decide, ?_, ?_⟩
  · intro _
    exact ⟨rfl, raw_valid_trailer_prefix valid _⟩
  · intro impossible
    have falseEq : (0 : Nat) = 1 := impossible
    contradiction

end ZlibF.Math.DeflateEncoding
