import ZlibF.Math.«whole-epoch-original-valid-body»
import ZlibF.Proof.«inflate.c.whole-epoch-trailer-finished»
import ZlibF.Proof.Format.Deflate

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A wrong complete checksum word is rejected using only credited
bytes. Independently valid continuations must parse the same completed
blocks and output, and hence require the exact different Adler trailer. -/
theorem Trailer.rejects_checksum_word
    {log : DataLog} {wire word : List Bool} {input : List UInt8}
    (trailer : Trailer log wire) (empty : trailer.checksumWord = [])
    (source : bytesBits input = wire ++ word) (length : word.length = 32)
    (mismatch : word ≠ bytesBits (be32 (adler32 log.output).toNat)) :
    ∀ future decoded, ¬ Zlib.Decodes log.dictionary (input ++ future) decoded := by
  intro future decoded valid
  have completeSource : bytesBits (input ++ future) = bytesBits trailer.wrapper.bytes ++
      (trailer.bodyWord ++ trailer.padding ++ word ++ bytesBits future) := by
    rw [bytesBits_append, source]
    simpa only [empty, List.append_nil, List.append_assoc] using
      congrArg (fun before => before ++ word ++ bytesBits future) trailer.anchor
  obtain ⟨bodyBytes, bytes, bodyBits⟩ := bytes_prefix_of_bits completeSource
  have bodyValid := trailer.wrapper.original_valid_body (by rwa [bytes] at valid)
  obtain ⟨rest, parsed, skipped⟩ := bodyValid
  have alignment : (trailer.bodyWord.length +
      (trailer.padding ++ word ++ bytesBits future).length) % 8 = 0 := by
    have before := trailer.aligned
    simp only [List.length_append, bytesBits_length, length]
    omega
  have original := trailer.blocks (trailer.padding ++ word ++ bytesBits future) alignment
  have parse : Blocks trailer.wrapper.dictionary []
      (trailer.bodyWord ++ trailer.padding ++ word ++ bytesBits future) rest decoded := by
    rw [bytesBits_eq_bytesToBits, bodyBits] at parsed
    exact parsed
  have same := Blocks.det (by simpa only [List.append_assoc] using original) parse
  have restEq : trailer.padding ++ word ++ bytesBits future = rest := by
    simpa only [List.append_assoc] using same.1
  have outputEq : log.output = decoded := same.2
  rw [← restEq, ← outputEq, bytesBits_eq_bytesToBits] at skipped
  have paddingCount : (trailer.padding ++ word ++ bytesBits future).length % 8 =
      trailer.padding.length := by
    have short := trailer.shortPadding
    simp only [List.length_append, bytesBits_length, length]
    omega
  rw [paddingCount] at skipped
  have suffix : word ++ bytesBits future = bytesBits (be32 (adler32 log.output).toNat) := by
    simpa only [List.append_assoc, List.drop_left] using skipped
  have expectedLength : (bytesBits (be32 (adler32 log.output).toNat)).length = 32 := by
    simp only [bytesBits_length, be32, List.length_cons, List.length_nil]
  apply mismatch
  have first := congrArg (List.take 32) suffix
  have actualFirst : (word ++ bytesBits future).take 32 = word := by
    rw [← length]
    simp
  have expectedFirst : (bytesBits (be32 (adler32 log.output).toNat)).take 32 =
      bytesBits (be32 (adler32 log.output).toNat) := by
    rw [← expectedLength]
    simp
  exact actualFirst.symm.trans (first.trans expectedFirst)

#print axioms Trailer.rejects_checksum_word
end Zlib.Inflate.Proofs.WholeEpoch
