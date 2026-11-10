import ZlibF.Proof.«inflate.c.whole-epoch-final-acceptance»
import ZlibF.Math.«whole-epoch-wrapper-prefix»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- BYTEBITS adds only the actual final padding to a completed block
source. No checksum bytes or source completion are guessed. -/
theorem CompletedBody.begin_trailer {log : DataLog} {wire padding : List Bool}
    (complete : CompletedBody log wire) (short : padding.length < 8)
    (aligned : (complete.bodyWord.length + padding.length) % 8 = 0) :
    Nonempty (Trailer log (wire ++ padding)) := by
  refine ⟨{
    wrapper := complete.wrapper
    bodyWord := complete.bodyWord
    blocks := complete.blocks
    padding := padding
    shortPadding := short
    aligned := aligned
    checksumWord := []
    checksumPrefix := ⟨bytesBits (be32 (adler32 log.output).toNat), rfl⟩
    anchor := by
      simpa only [List.append_nil] using congrArg (fun word => word ++ padding) complete.anchor
  }⟩

/-- Full actual checksum credit and an empty saved bit buffer reconstruct
the exact source bytes and the independent wrapped DEFLATE prefix. -/
theorem Trailer.finished_of_credited {log : DataLog} {wire : List Bool} {hold : UInt64}
    (trailer : Trailer log wire)
    (complete : trailer.checksumWord = bytesBits (be32 (adler32 log.output).toNat))
    (credit : CausalInput.Credited log.input wire 0 hold) : Nonempty (Finished log) := by
  have source : bytesBits log.input = bytesBits trailer.wrapper.bytes ++
      (trailer.bodyWord ++ trailer.padding ++ bytesBits (be32 (adler32 log.output).toNat)) := by
    simpa only [CausalInput.Credited, UInt32.toNat_zero, natBits, List.append_nil,
      trailer.anchor, complete, List.append_assoc] using credit
  obtain ⟨suffix, bytes, bits⟩ := bytes_prefix_of_bits source
  refine ⟨{ wrapper := trailer.wrapper, bodyAndTrailer := suffix, source := bytes, deflate := ?_ }⟩
  refine ⟨trailer.padding ++ bytesBits (be32 (adler32 log.output).toNat), ?_, ?_⟩
  · rw [bytesBits_eq_bytesToBits, bits]
    have aligned : (trailer.bodyWord.length +
        (trailer.padding ++ bytesBits (be32 (adler32 log.output).toNat)).length) % 8 = 0 := by
      have before := trailer.aligned
      rw [List.length_append, bytesBits_length]
      omega
    simpa only [List.append_assoc] using trailer.blocks _ aligned
  · rw [bytesBits_eq_bytesToBits]
    have skipped : (trailer.padding ++ bytesBits (be32 (adler32 log.output).toNat)).length % 8 =
        trailer.padding.length := by
      have short := trailer.shortPadding
      rw [List.length_append, bytesBits_length]
      omega
    rw [skipped]
    simp

/-- The actual DONE scalar and full checksum select the finished branch
of the same finite source spine. Accepted-call preservation is separate. -/
theorem Trailer.done_phase {log : DataLog} {wire : List Bool} {s : InflateState}
    (trailer : Trailer log wire) (mode : s.mode = DONE) (empty : s.bits = 0)
    (complete : trailer.checksumWord = bytesBits (be32 (adler32 log.output).toNat))
    (credit : CausalInput.Credited log.input wire s.bits s.hold) :
    Nonempty (SourcePhase log s wire) := by
  rw [empty] at credit
  obtain ⟨finished⟩ := trailer.finished_of_credited complete credit
  exact ⟨.done mode empty finished⟩

#print axioms CompletedBody.begin_trailer
#print axioms Trailer.finished_of_credited
#print axioms Trailer.done_phase
end Zlib.Inflate.Proofs.WholeEpoch
