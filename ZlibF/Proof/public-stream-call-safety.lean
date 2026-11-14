import ZlibF.Proof.«public-inflate-sequence-safety»
import ZlibF.Proof.«public-deflate-goals»
import ZlibF.Spec.Safety.Streams

/-!
# Per-function safety of the inflate and deflate functions

Each theorem proves one goal of `ZlibF/Spec/Safety/Streams.lean` as a corollary of the sequence
safety theorems `Zlib.Inflate.Proofs.inflate_sequence_safety_public` (clauses 2 and 3 of
`StreamSequenceSafety .inflate`) and `Zlib.Deflate.Universal.deflate_sequence_safety`.
-/

namespace ZlibF.Spec.Public.StreamCallSafetyProof
open C ZlibF.Spec ZlibF.Spec.Public

theorem inflate_safety : Goal.inflate_safety :=
  fun h r flush d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflateSetDictionary_safety : Goal.inflateSetDictionary_safety :=
  fun h r dictionary dictLength d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflateGetDictionary_safety : Goal.inflateGetDictionary_safety :=
  fun h r dictionary dictLength d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflateSync_safety : Goal.inflateSync_safety :=
  fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflateReset_safety : Goal.inflateReset_safety :=
  fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflateReset2_safety : Goal.inflateReset2_safety :=
  fun h r windowBits d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflatePrime_safety : Goal.inflatePrime_safety :=
  fun h r bits value d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflateMark_safety : Goal.inflateMark_safety :=
  fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflateGetHeader_safety : Goal.inflateGetHeader_safety :=
  fun h r head d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflate_safety : Goal.deflate_safety :=
  fun h r flush d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateSetDictionary_safety : Goal.deflateSetDictionary_safety :=
  fun h r dictionary dictLength d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateGetDictionary_safety : Goal.deflateGetDictionary_safety :=
  fun h r dictionary hasDictLength d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateReset_safety : Goal.deflateReset_safety :=
  fun h r d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateParams_safety : Goal.deflateParams_safety :=
  fun h r level strategy d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateTune_safety : Goal.deflateTune_safety :=
  fun h r good_length max_lazy nice_length max_chain d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateBound_safety : Goal.deflateBound_safety :=
  fun h r sourceLen d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateBound_z_safety : Goal.deflateBound_z_safety :=
  fun h r sourceLen d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflatePending_safety : Goal.deflatePending_safety :=
  fun h r hasPending hasBits d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateUsed_safety : Goal.deflateUsed_safety :=
  fun h r hasBits d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflatePrime_safety : Goal.deflatePrime_safety :=
  fun h r bits value d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem deflateSetHeader_safety : Goal.deflateSetHeader_safety :=
  fun h r head d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

theorem inflateEnd_safety : Goal.inflateEnd_safety := by
  intro h r hr
  obtain ⟨rc, after, z, hrun, hrc, hz, hs, hf, hl⟩ :=
    Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.2 h r hr
  refine ⟨rc, after, z, hrun, ?_, hz, hs, hf, hl⟩
  rcases hrc with hrc | ⟨hk, _⟩
  · exact hrc
  · cases hk

theorem deflateEnd_safety : Goal.deflateEnd_safety := by
  intro h r hr
  obtain ⟨rc, after, z, hrun, hrc, hz, hs, hf, hl⟩ :=
    Zlib.Deflate.Universal.deflate_sequence_safety.2.2 h r hr
  refine ⟨rc, after, z, hrun, ?_, hz, hs, hf, hl⟩
  rcases hrc with hrc | ⟨_, hrc⟩
  · exact Or.inl hrc
  · exact Or.inr hrc

end ZlibF.Spec.Public.StreamCallSafetyProof
