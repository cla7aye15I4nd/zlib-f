import ZlibF.Proof.«inflate.c.global-payload-representation»
namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Discarding dictionary bytes older than the configured capacity before
appending prior output leaves the exact final retained history unchanged. -/
theorem retain_trimmed_dictionary (dict past : List UInt8) (capacity : Nat) :
    ((dict.drop (dict.length - capacity)) ++ past).drop
        (((dict.drop (dict.length - capacity)) ++ past).length - capacity) =
      (dict ++ past).drop ((dict ++ past).length - capacity) := by
  simp only [List.length_append, List.length_drop, List.drop_append, List.drop_drop]
  congr 1
  · congr 1
    omega
  · congr 1
    omega

/-- The actual default saved window can be represented with the configured
32KiB dictionary used by accepted-stream semantics. This changes no heap,
parser, output, public history or caller premise. -/
theorem PayloadRepresentation.trim_dictionary
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict past : List UInt8} {L D : List Nat}
    (before : PayloadRepresentation h r zs z s l bs L D (dict ++ past)) :
    PayloadRepresentation h r zs z s l bs L D (dict.drop (dict.length - 32768) ++ past) := by
  obtain ⟨origin, buffers, bits, tables, dictionary⟩ := before
  refine ⟨origin, buffers, bits, tables, ?_⟩
  rw [origin.toDefaultStateJ.window] at dictionary ⊢
  change InflateDictionary h s ((dict.drop (dict.length - 32768) ++ past).drop
    ((dict.drop (dict.length - 32768) ++ past).length - 32768))
  rw [retain_trimmed_dictionary]
  exact dictionary

end Zlib.Inflate.Proofs.FunctionalEpoch
