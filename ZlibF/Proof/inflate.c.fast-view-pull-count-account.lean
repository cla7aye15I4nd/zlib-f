import ZlibF.Proof.«inflate.c.fast-view-body-input-bridge»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- A stream trace identifies the source-level byte count once the actual
run supplies its input-bit ledger. This uses lengths, so repeated byte values
cannot make two different input positions appear equal. -/
theorem stream_pull_count_eq
    {start finish : IL} {bs : List UInt8}
    {used consumed pulled : Nat}
    (usedBound : used ≤ bs.length)
    (pulledBound : pulled ≤ bs.length)
    (trace : stream finish (bs.drop used) =
      (stream start bs).drop consumed)
    (budget : finish.bits.toNat + consumed =
      start.bits.toNat + 8 * pulled) :
    used = pulled := by
  have consumedBound : consumed ≤ (stream start bs).length := by
    simp only [stream, List.length_append, natBits_length,
      bytesBits_length]
    omega
  have lengths := congrArg List.length trace
  simp only [stream, List.length_append, natBits_length,
    bytesBits_length, List.length_drop] at lengths
  omega

#print axioms stream_pull_count_eq
end Zlib.Inflate.Proofs
