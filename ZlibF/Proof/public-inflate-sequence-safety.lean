import ZlibF.Proof.«inflate.c.sequence-safety»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Safety of every permitted inflate call sequence: the invariant on every
reachable history, a safe next call with an exact allocation ledger, and an
`inflateEnd` that frees everything the stream owns. -/
theorem inflate_sequence_safety_public : ZlibF.Spec.Public.Goal.inflate_sequence_safety :=
  inflate_sequence_safety

#print axioms inflate_sequence_safety_public
end Zlib.Inflate.Proofs
