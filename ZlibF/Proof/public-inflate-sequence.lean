import ZlibF.Proof.«inflate.c.format-trace»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `inflate` over every public history: safety of the next call and of
`inflateEnd`, acceptance, valid-prefix behaviour and completion. -/
theorem inflate_sequence_public : ZlibF.Spec.Public.Goal.inflate_sequence :=
  ⟨inflate_sequence_safety, inflate_sequence_format, inflate_completes_proof⟩

end Zlib.Inflate.Proofs
