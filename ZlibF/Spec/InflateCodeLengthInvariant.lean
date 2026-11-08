import ZlibF.Spec.InflateTableSafety
import ZlibF.Proof.«inflate.c.base»

namespace Zlib.Inflate.Spec
open C

/-- The CODELENS boundary facts, before the next code length is read.
Only the initialized prefix is constrained. The unused lens entries remain
arbitrary. The table is the actual codes field of this state record. -/
def CodeLengthInvariant (state : Nat) (s : InflateState) : Prop :=
  s.mode = CODELENS →
    s.lencode = .ref (.istate_codes state) 0 ∧
    Zlib.Inftrees.Spec.CodeLengthTableSafe s.codes 0 s.lenbits.toNat ∧
    s.nlen.toNat ≤ 286 ∧ s.ndist.toNat ≤ 30 ∧
    s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat ∧
    ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15

end Zlib.Inflate.Spec
