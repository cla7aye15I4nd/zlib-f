import ZlibF.Proof.«inflate.c.local-fast-effect»
import ZlibF.Proof.«inflate.c.fast-view-exact-frame-bridge»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual output writes stop at the returned physical output cursor.
The interval starts at this body's incoming output cursor. -/
def FastExactOutput (before after : Heap) (r : ZStreamRef) (zs : Nat)
    (dest : BRef) (start : Nat) (result : Zlib.Inffast.L) : Prop :=
  ∃ finish, result.out = .ref dest finish ∧ start ≤ finish ∧
    BufferFrame before after (fun b => StreamRoot r b ∨ b = zs)
      [⟨.ref dest start, finish - start⟩]

end Zlib.Inflate.Local
