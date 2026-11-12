import ZlibF.Proof.«inflate.c.gzip-header-frame»

/-!
# inflate.c: the blocks one public call may change
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The blocks a public call may change besides caller regions: the stream,
the private state, the local `hbuf` and the attached gzip header record. -/
def CallChanged (c : Ctx) (r : ZStreamRef) (zs : Nat) (head : GzHeaderPtr) (b : Nat) : Prop :=
  StreamRoot r b ∨ b = zs ∨ c.hbuf = .ref (.blk b) 0 ∨ head = some (.tab b)

theorem CallChanged.of_view {c : Ctx} {r : ZStreamRef} {zs : Nat} {head : GzHeaderPtr} {b : Nat}
    (view : StreamRoot r b ∨ b = zs) : CallChanged c r zs head b := by
  rcases view with root | state
  · exact Or.inl root
  · exact Or.inr (Or.inl state)

end Zlib.Inflate.Proofs
