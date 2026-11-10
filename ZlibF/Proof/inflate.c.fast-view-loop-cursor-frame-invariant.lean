import ZlibF.Proof.«inflate.c.fast-view-body-rank-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-entry-six-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A nonbreaking fast body preserves the fixed `last` geometry when its
packet consumes exactly the recorded number of caller bytes. -/
theorem FastInputPacket.fast_last_after_body
    {h after : Heap} {slow slowFinal : IL} {bs : List UInt8}
    {l result : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {used : Nat} {ref : BRef} {off : Nat}
    (before : FastInputPacket h slow bs l)
    (final : FastInputPacket after slowFinal (bs.drop used) result)
    (bound : used ≤ bs.length)
    (nextPtr : slow.next = .ref ref off)
    (lastPtr : c.last = .ref ref
      (off + slow.have_.toNat - 5))
    (cursor : slowFinal.next = inputAdvance slow.next used) :
    slowFinal.next = .ref ref (off + used) ∧
    slowFinal.have_.toNat + used = slow.have_.toNat ∧
    c.last = .ref ref
      (off + used + slowFinal.have_.toNat - 5) := by
  have count := before.have_after_drop final bound
  have next : slowFinal.next = .ref ref (off + used) := by
    rw [cursor, nextPtr]
    rfl
  have last := fast_last_after_advance lastPtr count
  exact ⟨next, count, last⟩

end Zlib.Inflate.Proofs
