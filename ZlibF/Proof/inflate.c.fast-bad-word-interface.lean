import ZlibF.Proof.«inftrees.c.query-take-rejected-word»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees Zlib.Inffast.Proofs
set_option autoImplicit false

/-- A real BAD body consumes exactly the rejected word from credited held
and pulled bytes. Every undropped held bit remains an arbitrary future. -/
def BadWordResult (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (c : Zlib.Inffast.Ctx) (slow : IL) (fast : Zlib.Inffast.L) (bs dict history : List UInt8)
    (L D : List Nat) : Prop :=
  ∃ used word result after finalSlow i,
    used ≤ 7 ∧ used ≤ bs.length ∧ result.in_ = inputAdvance fast.in_ used ∧
    C.run (Zlib.Inffast.inflate_fast_body c fast) h = .ok (result, after) ∧
    after = badHeap h r zs z s i ∧ result.broke = true ∧ result.out = fast.out ∧
    FastInputPacket after finalSlow (bs.drop used) result ∧ DispatchBuffers after r finalSlow (bs.drop used) ∧
    DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD} ∧
    (∀ dest : BRef, (Space.get after dest : Option (Array UInt8)) = Space.get h dest) ∧
    natBits slow.bits.toNat slow.hold.toNat ++ bytesBits (bs.take used) =
      word ++ natBits finalSlow.bits.toNat finalSlow.hold.toNat ∧
    (∀ future : List Bool, Token.Rejected L D dict history (word ++ future))

end Zlib.Inflate.Proofs.FastArbitraryBody
