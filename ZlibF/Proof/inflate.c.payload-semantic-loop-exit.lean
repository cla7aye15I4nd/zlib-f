import ZlibF.Proof.«inflate.c.payload-semantic-loop-ready»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The last real body leaves a synchronized token witness. For a normal
exit the independent block parser remains available; for EOB it reached
the specified target and tail. -/
def FastSemanticExit (ctx : FastLoopContext)
    (L D : List Nat) (dict : List UInt8)
    (tail : List Bool) (target : List UInt8)
    (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  FastLoopExit ctx h q ∧
    ∃ (slow : IL) (bs : List UInt8) (array : Array UInt8)
      (k made : Nat) (next : List UInt8) (done : Bool)
      (input : List Bool) (history : List UInt8),
      FastInputPacket h slow bs q ∧
      Space.get h ctx.dest = some array ∧
      Token.Step L D dict history input (stream slow bs) next done ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (k + made) ((k - ctx.bg) + made) = next ∧
      (done = false →
        q.out = .ref ctx.dest (k + made) ∧
        Symbols L D dict next (stream slow bs) tail target) ∧
      (done = true →
        stream slow bs = tail ∧ next = target ∧ q.broke = true)

end Zlib.Inflate.Proofs
