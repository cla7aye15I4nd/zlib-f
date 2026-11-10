import ZlibF.Proof.«inftrees.c.decode.stability»

set_option autoImplicit false
namespace Zlib.Inftrees.Proofs.QueryTakeSource
open C Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics

/-- An actual fitted query depends only on its consumed prefix, including
reserved symbols and invalid empty/singleton padding. -/
def QueryTake (type : UInt32) (ca : Array Code) (offset root : Nat) : Prop :=
  ∀ (inp : List Bool) (entry : Code) (consumed : Nat),
    tableRead type ca offset root (DecodeShort.padded inp) = some (entry, consumed) →
    consumed ≤ inp.length →
    tableRead type ca offset root (DecodeShort.padded (inp.take consumed)) = some (entry, consumed)


end Zlib.Inftrees.Proofs.QueryTakeSource
