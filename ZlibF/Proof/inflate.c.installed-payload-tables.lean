import ZlibF.Proof.«inflate.c.default-origin-state»
import ZlibF.Spec.InflateDecodeTableStability

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

/-- Installed semantic tables resolve through their actual pointers on the
same heap. Fixed tables and dynamic arrays use this common interface. -/
def InstalledTables (h : Heap) (s : InflateState) (L D : List Nat) : Prop :=
  (∃ ref offset ca used, s.lencode = .ref ref offset ∧ Space.get h ref = some ca ∧
    Inv LENS ca offset s.lenbits.toNat used L ∧ StableQuery LENS ca offset s.lenbits.toNat) ∧
  (∃ ref offset ca used, s.distcode = .ref ref offset ∧ Space.get h ref = some ca ∧
    Inv DISTS ca offset s.distbits.toNat used D ∧ StableQuery DISTS ca offset s.distbits.toNat)

end Zlib.Inflate.Proofs.FunctionalEpoch
