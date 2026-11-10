import ZlibF.Proof.«inflate.c.payload-link-meaning-cursor-stage-relinked»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false

/-- The shape-checked length-table link is exactly the code branch read by
the independent table query. This is a finite fact about the code op field. -/
theorem payload_len_table_link_query
    {codes : Array Code} {baseOff rootWidth idx : Nat}
    (safe : LenTableSafe codes baseOff rootWidth)
    (idxBound : idx < 2 ^ rootWidth) :
    let entry := codes.getD (baseOff + idx) default
    LenLink entry ↔ IsLink LENS entry = true := by
  let entry := codes.getD (baseOff + idx) default
  constructor
  · intro link
    have linkOK := safe.2.2 idx idxBound
    rw [ite_eq_left link] at linkOK
    have smallMask : ∀ op : UInt8,
        op.toNat ≤ 15 → op &&& 0xf0 = 0 := by
      apply Zlib.Inffast.Proofs.u8_forall
      decide +kernel
    have opMask : entry.op &&& 0xf0 = 0 :=
      smallMask entry.op linkOK.2.2.1
    simp [IsLink]
    exact ⟨by simpa only [entry, Array.getD_eq_getD_getElem?] using link.1,
      by simpa only [entry, Array.getD_eq_getD_getElem?] using opMask⟩
  · intro query
    have pure : ∀ op : UInt8,
        (op != 0 && (op &&& 0xf0) == 0) = true →
        op ≠ 0 ∧ op &&& 16 = 0 ∧ op &&& 64 = 0 := by
      apply Zlib.Inffast.Proofs.u8_forall
      decide +kernel
    exact pure entry.op (by simpa [IsLink, entry] using query)

#print axioms payload_len_table_link_query
end Zlib.Inflate.Proofs
