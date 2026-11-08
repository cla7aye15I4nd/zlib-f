import ZlibF.Proof.«inftrees.c.decode.invariant»
import ZlibF.Proof.«inftrees.c.decode.invariant-prefix»

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The real later constructor retains an earlier installed table's full shape
and independent meaning. Its successful new table has the same invariant
on that one returned heap. Refusals retain the earlier table too. The
earlier table is an internal input; its producer is the constructor theorem.
No later-constructor contract or pointwise frame is assumed. -/
theorem inflate_table_preserves_decode_invariant
    {h : Heap} {type : UInt32} {rl rw : WRef} {ol ow oc : Nat}
    {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h type rl ol codes rc oc bits rw ow)
    (kind : type = LENS ∨ type = DISTS)
    {priorType : UInt32} {offset root used : Nat} {lens : List Nat}
    (prior : DecodeTableInvariant.Inv priorType pre.ca offset root used lens)
    (ordered : offset + used ≤ oc) :
    ∃ r after ca,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca
        (.ref rc oc) bits r after ∧
      Space.get after rc = some ca ∧
      DecodeTableInvariant.Inv priorType ca offset root used lens ∧
      (r.1 = 0 → ∃ newUsed,
        r.2.1 = .ref rc (oc + newUsed) ∧ newUsed ≤ capOf type ∧
        DecodeTableInvariant.Inv type ca oc r.2.2.toNat newUsed
          (lensOf pre.f codes.toNat)) := by
  obtain ⟨result, after, run, frame, built⟩ :=
    constructor_establishes_decode_table_invariant h type rl ol codes rc oc bits rw ow pre kind
  have originalFrame := frame
  obtain ⟨wa, ca, heap, _workSize, codeSize, _workFrame, codeFrame, _returned⟩ := frame
  have get : Space.get after rc = some ca := by
    rw [heap]
    apply cget_put_self (a0 := pre.ca)
    · rw [cget_put_word]
      exact pre.hgc
    · cases rc <;> exact pre.hro
  have retained : DecodeTableInvariant.Inv priorType ca offset root used lens := by
    apply decode_table_invariant_of_prefix priorType pre.ca ca offset root used lens prior
    · exact Nat.le_of_eq codeSize.symm
    · intro i _lower upper
      exact codeFrame i (Or.inl (by omega))
  refine ⟨result, after, ca, run, originalFrame, get, retained, ?_⟩
  intro success
  obtain ⟨newArray, newUsed, newGet, pointer, capacity, invariant⟩ := built success
  have arrays : ca = newArray := Option.some.inj (get.symm.trans newGet)
  subst newArray
  exact ⟨newUsed, pointer, capacity, invariant⟩

#print axioms inflate_table_preserves_decode_invariant
end Zlib.Inftrees.Proofs
