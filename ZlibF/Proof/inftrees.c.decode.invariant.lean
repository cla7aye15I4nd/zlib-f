import ZlibF.Proof.«inftrees.c.decode.bits»
import ZlibF.Proof.«inftrees.c.decode.short»
import ZlibF.Proof.«inftrees.c.read-extent»
import ZlibF.Spec.InflateDecodeTableInvariant

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec Zlib.Inffast.Spec

/-- The actual constructor establishes the installed table's shape,
read extent and independent decoding semantics in one invariant. -/
theorem constructor_establishes_decode_table_invariant :
    DecodeTableInvariant.Goal.constructor_establishes_decode_table_invariant := by
  intro h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨result, after, run, frame, ret, _construction⟩ :=
    inflate_table_construction h type rl ol codes rc oc bits rw ow pre
  obtain ⟨extentResult, extentAfter, extentRun, _extentFrame, extent⟩ :=
    inflate_table_read_extent h type rl ol codes rc oc bits rw ow pre
  obtain ⟨results, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans extentRun))
  subst extentResult extentAfter
  obtain ⟨shapeResult, shapeAfter, shapeRun, shape⟩ :=
    constructor_subtable_bits h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨results, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans shapeRun))
  subst shapeResult shapeAfter
  obtain ⟨shortResult, shortAfter, shortRun, short⟩ :=
    short_decode_table_leaf_sound h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨results, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans shortRun))
  subst shortResult shortAfter
  obtain ⟨classResult, classAfter, classRun, classify⟩ :=
    decode_table_classifies_input h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨results, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans classRun))
  subst classResult classAfter
  refine ⟨result, after, run, frame, ?_⟩
  intro success
  obtain ⟨ca, used, get, pointer, capacity, readExtent, _codeSafe, _lenSafe, _distSafe⟩ := extent success
  obtain ⟨shapeArray, shapeGet, rootSafe, subtableSafe⟩ := shape success
  have arrays : ca = shapeArray := Option.some.inj (get.symm.trans shapeGet)
  subst shapeArray
  have acceptable := (acc_iff type pre.f codes.toNat pre.hf15).mp (ret.1 success)
  refine ⟨ca, used, get, pointer, capacity, kind, rootSafe, subtableSafe,
    readExtent, acceptable, ?_, ?_⟩
  · intro inp entry consumed query fits accepted
    exact short success inp ca entry consumed get query fits accepted
  · intro inp enough
    obtain ⟨queryArray, entry, consumed, queryGet, query, classification⟩ := classify success inp enough
    have arrays : ca = queryArray := Option.some.inj (get.symm.trans queryGet)
    subst queryArray
    exact ⟨entry, consumed, query, classification⟩

#print axioms constructor_establishes_decode_table_invariant
end Zlib.Inftrees.Proofs
