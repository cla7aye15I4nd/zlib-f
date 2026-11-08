import ZlibF.Spec.InflateFastTableFlags
import ZlibF.Spec.InflateSubtable

set_option autoImplicit false
namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.FastTableFlags Zlib.Inftrees.Spec.DecodeSemantics

def fixedFlagsCheck (type : UInt32) (entry : Code) : Bool :=
  (((entry.op &&& 16) == 0) || ((entry.op &&& 64) == 0)) &&
    !(Subtable.IsLink type entry)

theorem fixedFlagsCheck_sound {type : UInt32} {entry : Code}
    (check : fixedFlagsCheck type entry = true) :
    Compatible entry ∧ Subtable.IsLink type entry = false := by
  simp only [fixedFlagsCheck, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq] at check
  refine ⟨?_, ?_⟩
  · intro length
    rcases check.1 with noLength | noInvalid
    · exact False.elim (length noLength)
    · exact noInvalid
  · cases link : Subtable.IsLink type entry <;> simp_all

set_option maxRecDepth 10000 in
theorem distfix_all_flags : Zlib.InffixedH.distfix.all (fixedFlagsCheck DISTS) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem lenfix_all_flags : Zlib.InffixedH.lenfix.all (fixedFlagsCheck LENS) = true := by
  decide +kernel

/-- Actual root cells suffice; failed or short queries impose no obligation. -/
theorem all_root_flags_query_compatible {type : UInt32} {ca : Array Code} {offset root : Nat}
    (allFlags : ca.all (fixedFlagsCheck type) = true) :
    QueryCompatible type ca offset root := by
  intro inp entry consumed _enough query
  unfold tableRead at query
  cases read : readBits root inp with
  | none => simp only [read, bind, Option.bind] at query; contradiction
  | some pair =>
      obtain ⟨i, rest⟩ := pair
      simp only [read, bind, Option.bind] at query
      cases get : ca[offset + i]? with
      | none => simp only [get, Option.bind] at query; contradiction
      | some actual =>
          have check := (Array.all_eq_true_iff_forall_mem.mp allFlags) actual (Array.mem_of_getElem? get)
          obtain ⟨compatible, leaf⟩ := fixedFlagsCheck_sound check
          unfold Subtable.IsLink at leaf
          simp only [get, Option.bind, leaf, Bool.false_eq_true, ite_false] at query
          have equal : actual = entry := congrArg Prod.fst (Option.some.inj query)
          subst actual
          exact compatible

theorem fixed_tables_have_fast_leaf_flags : FastTableFlags.Goal.fixed_tables_have_fast_leaf_flags := by
  exact ⟨all_root_flags_query_compatible lenfix_all_flags,
    all_root_flags_query_compatible distfix_all_flags⟩

#print axioms distfix_all_flags
#print axioms lenfix_all_flags
#print axioms fixed_tables_have_fast_leaf_flags
end Zlib.Inftrees.Proofs
