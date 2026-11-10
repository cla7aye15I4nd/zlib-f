import ZlibF.Proof.«inftrees.c.default-budget»
import ZlibF.Proof.«inftrees.c.decode.install»
import ZlibF.Proof.«inftrees.c.decode.stability»
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»

namespace Zlib.Inftrees.Proofs.DefaultStability
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

/-- The same real default payload constructor that establishes Inv also
establishes suffix stability, including invalid and reserved table cells. -/
theorem default_payload_installed_stable
    {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32} {rc : CodeRef} {oc : Nat}
    {bits : UInt32} {rw : WRef} {ow : Nat} (pre : CallPre h type rl ol codes rc oc bits rw ow)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ bits = 9) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ bits = 6))
    (valid : Acceptable (kindOf type) (lensList pre.la ol codes.toNat)) :
    ∃ result after, C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧ result.1 = 0 ∧
      ∃ (ca : Array Code) (used : Nat), Space.get after rc = some ca ∧ result.2.1 = .ref rc (oc + used) ∧
        used ≤ capOf type ∧ DecodeTableInvariant.Inv type ca oc result.2.2.toNat used (lensOf pre.f codes.toNat) ∧
        StableQuery type ca oc result.2.2.toNat := by
  obtain ⟨result, after, run, frame, zero, ca, used, get, pointer, capacity, inv⟩ :=
    BudgetExecution.inflate_table_default_payload_installed pre defaults valid
  have kind : type = LENS ∨ type = DISTS := defaults.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  obtain ⟨other, otherHeap, otherRun, stable⟩ :=
    constructor_establishes_query_stability h type rl ol codes rc oc bits rw ow pre kind
  rw [run] at otherRun
  cases otherRun
  exact ⟨result, after, run, frame, zero, ca, used, get, pointer, capacity, inv, stable zero ca get⟩

/-- A real later constructor preserves both the earlier invariant and
its suffix stability through its actual pointwise write frame. The new
table gets the same two properties when that constructor succeeds. -/
theorem constructor_preserves_installed_stable
    {h : Heap} {type : UInt32} {rl rw : WRef} {ol ow oc : Nat}
    {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h type rl ol codes rc oc bits rw ow) (kind : type = LENS ∨ type = DISTS)
    {priorType : UInt32} {offset root used : Nat} {lens : List Nat}
    (prior : DecodeTableInvariant.Inv priorType pre.ca offset root used lens)
    (priorStable : StableQuery priorType pre.ca offset root) (ordered : offset + used ≤ oc) :
    ∃ result after ca, C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      Space.get after rc = some ca ∧ DecodeTableInvariant.Inv priorType ca offset root used lens ∧
      StableQuery priorType ca offset root ∧
      (result.1 = 0 → ∃ newUsed, result.2.1 = .ref rc (oc + newUsed) ∧ newUsed ≤ capOf type ∧
        DecodeTableInvariant.Inv type ca oc result.2.2.toNat newUsed (lensOf pre.f codes.toNat) ∧
        StableQuery type ca oc result.2.2.toNat) := by
  obtain ⟨result, after, ca, run, frame, get, retained, built⟩ :=
    inflate_table_preserves_decode_invariant pre kind prior ordered
  obtain ⟨other, otherHeap, otherRun, stable⟩ :=
    constructor_establishes_query_stability h type rl ol codes rc oc bits rw ow pre kind
  rw [run] at otherRun
  cases otherRun
  have originalFrame := frame
  obtain ⟨wa, actual, heap, _workSize, _codeSize, _workFrame, codeFrame, _returned⟩ := frame
  have actualGet : Space.get after rc = some actual := by
    rw [heap]
    apply cget_put_self (a0 := pre.ca)
    · rw [cget_put_word]
      exact pre.hgc
    · cases rc <;> exact pre.hro
  have equal : actual = ca := Option.some.inj (actualGet.symm.trans get)
  subst actual
  have retainedStable : StableQuery priorType ca offset root := by
    apply query_stability_of_prefix priorType pre.ca ca offset root used prior.tableType prior.readExtent priorStable
    intro i _lower upper
    exact codeFrame i (Or.inl (by omega))
  refine ⟨result, after, ca, run, originalFrame, get, retained, retainedStable, ?_⟩
  intro zero
  obtain ⟨newUsed, pointer, capacity, inv⟩ := built zero
  exact ⟨newUsed, pointer, capacity, inv, stable zero ca get⟩

/-- Default payload parameters and independent alphabet validity remove
all constructor-success premises from the actual installation/frame result.
In particular a DISTS call retains an earlier LENS StableQuery. -/
theorem default_payload_preserves_installed_stable
    {h : Heap} {type : UInt32} {rl rw : WRef} {ol ow oc : Nat}
    {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h type rl ol codes rc oc bits rw ow)
    (defaults : (type = LENS ∧ codes.toNat ≤ 286 ∧ bits = 9) ∨
      (type = DISTS ∧ codes.toNat ≤ 30 ∧ bits = 6))
    (valid : Acceptable (kindOf type) (lensList pre.la ol codes.toNat))
    {priorType : UInt32} {offset root used : Nat} {lens : List Nat}
    (prior : DecodeTableInvariant.Inv priorType pre.ca offset root used lens)
    (priorStable : StableQuery priorType pre.ca offset root) (ordered : offset + used ≤ oc) :
    ∃ result after ca newUsed, C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧ result.1 = 0 ∧
      Space.get after rc = some ca ∧ result.2.1 = .ref rc (oc + newUsed) ∧ newUsed ≤ capOf type ∧
      DecodeTableInvariant.Inv priorType ca offset root used lens ∧ StableQuery priorType ca offset root ∧
      DecodeTableInvariant.Inv type ca oc result.2.2.toNat newUsed (lensOf pre.f codes.toNat) ∧
      StableQuery type ca oc result.2.2.toNat := by
  have kind : type = LENS ∨ type = DISTS := defaults.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  obtain ⟨result, after, ca, run, frame, get, retained, retainedStable, installed⟩ :=
    constructor_preserves_installed_stable pre kind prior priorStable ordered
  obtain ⟨other, otherHeap, otherRun, _, zero⟩ :=
    BudgetExecution.inflate_table_default_payload_success pre defaults valid
  rw [run] at otherRun
  cases otherRun
  obtain ⟨newUsed, pointer, capacity, inv, stable⟩ := installed zero
  exact ⟨result, after, ca, newUsed, run, frame, zero, get, pointer, capacity, retained, retainedStable, inv, stable⟩

#print axioms default_payload_installed_stable
#print axioms constructor_preserves_installed_stable
#print axioms default_payload_preserves_installed_stable
end Zlib.Inftrees.Proofs.DefaultStability
