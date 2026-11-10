import ZlibF.Proof.«inftrees.c»
import ZlibF.Proof.«inftrees.c.decode.frame»

/-!
# inftrees.c: a later constructor preserves an earlier decoder table

The root and all reachable subtable cells belong to the earlier returned
extent. The actual later constructor's existing write frame therefore
preserves both table safety and the exact lookup, including failed queries.
-/

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inffast.Spec
set_option autoImplicit false

private theorem getD_eq_of_prefix {before after : Array Code} {offset used i : Nat}
    (cells : ∀ j, offset ≤ j → j < offset + used → after[j]? = before[j]?)
    (lo : offset ≤ i) (hi : i < offset + used) :
    after.getD i default = before.getD i default := by
  simp only [Array.getD_eq_getD_getElem?]
  rw [cells i lo hi]

/-- Table safety depends only on root cells and cells reached by links.
Other cells of the shared code array may change arbitrarily. -/
theorem tableSafe_of_prefix {P : Nat → Code → Prop} {L : Code → Prop}
    [DecidablePred L] {before after : Array Code} {offset root used : Nat}
    (safe : TableSafe P L before offset root) (size : after.size = before.size)
    (rootEnd : offset + 2 ^ root ≤ offset + used)
    (linkEnd : ∀ i, i < 2 ^ root → L (before.getD (offset + i) default) →
      offset + (before.getD (offset + i) default).val.toNat +
        2 ^ (before.getD (offset + i) default).op.toNat ≤ offset + used)
    (cells : ∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) :
    TableSafe P L after offset root := by
  refine ⟨safe.1, by rw [size]; exact safe.2.1, ?_⟩
  intro i hi
  have same := getD_eq_of_prefix cells (by omega : offset ≤ offset + i)
    (by omega : offset + i < offset + used)
  rw [same]
  have entry := safe.2.2 i hi
  by_cases link : L (before.getD (offset + i) default)
  · simp only [link, ite_true] at entry ⊢
    obtain ⟨bits, opLo, opHi, bound, leaves⟩ := entry
    refine ⟨bits, opLo, opHi, by rw [size]; exact bound, ?_⟩
    intro j hj
    have endBound := linkEnd i hi link
    rw [getD_eq_of_prefix cells (by omega) (by omega)]
    exact leaves j hj
  · simpa only [link, ite_false] using entry

/-- Preserve the exact read extent along with its root entries. -/
theorem tableReadExtent_of_prefix {type : UInt32} {before after : Array Code}
    {offset root used : Nat} (extent : TableReadExtent type before offset root used)
    (cells : ∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) :
    TableReadExtent type after offset root used := by
  refine ⟨extent.1, extent.2.1, extent.2.2.1, ?_⟩
  intro i hi
  rw [getD_eq_of_prefix cells (by omega) (by have := extent.2.2.1; omega)]
  exact extent.2.2.2 i hi

/-- Derive preservation of the length-table safety predicate from the
returned extent, rather than from the unused capacity of the whole array. -/
theorem lenTableSafe_of_prefix {before after : Array Code} {offset root used : Nat}
    (safe : LenTableSafe before offset root) (size : after.size = before.size)
    (extent : TableReadExtent LENS before offset root used)
    (cells : ∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) :
    LenTableSafe after offset root := by
  apply tableSafe_of_prefix safe size extent.2.2.1 ?_ cells
  intro i hi link
  exact extent.2.2.2 i hi (Or.inl ⟨rfl, link⟩)

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The actual distance-table call preserves a previously established length
table whose returned extent ends before this call's start. All returning
constructor outcomes are included. No distance-constructor contract or
table property is assumed: execution and the write frame come from the
existing proved translated constructor. The earlier table's safety and
extent remain inputs until its producer theorem is completed. -/
theorem inflate_table_dists_preserves_lens
    {h : Heap} {rl rw : WRef} {ol ow oc : Nat} {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h DISTS rl ol codes rc oc bits rw ow)
    {offset root used : Nat} (ordered : offset + used ≤ oc)
    (safe : LenTableSafe pre.ca offset root)
    (extent : TableReadExtent LENS pre.ca offset root used) :
    ∃ r after ca,
      C.run (inflate_table DISTS (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h = .ok (r, after) ∧
      Result h rw rc ow oc (capOf DISTS) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      Space.get after rc = some ca ∧ LenTableSafe ca offset root ∧
      TableReadExtent LENS ca offset root used ∧
      ∀ inp, DecodeSemantics.tableRead LENS ca offset root inp =
        DecodeSemantics.tableRead LENS pre.ca offset root inp := by
  obtain ⟨r, after, run, result, _⟩ := itTop_wp pre
  have actual : C.run (inflate_table DISTS (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
      .ok (r, after) := by
    rw [C.run, inflate_table_eq]
    exact run
  have retained := result
  obtain ⟨wa, ca, heap, _, size, _, frame, _⟩ := result
  have cells : ∀ i, offset ≤ i → i < offset + used → ca[i]? = pre.ca[i]? := by
    intro i _ hi
    exact frame i (Or.inl (by omega))
  have get : Space.get after rc = some ca := by
    rw [heap]
    apply cget_put_self (a0 := pre.ca)
    · rw [cget_put_word]
      exact pre.hgc
    · cases rc <;> exact pre.hro
  exact ⟨r, after, ca, actual, retained, get,
    lenTableSafe_of_prefix safe size extent cells,
    tableReadExtent_of_prefix extent cells,
    decode_table_read_preserved LENS pre.ca ca offset root used
      (Or.inl rfl) extent cells⟩

end Zlib.Inftrees.Proofs
