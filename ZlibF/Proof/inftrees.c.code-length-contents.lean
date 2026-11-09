import ZlibF.Proof.«inftrees.c.code-length-meaning-state»

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Canon ZlibF.Spec
set_option autoImplicit false

/-- A nonempty accepted CODES construction covers the entire flat root
with actual canonical leaves. No invalid opcode remains in this case. -/
theorem Env.code_length_root_cells {e : Env} {ca : Array Code}
    (kind : e.c.type = CODES) (written : Written e e.m ca) :
    ∀ index, index < 2 ^ e.R → ∃ entry, ca[e.oc + index]? = some entry ∧ entry.op = 0 := by
  obtain ⟨maximum, root, _count, _match⟩ := e.h_codes kind
  have rootBound : e.R ≤ 15 := by rw [root]; omega
  have complete : Kc e.f e.n 15 = 2 ^ 15 := by
    rcases e.h_end with full | ⟨_, _, notCodes⟩
    · exact full
    · exact False.elim (notCodes kind)
  intro cell inside
  rcases Cover.root_cover_complete_fn e.h_fits complete rootBound inside with
    ⟨j, short, _, _⟩ | ⟨⟨j, long⟩, _⟩
  · have shortList := (Cover.shortAt_iff e.f e.n e.R cell j).mpr short
    have leaf := e.code_length_root_word kind written short.1 inside shortList.2.2
    exact ⟨e.here j, leaf.1, leaf.2.1⟩
  · have index := long.1
    have upper : lenAt e.f e.n j ≤ e.R := by
      rw [root]
      exact lenAt_mono (f := e.f) (n := e.n) (by omega) (by have := e.h_pos; omega)
    exact False.elim (by have := long.2.1; omega)

/-- The source also fixes the contents of its exceptional empty table.
clRead uses val directly, so retaining only the invalid opcode would lose
information needed for malformed-input semantics. Empty is not an automatic
refusal: the actual constructor returns two zero-valued invalid cells. -/
structure CodeLengthContents (ca : Array Code) (offset root : Nat) (alphabet : List Nat)
    : Prop extends CodeLengthMeaning ca offset root alphabet where
  layout :
    (root = 1 ∧ (∀ length ∈ alphabet, length = 0) ∧
      ca[offset]? = some (⟨64, 1, 0⟩ : Code) ∧ ca[offset + 1]? = some (⟨64, 1, 0⟩ : Code)) ∨
    (∀ index, index < 2 ^ root → ∃ entry, ca[offset + index]? = some entry ∧ entry.op = 0)

/-- An invalid actual root cell has the precise empty-table fields.
clRead may read its zero value; the opcode alone does not cause a refusal. -/
theorem CodeLengthContents.invalid_cell_fields {ca : Array Code} {offset root index : Nat}
    {alphabet : List Nat} {entry : Code} (contents : CodeLengthContents ca offset root alphabet)
    (inside : index < 2 ^ root) (get : ca[offset + index]? = some entry) (invalid : entry.op = 64) :
    root = 1 ∧ entry.bits = 1 ∧ entry.val = 0 ∧ (∀ length ∈ alphabet, length = 0) := by
  rcases contents.layout with empty | complete
  · obtain ⟨width, allZero, first, second⟩ := empty
    have bound : index < 2 := by rw [width] at inside; exact inside
    have cell : ca[offset + index]? = some (⟨64, 1, 0⟩ : Code) := by
      have alternatives : index = 0 ∨ index = 1 := by omega
      rcases alternatives with rfl | rfl
      · simpa only [Nat.add_zero] using first
      · exact second
    have same : entry = (⟨64, 1, 0⟩ : Code) := Option.some.inj (get.symm.trans cell)
    exact ⟨width, by rw [same], by rw [same], allZero⟩
  · obtain ⟨stored, cell, opcode⟩ := complete index inside
    have same : stored = entry := Option.some.inj (cell.symm.trans get)
    rw [same, invalid] at opcode
    exact False.elim ((by decide : (64 : UInt8) ≠ 0) opcode)

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)` for CODES.
The real call supplies both independent accepted-query meaning and the
complete exceptional/nonempty root-cell classification on its actual array. -/
theorem inflate_table_establishes_code_length_contents
    {h : Heap} {rl rw : WRef} {ol ow oc : Nat} {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h CODES rl ol codes rc oc bits rw ow) :
    ∃ result after,
      C.run (inflate_table CODES (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (result, after) ∧
      Result h rw rc ow oc (capOf CODES) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      (result.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        CodeLengthContents ca oc result.2.2.toNat (lensOf pre.f codes.toNat)) := by
  obtain ⟨result, after, run, frame, meaning⟩ := inflate_table_establishes_code_length_meaning pre
  obtain ⟨result2, after2, run2, _frame2, _ret, content⟩ :=
    inflate_table_content h CODES rl ol codes rc oc bits rw ow pre
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  refine ⟨result, after, run, frame, ?_⟩
  intro success
  obtain ⟨ca, get, semantic⟩ := meaning success
  refine ⟨ca, get, semantic, ?_⟩
  rcases content success with empty | built
  · obtain ⟨zero, root, _, array, arrayGet, first, second⟩ := empty
    have arrays : array = ca := Option.some.inj (arrayGet.symm.trans get)
    subst array
    exact Or.inl ⟨by rw [root]; rfl, (zero_iff pre.f codes.toNat pre.hf15).mpr zero, first, second⟩
  · obtain ⟨_positive, e, array, _function, _count, width, _reference, offset, kind,
      arrayGet, written, _links⟩ := built
    have arrays : array = ca := Option.some.inj (arrayGet.symm.trans get)
    subst array
    have cells := e.code_length_root_cells kind written
    rw [offset, width] at cells
    exact Or.inr cells

#print axioms CodeLengthContents.invalid_cell_fields
#print axioms Env.code_length_root_cells
#print axioms inflate_table_establishes_code_length_contents
end Zlib.Inftrees.Proofs
