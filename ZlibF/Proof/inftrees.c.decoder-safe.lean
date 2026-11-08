import ZlibF.Proof.«inftrees.c.content.data»
import ZlibF.Proof.«inftrees.c.content.result»

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Canon Zlib.Inffast.Spec
set_option autoImplicit false

theorem lenLeaf_not_link {drop : Nat} {entry : Code} (leaf : LenLeaf drop entry) :
    ¬ LenLink entry := by
  rintro ⟨nonzero, bit16, bit64⟩
  rcases leaf.2 with literal | length | invalid
  · exact nonzero literal
  · exact length.1 bit16
  · exact invalid.2 bit64

theorem distLeaf_not_link {drop : Nat} {entry : Code} (leaf : DistLeaf drop entry) :
    ¬ DistLink entry := by
  rintro ⟨bit16, bit64⟩
  rcases leaf.2 with distance | invalid
  · exact distance.1 bit16
  · exact invalid.2 bit64

private theorem two_cell_table {P : Nat → Code → Prop} {L : Code → Prop}
    [DecidablePred L] {ca : Array Code} {offset : Nat} {first second : Code}
    (one : ca[offset]? = some first) (two : ca[offset + 1]? = some second)
    (firstLeaf : P 0 first) (firstNotLink : ¬ L first)
    (secondLeaf : P 0 second) (secondNotLink : ¬ L second) :
    TableSafe P L ca offset 1 := by
  have bound : offset + 1 < ca.size := by
    by_cases inside : offset + 1 < ca.size
    · exact inside
    · rw [Array.getElem?_eq_none (by omega)] at two
      contradiction
  refine ⟨by decide, by change offset + 2 ≤ ca.size; omega, ?_⟩
  intro cell inside
  have cases : cell = 0 ∨ cell = 1 := by change cell < 2 at inside; omega
  rcases cases with rfl | rfl
  · simp only [Nat.add_zero, Array.getD_eq_getD_getElem?, one, Option.getD_some,
      firstNotLink, ite_false]
    exact firstLeaf
  · simp only [Array.getD_eq_getD_getElem?, two, Option.getD_some, secondNotLink, ite_false]
    exact secondLeaf

theorem invalid_two_cells {ca : Array Code} {offset : Nat}
    (one : ca[offset]? = some ⟨64, 1, 0⟩) (two : ca[offset + 1]? = some ⟨64, 1, 0⟩) :
    LenTableSafe ca offset 1 ∧ DistTableSafe ca offset 1 := by
  have leaves := Cover.invalid_leaf 0 1 (by decide)
  exact ⟨two_cell_table one two leaves.1 (lenLeaf_not_link leaves.1)
      leaves.1 (lenLeaf_not_link leaves.1),
    two_cell_table one two leaves.2 (distLeaf_not_link leaves.2)
      leaves.2 (distLeaf_not_link leaves.2)⟩

theorem singleton_data_tables {e : Env} {ca : Array Code}
    (single : e.m = 1) (one : e.mx = 1) (written : Written e e.m ca)
    (invalid : ca[e.oc + 1]? = some ⟨64, 1, 0⟩) :
    (e.c.type = LENS → LenTableSafe ca e.oc e.R) ∧
    (e.c.type = DISTS → DistTableSafe ca e.oc e.R) := by
  have root : e.R = 1 := by
    have := e.h_R1
    have := e.h_Rmx
    have one' : mxl e.f e.n = 1 := one
    omega
  have len : Canon.L e.ls 0 = 1 := by
    rw [show Canon.L e.ls 0 = lenAt e.f e.n 0 from L_eq e.f e.n e.h_pos]
    have last : e.mx = lenAt e.f e.n 0 := by
      change lenAt e.f e.n (e.m - 1) = lenAt e.f e.n 0
      rw [single]
    exact last.symm.trans one
  have drop : (e.D 0).drop = 0 := rfl
  have replicas : 0 < gReps e.ls e.R e.mx 0 := Nat.two_pow_pos _
  have first := written 0 (by omega) 0 replicas
  rw [gaddr0 e single root replicas, Nat.add_zero] at first
  have leaf := here_data_leaf_of_drop (e := e) (j := 0) (by omega)
    (by rw [drop]; omega) (by omega)
  have invalidLeaf := Cover.invalid_leaf 0 1 (by decide)
  constructor
  · intro type
    have firstLeaf : LenLeaf 0 (e.here 0) := by simpa only [drop] using leaf.1 type
    rw [root]
    exact two_cell_table first invalid firstLeaf (lenLeaf_not_link firstLeaf)
      invalidLeaf.1 (lenLeaf_not_link invalidLeaf.1)
  · intro type
    have firstLeaf : DistLeaf 0 (e.here 0) := by simpa only [drop] using leaf.2 type
    rw [root]
    exact two_cell_table first invalid firstLeaf (distLeaf_not_link firstLeaf)
      invalidLeaf.2 (distLeaf_not_link invalidLeaf.2)

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The existing decoder-safety goal, including rejected alphabets, capacity
errors, empty tables and incomplete single-symbol tables. Every table
property comes from actual writes on the same execution. -/
theorem inflate_table_decoder_safe : Goal.inflate_table_decoder_safe := by
  intro h type rl ol codes rc oc bits rw ow pre
  by_cases codeLength : type = CODES
  · subst type
    obtain ⟨result, after, run, frame, safe⟩ := inflate_table_codes_decoder_safe pre
    refine ⟨result, after, run, frame, ?_⟩
    intro success
    obtain ⟨ca, get, table⟩ := safe success
    refine ⟨ca, get, table.1, by have := table.2.1; omega, fun _ => table, ?_, ?_⟩
    · intro impossible; cases impossible
    · intro impossible; cases impossible
  · obtain ⟨result, after, run, frame, _, construction⟩ :=
      inflate_table_construction h type rl ol codes rc oc bits rw ow pre
    refine ⟨result, after, run, frame, ?_⟩
    intro success
    rcases construction success with ⟨_, root, _, ca, get, first, second⟩ |
      ⟨_, e, ca, function, count, width, reference, offset, kind, get, written, links, details⟩
    · have tables := invalid_two_cells first second
      refine ⟨ca, get, ?_, ?_, ?_, ?_, ?_⟩
      · rw [root]; decide
      · rw [root]; decide
      · intro impossible; exact False.elim (codeLength impossible)
      · intro _; rw [root]; exact tables.1
      · intro _; rw [root]; exact tables.2
    · have rootLo : 1 ≤ result.2.2.toNat := by rw [← width]; exact e.h_R1
      have rootHi : result.2.2.toNat ≤ 15 := by
        rw [← width]
        have bound := lenAt_bounds (f := e.f) (n := e.n)
          (show Tc e.f e.n 15 - 1 < Tc e.f e.n 15 by have := e.h_pos; omega)
        have := e.h_Rmx
        exact Nat.le_trans this bound.2
      refine ⟨ca, get, rootLo, rootHi, ?_, ?_, ?_⟩
      · intro impossible; exact False.elim (codeLength impossible)
      all_goals
        intro typeEq
        rw [← offset, ← width]
        rcases e.h_end with complete | ⟨one, single, _⟩
        · first
          | exact complete_len_table_of_content (kind.trans typeEq) complete written links
          | exact complete_dist_table_of_content (kind.trans typeEq) complete written links
        · obtain ⟨_, _, _, invalid⟩ := details success
          have tables := singleton_data_tables single one written (invalid single one)
          first
          | exact tables.1 (kind.trans typeEq)
          | exact tables.2 (kind.trans typeEq)

end Zlib.Inftrees.Proofs
