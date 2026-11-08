import ZlibF.Proof.«inftrees.c.decode.stability»
import ZlibF.Spec.InflateSubtable

set_option autoImplicit false
namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Canon

private theorem cell_exists_bound {ca : Array Code} {i : Nat} {value : Code}
    (get : ca[i]? = some value) : i < ca.size := by
  by_cases inside : i < ca.size
  · exact inside
  · rw [Array.getElem?_eq_none (by omega)] at get
    contradiction

set_option maxHeartbeats 2000000 in
theorem Env.complete_table_bits {e : Env} {ca : Array Code}
    (complete : Kc e.f e.n 15 = 2 ^ 15)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (links : Links e e.m ca) :
    RootTable.Safe ca e.oc e.R ∧
    ∀ i entry, i < 2 ^ e.R → ca[e.oc + i]? = some entry →
      Subtable.IsLink e.c.type entry = true →
      entry.bits.toNat = e.R ∧ Subtable.Safe ca e.oc entry := by
  have code := e.completeCode complete
  have listIndex : ∀ j, j < e.m ↔ j < Canon.nz e.ls := by
    intro j
    rw [e.nz_eq]
  have rootEntries : ∀ cell, cell < 2 ^ e.R →
      ∃ value, ca[e.oc + cell]? = some value ∧
        1 ≤ value.bits.toNat ∧ value.bits.toNat ≤ e.R ∧
        (Subtable.IsLink e.c.type value = true →
          value.bits.toNat = e.R ∧ Subtable.Safe ca e.oc value) := by
    intro cell inside
    rcases Cover.root_cover_complete_fn e.h_fits complete
        (Nat.le_trans code.root_le code.mx_le) inside with
      ⟨j, short, _, _⟩ | ⟨⟨j, long⟩, _⟩
    · have shortList := (Cover.shortAt_iff e.f e.n e.R cell j).mpr short
      obtain ⟨replica, bound, address⟩ := short_root_replica (mx := e.mx)
        shortList.1 shortList.2.1 inside shortList.2.2
      have get := written j short.1 replica bound
      change gAddr e.ls e.R e.mx j replica = cell at address
      rw [address] at get
      have drop : (e.D j).drop = 0 := by
        change (Canon.desc e.ls e.R e.mx j).drop = 0
        rw [Canon.desc_short e.ls shortList.1 shortList.2.1]
        rfl
      have interval := Canon.L_interval e.ls shortList.1
      have bits : (e.here j).bits.toNat = Canon.L e.ls j := by
        rw [e.here_bits interval.2.1, drop, Nat.sub_zero]
      have leaf : Subtable.IsLink e.c.type (e.here j) = false :=
        e.here_not_query_link short.1 kind (by rw [drop]; omega) interval.2.1
      refine ⟨e.here j, get, ?_, ?_, ?_⟩
      · rw [bits]; exact interval.1
      · rw [bits]; exact shortList.2.1
      · intro flag; rw [leaf] at flag; contradiction
    · have longList := (Cover.longAt_iff e.f e.n e.R cell j).mpr long
      obtain ⟨a, order, start, group, _drop, _width, _⟩ :=
        desc_long (mx := e.mx) code.min_le longList.1 longList.2.1
      have jIndex : j < e.m := long.1
      have startIndex : a + 1 < e.m := by omega
      have aList : a + 1 < Canon.nz e.ls := (listIndex _).mp startIndex
      have aLong : e.R < Canon.L e.ls (a + 1) := start.1
      have get := links (a + 1) (by omega) (by omega) startIndex
        (by simpa only [Nat.add_sub_cancel] using start)
      have slot : gSlot e.ls e.R (a + 1) = cell := by
        unfold gSlot
        rw [group, ← Canon.H_mod_root e.ls (root := e.R) longList.1 (Nat.le_of_lt longList.2.1)]
        exact longList.2.2
      rw [slot] at get
      have info := width_spec e.ls aList code.mx_le aLong (code.L_le_mx aList)
      have op : ((Canon.width e.ls (a + 1) e.R e.mx).toUInt8).toNat =
          Canon.width e.ls (a + 1) e.R e.mx := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have := code.mx_le; omega)]
      have root : (e.R.toUInt8).toNat = e.R := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have := code.mx_le; have := code.root_le; omega)]
      have base : ((e.D (a + 1)).base.toUInt16).toNat = (e.D (a + 1)).base := by
        rw [UInt16.toNat_ofNat']
        exact Nat.mod_eq_of_lt (desc_base_lt_u16 code aList)
      have dc : (e.D (a + 1)).curr = Canon.width e.ls (a + 1) e.R e.mx := by
        change (desc e.ls e.R e.mx (a + 1)).curr = _
        rw [desc_succ_of_starts e.ls e.R e.mx a start]
      have localEntries : ∀ t, t < 2 ^ Canon.width e.ls (a + 1) e.R e.mx →
          ∃ value, ca[e.oc + (e.D (a + 1)).base + t]? = some value ∧
            1 ≤ value.bits.toNat ∧ value.bits.toNat ≤ Canon.width e.ls (a + 1) e.R e.mx := by
        intro t bounded
        obtain ⟨j', replica, member, same, repBound, address⟩ := long_subtable_replica
          code aList aLong (by change t < 2 ^ (e.D (a + 1)).curr; rw [dc]; exact bounded)
        have value := written j' ((listIndex _).mpr member) replica repBound
        rw [address, ← Nat.add_assoc] at value
        have drop : (e.D j').drop = e.R := by
          change (Canon.desc e.ls e.R e.mx j').drop = e.R
          rw [same, desc_succ_of_starts e.ls e.R e.mx a start]
        have longLeaf : e.R < Canon.L e.ls j' := by
          by_cases small : Canon.L e.ls j' ≤ e.R
          · have short := Canon.desc_short e.ls (mx := e.mx) member small
            have zero : (e.D j').drop = 0 := by rw [show e.D j' = _ from short]; rfl
            have positive := e.h_R1
            omega
          · omega
        have interval := Canon.L_interval e.ls member
        have fits := (Canon.desc_fits code member).2.1
        have curr : (e.D j').curr = Canon.width e.ls (a + 1) e.R e.mx := by
          change (Canon.desc e.ls e.R e.mx j').curr = _
          rw [same]; exact dc
        have bits := e.here_bits (j := j') interval.2.1
        rw [drop] at bits
        refine ⟨e.here j', value, ?_, ?_⟩
        · rw [bits]; omega
        · rw [bits]; change Canon.L e.ls j' - (e.D j').drop ≤ (e.D j').curr at fits
          rw [drop, curr] at fits
          exact fits
      refine ⟨e.link (a + 1), get, ?_, ?_, ?_⟩
      · change 1 ≤ (e.R.toUInt8).toNat; rw [root]; exact e.h_R1
      · change (e.R.toUInt8).toNat ≤ e.R; rw [root]
        exact Nat.le_refl _
      · intro _flag
        refine ⟨root, ?_⟩
        change 1 ≤ (e.R.toUInt8).toNat ∧ _
        dsimp only [Env.link]
        rw [root, op, base]
        have positive := Nat.two_pow_pos (Canon.width e.ls (a + 1) e.R e.mx)
        obtain ⟨last, lastGet, _, _⟩ := localEntries
          (2 ^ Canon.width e.ls (a + 1) e.R e.mx - 1) (by omega)
        have arrayBound := cell_exists_bound lastGet
        refine ⟨e.h_R1, by omega, by have := code.mx_le; omega, by omega, ?_⟩
        exact localEntries
  have positive := Nat.two_pow_pos e.R
  obtain ⟨last, lastGet, _⟩ := rootEntries (2 ^ e.R - 1) (by omega)
  have arrayBound := cell_exists_bound lastGet
  refine ⟨⟨e.h_R1, Nat.le_trans code.root_le code.mx_le, by omega, ?_⟩, ?_⟩
  · intro cell inside
    obtain ⟨value, get, low, high, _⟩ := rootEntries cell inside
    exact ⟨value, get, low, high⟩
  · intro cell entry inside get flag
    obtain ⟨value, actual, _, _, safe⟩ := rootEntries cell inside
    have equal := Option.some.inj (actual.symm.trans get)
    subst value
    exact safe flag


theorem two_leaf_table_bits {type : UInt32} {ca : Array Code} {offset : Nat}
    {first second : Code}
    (firstGet : ca[offset]? = some first) (secondGet : ca[offset + 1]? = some second)
    (firstBits : first.bits.toNat = 1) (secondBits : second.bits.toNat = 1)
    (firstLeaf : Subtable.IsLink type first = false)
    (secondLeaf : Subtable.IsLink type second = false) :
    RootTable.Safe ca offset 1 ∧
    ∀ i entry, i < 2 ^ 1 → ca[offset + i]? = some entry →
      Subtable.IsLink type entry = true →
      entry.bits.toNat = 1 ∧ Subtable.Safe ca offset entry := by
  have arrayBound := cell_exists_bound secondGet
  have entries : ∀ i, i < 2 ^ 1 →
      ∃ value, ca[offset + i]? = some value ∧
        value.bits.toNat = 1 ∧ Subtable.IsLink type value = false := by
    intro i inside
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    · exact ⟨first, by simpa only [Nat.add_zero] using firstGet, firstBits, firstLeaf⟩
    · exact ⟨second, secondGet, secondBits, secondLeaf⟩
  refine ⟨⟨by decide, by decide, by omega, ?_⟩, ?_⟩
  · intro i inside
    obtain ⟨value, get, bits, _⟩ := entries i inside
    exact ⟨value, get, by rw [bits]; exact Nat.le_refl _, by rw [bits]; exact Nat.le_refl _⟩
  · intro i entry inside get flag
    obtain ⟨value, actual, _, leaf⟩ := entries i inside
    have equal := Option.some.inj (actual.symm.trans get)
    subst value
    rw [leaf] at flag
    contradiction

theorem invalid_table_bits {type : UInt32} {ca : Array Code} {offset : Nat}
    (first : ca[offset]? = some ⟨64, 1, 0⟩)
    (second : ca[offset + 1]? = some ⟨64, 1, 0⟩) :
    RootTable.Safe ca offset 1 ∧
    ∀ i entry, i < 2 ^ 1 → ca[offset + i]? = some entry →
      Subtable.IsLink type entry = true →
      entry.bits.toNat = 1 ∧ Subtable.Safe ca offset entry := by
  have leaf : Subtable.IsLink type ⟨64, 1, 0⟩ = false := by
    unfold Subtable.IsLink
    split <;> decide
  exact two_leaf_table_bits first second rfl rfl leaf leaf

set_option maxHeartbeats 2000000 in
theorem Env.singleton_table_bits {e : Env} {ca : Array Code}
    (single : e.m = 1) (one : e.mx = 1)
    (kind : e.c.type = LENS ∨ e.c.type = DISTS)
    (written : Written e e.m ca) (invalid : ca[e.oc + 1]? = some ⟨64, 1, 0⟩) :
    RootTable.Safe ca e.oc e.R ∧
    ∀ i entry, i < 2 ^ e.R → ca[e.oc + i]? = some entry →
      Subtable.IsLink e.c.type entry = true →
      entry.bits.toNat = e.R ∧ Subtable.Safe ca e.oc entry := by
  have root : e.R = 1 := by
    have positive := e.h_R1
    have upper : e.R ≤ e.mx := e.h_Rmx
    omega
  have index : 0 < e.m := e.h_pos
  have zeroLength : Canon.L e.ls 0 = 1 := by
    have equal := L_eq e.f e.n e.h_pos
    change Canon.L e.ls 0 = _ at equal
    have maximum : e.mx = lenAt e.f e.n 0 := by
      change lenAt e.f e.n (e.m - 1) = _
      rw [single]
    exact equal.trans (maximum.symm.trans one)
  have replicas : 0 < gReps e.ls e.R e.mx 0 := Nat.two_pow_pos _
  have first := written 0 index 0 replicas
  rw [gaddr0 e single root replicas, Nat.add_zero] at first
  have drop : (e.D 0).drop = 0 := rfl
  have firstLeaf : Subtable.IsLink e.c.type (e.here 0) = false :=
    e.here_not_query_link index kind (by rw [drop]; omega) (by rw [zeroLength]; decide)
  have firstBits : (e.here 0).bits.toNat = 1 := by
    rw [e.here_bits (by rw [zeroLength]; decide), drop, zeroLength]
  have invalidLeaf : Subtable.IsLink e.c.type ⟨64, 1, 0⟩ = false := by
    unfold Subtable.IsLink
    split <;> decide
  rw [root]
  exact two_leaf_table_bits first invalid firstBits rfl firstLeaf invalidLeaf

/-- The actual constructor supplies positive root and subtable bit counts,
including the empty and singleton-invalid cases. -/
theorem constructor_subtable_bits : Subtable.Goal.constructor_subtable_bits := by
  intro h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨result, after, run, _frame, _ret, construction⟩ :=
    inflate_table_construction h type rl ol codes rc oc bits rw ow pre
  refine ⟨result, after, run, ?_⟩
  intro success
  rcases construction success with empty | built
  · obtain ⟨_count, root, _pointer, ca, get, first, second⟩ := empty
    refine ⟨ca, get, ?_⟩
    have rootNat : result.2.2.toNat = 1 := by rw [root]; rfl
    rw [rootNat]
    exact invalid_table_bits first second
  · obtain ⟨_positive, e, ca, _sameF, _sameN, root, _table, offset, sameType,
      get, written, links, details⟩ := built
    have eKind : e.c.type = LENS ∨ e.c.type = DISTS := by rw [sameType]; exact kind
    have table : RootTable.Safe ca e.oc e.R ∧
        ∀ i entry, i < 2 ^ e.R → ca[e.oc + i]? = some entry →
          Subtable.IsLink e.c.type entry = true →
          entry.bits.toNat = e.R ∧ Subtable.Safe ca e.oc entry := by
      rcases e.h_end with complete | ⟨one, single, _notCodes⟩
      · exact e.complete_table_bits complete eKind written links
      · obtain ⟨_used, _returned, _layout, invalid⟩ := details success
        exact e.singleton_table_bits single one eKind written (invalid single one)
    refine ⟨ca, get, ?_⟩
    rwa [sameType, offset, root] at table

theorem code_length_root_bits {ca : Array Code} {offset root : Nat}
    (safe : CodeLengthTableSafe ca offset root) : RootTable.Safe ca offset root := by
  obtain ⟨positive, upper, extent, entries⟩ := safe
  refine ⟨positive, by omega, extent, ?_⟩
  intro i inside
  have bound : offset + i < ca.size := by omega
  have get : ca[offset + i]? = some ca[offset + i] := Array.getElem?_eq_getElem bound
  have cell := entries i inside
  simp only [Array.getD_eq_getD_getElem?, get, Option.getD_some] at cell
  exact ⟨ca[offset + i], get, cell.1, cell.2.1⟩

/-- All admitted table kinds have positive root entry bit counts after
successful construction; CODES reuses its established code-length table. -/
theorem constructor_root_bits : RootTable.Goal.constructor_root_bits := by
  intro h type rl ol codes rc oc bits rw ow pre
  by_cases codesKind : type = CODES
  · obtain ⟨result, after, run, _frame, safe⟩ :=
      inflate_table_decoder_safe h type rl ol codes rc oc bits rw ow pre
    refine ⟨result, after, run, ?_⟩
    intro success
    obtain ⟨ca, get, _low, _high, codesSafe, _lens, _dist⟩ := safe success
    exact ⟨ca, get, code_length_root_bits (codesSafe codesKind)⟩
  · have kind : type = LENS ∨ type = DISTS := by
      rcases pre.hty with codesEq | lensEq | distEq
      · exact False.elim (codesKind codesEq)
      · exact Or.inl lensEq
      · exact Or.inr distEq
    obtain ⟨result, after, run, safe⟩ :=
      constructor_subtable_bits h type rl ol codes rc oc bits rw ow pre kind
    refine ⟨result, after, run, ?_⟩
    intro success
    obtain ⟨ca, get, root, _subtables⟩ := safe success
    exact ⟨ca, get, root⟩

#print axioms Env.complete_table_bits
#print axioms constructor_root_bits
#print axioms constructor_subtable_bits
end Zlib.Inftrees.Proofs
