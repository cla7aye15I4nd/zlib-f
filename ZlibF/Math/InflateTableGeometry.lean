import ZlibF.Proof.«inftrees.c.step»
import ZlibF.Proof.«inftrees.c.cover.root»

/-!
# Disjoint cells in the actual decode-table layout

The existing descriptor vocabulary lives with the constructor proof. These
lemmas are heap-free: separate allocation intervals first, then use canonical
prefix uniqueness inside an interval.
-/

namespace Zlib.Inftrees.Proofs
open Zlib.Inftrees.Canon
set_option autoImplicit false

theorem desc_regions (ls : List Nat) (root mx : Nat) {i j : Nat} (order : i ≤ j) :
    desc ls root mx i = desc ls root mx j ∨
      (desc ls root mx i).used ≤ (desc ls root mx j).base := by
  induction j with
  | zero => have : i = 0 := by omega
            subst i
            exact Or.inl rfl
  | succ j ih =>
    by_cases same : i = j + 1
    · subst i
      exact Or.inl rfl
    · have previous := ih (by omega)
      by_cases start : startsAt ls root j
      · rw [desc_succ_of_starts ls root mx j start]
        dsimp only
        right
        rcases previous with equal | separated
        · rw [equal, desc_used]
          exact Nat.le_refl _
        · have := Nat.two_pow_pos (desc ls root mx j).curr
          omega
      · rw [desc_succ_of_not ls root mx j start]
        exact previous

theorem gAddr_in_region {ls : List Nat} {root mx i m : Nat}
    (code : CompleteCode ls root mx) (index : i < nz ls)
    (copy : m < gReps ls root mx i) :
    (desc ls root mx i).base ≤ gAddr ls root mx i m ∧
      gAddr ls root mx i m < (desc ls root mx i).used := by
  obtain ⟨drop, fits, _, _⟩ := desc_fits code index
  have power : 2 ^ (L ls i - (desc ls root mx i).drop) *
      2 ^ (desc ls root mx i).drop = 2 ^ L ls i := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have quotient : H ls i / 2 ^ (desc ls root mx i).drop <
      2 ^ (L ls i - (desc ls root mx i).drop) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), power]
    exact Canon.H_lt ls i
  have capacity : 2 ^ ((desc ls root mx i).curr -
      (L ls i - (desc ls root mx i).drop)) *
      2 ^ (L ls i - (desc ls root mx i).drop) = 2 ^ (desc ls root mx i).curr := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have count := Nat.mul_le_mul_right
    (2 ^ (L ls i - (desc ls root mx i).drop)) (Nat.succ_le_of_lt copy)
  change (m + 1) * _ ≤ 2 ^ ((desc ls root mx i).curr -
    (L ls i - (desc ls root mx i).drop)) * _ at count
  rw [capacity, Nat.add_mul, Nat.one_mul] at count
  rw [desc_used]
  unfold gAddr
  constructor
  · exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  · have localBound : H ls i / 2 ^ (desc ls root mx i).drop +
        m * 2 ^ (L ls i - (desc ls root mx i).drop) < 2 ^ (desc ls root mx i).curr := by
      calc
        _ < 2 ^ (L ls i - (desc ls root mx i).drop) +
            m * 2 ^ (L ls i - (desc ls root mx i).drop) := Nat.add_lt_add_right quotient _
        _ = m * 2 ^ (L ls i - (desc ls root mx i).drop) +
            2 ^ (L ls i - (desc ls root mx i).drop) := Nat.add_comm _ _
        _ ≤ _ := count
    simpa only [Nat.add_assoc] using Nat.add_lt_add_left localBound (desc ls root mx i).base

theorem desc_residue {ls : List Nat} {root mx i : Nat}
    (code : CompleteCode ls root mx) (index : i < nz ls) :
    H ls i % 2 ^ (desc ls root mx i).drop =
      (desc ls root mx i).low % 2 ^ (desc ls root mx i).drop := by
  by_cases short : L ls i ≤ root
  · rw [desc_short ls index short]
    simp [desc, Nat.mod_one]
  · obtain ⟨a, _, _, _, drop, _, low⟩ := desc_long (mx := mx) code.min_le index (by omega)
    rw [drop, low, H_mod_root ls index (by omega),
      Nat.mod_eq_of_lt (Canon.rev_lt _ _)]

theorem replicated_residue (value len drop m : Nat) (inside : value < 2 ^ len)
    (le : drop ≤ len) :
    (value % 2 ^ drop + 2 ^ drop * (value / 2 ^ drop + m * 2 ^ (len - drop))) %
      2 ^ len = value := by
  have factor : 2 ^ drop * 2 ^ (len - drop) = 2 ^ len := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have decompose := Nat.mod_add_div value (2 ^ drop)
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ drop) m,
    Nat.mul_assoc, factor]
  rw [show value % 2 ^ drop + (2 ^ drop * (value / 2 ^ drop) + m * 2 ^ len) =
    value + m * 2 ^ len by omega]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt inside]

theorem canonical_prefix_unique {ls : List Nat} (fit : Cover.Fit ls)
    {i j value : Nat} (hi : i < nz ls) (hj : j < nz ls)
    (left : value % 2 ^ L ls i = H ls i) (right : value % 2 ^ L ls j = H ls j) : i = j := by
  have ti := (Cover.short_iff fit (R := 15) (by omega) hi (L_interval ls hi).2.1).mpr left
  have tj := (Cover.short_iff fit (R := 15) (by omega) hj (L_interval ls hj).2.1).mpr right
  exact Cover.tile_unique ls ti tj

/-- Every root cell covered by a short code is one of that code's actual
replicated write addresses, with the replica index in range. -/
theorem short_root_replica {ls : List Nat} {root mx i cell : Nat}
    (index : i < nz ls) (short : L ls i ≤ root) (inside : cell < 2 ^ root)
    (residue : cell % 2 ^ L ls i = H ls i) :
    ∃ replica, replica < gReps ls root mx i ∧ gAddr ls root mx i replica = cell := by
  refine ⟨cell / 2 ^ L ls i, ?_, ?_⟩
  · unfold gReps
    rw [desc_short ls index short]
    simp only [desc, Nat.sub_zero]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    have exponent : root - L ls i + L ls i = root := by omega
    rwa [exponent]
  · unfold gAddr
    rw [desc_short ls index short]
    simp only [desc, Nat.pow_zero, Nat.div_one, Nat.sub_zero, Nat.zero_add]
    have decompose := Nat.mod_add_div cell (2 ^ L ls i)
    rw [residue] at decompose
    simpa only [Nat.mul_comm] using decompose

theorem gAddr_unique {ls : List Nat} {root mx i j m n : Nat}
    (code : CompleteCode ls root mx) (hi : i < nz ls) (hj : j < nz ls)
    (hm : m < gReps ls root mx i) (hn : n < gReps ls root mx j)
    (same : gAddr ls root mx i m = gAddr ls root mx j n) : i = j ∧ m = n := by
  have ri := gAddr_in_region code hi hm
  have rj := gAddr_in_region code hj hn
  have descriptors : desc ls root mx i = desc ls root mx j := by
    by_cases order : i ≤ j
    · rcases desc_regions ls root mx order with equal | separated
      · exact equal
      · omega
    · rcases desc_regions ls root mx (by omega : j ≤ i) with equal | separated
      · exact equal.symm
      · omega
  have dropI := (desc_fits code hi).1
  have dropJ := (desc_fits code hj).1
  have residueI := desc_residue code hi
  have residueJ := desc_residue code hj
  rw [← descriptors] at dropJ residueJ
  have low : H ls i % 2 ^ (desc ls root mx i).drop =
      H ls j % 2 ^ (desc ls root mx i).drop := residueI.trans residueJ.symm
  have localSame : H ls i / 2 ^ (desc ls root mx i).drop +
      m * 2 ^ (L ls i - (desc ls root mx i).drop) =
      H ls j / 2 ^ (desc ls root mx i).drop +
      n * 2 ^ (L ls j - (desc ls root mx i).drop) := by
    unfold gAddr at same
    rw [← descriptors] at same
    omega
  let value := H ls i % 2 ^ (desc ls root mx i).drop +
    2 ^ (desc ls root mx i).drop *
      (H ls i / 2 ^ (desc ls root mx i).drop +
        m * 2 ^ (L ls i - (desc ls root mx i).drop))
  have left : value % 2 ^ L ls i = H ls i :=
    replicated_residue _ _ _ _ (Canon.H_lt ls i) dropI
  have right : value % 2 ^ L ls j = H ls j := by
    dsimp only [value]
    rw [low, localSame]
    exact replicated_residue _ _ _ _ (Canon.H_lt ls j) dropJ
  have fit : Cover.Fit ls := Nat.le_of_eq code.complete
  have equal := canonical_prefix_unique fit hi hj left right
  subst j
  refine ⟨rfl, ?_⟩
  unfold gAddr at same
  have product : m * 2 ^ (L ls i - (desc ls root mx i).drop) =
      n * 2 ^ (L ls i - (desc ls root mx i).drop) := by omega
  exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) product

theorem startsAt_group_strict {ls : List Nat} {root a b : Nat}
    (ha : a < nz ls) (hb : b < nz ls) (ordered : a < b)
    (long : root < L ls a) (positive : 1 ≤ b) (start : startsAt ls root (b - 1)) :
    grp ls root a < grp ls root b := by
  have monotone := grp_mono ls root (Nat.le_of_lt ordered)
  by_cases strict : grp ls root a < grp ls root b
  · exact strict
  exfalso
  have equal : grp ls root a = grp ls root b := by omega
  have left := grp_mono ls root (by omega : a ≤ b - 1)
  have right := grp_mono ls root (by omega : b - 1 ≤ b)
  have lengths := L_mono ls (by omega : a ≤ b - 1) (by omega : b - 1 < nz ls)
  unfold startsAt at start
  rw [show b - 1 + 1 = b by omega] at start
  rcases start.2 with short | changed
  · omega
  · apply changed
    omega

theorem gSlot_unique {ls : List Nat} {root mx a b : Nat}
    (code : CompleteCode ls root mx) (ha0 : 1 ≤ a) (ha : a < nz ls)
    (sa : startsAt ls root (a - 1)) (hb0 : 1 ≤ b) (hb : b < nz ls)
    (sb : startsAt ls root (b - 1)) (same : gSlot ls root a = gSlot ls root b) : a = b := by
  have sameGroup : grp ls root a = grp ls root b :=
    Canon.rev_inj (grp_lt code ha) (grp_lt code hb) same
  have la : root < L ls a := by
    have := sa.1
    simpa only [show a - 1 + 1 = a by omega] using this
  have lb : root < L ls b := by
    have := sb.1
    simpa only [show b - 1 + 1 = b by omega] using this
  by_cases order : a < b
  · have := startsAt_group_strict ha hb order la hb0 sb
    omega
  · by_cases reverse : b < a
    · have := startsAt_group_strict hb ha reverse lb ha0 sa
      omega
    · omega

theorem gSlot_ne_gAddr {ls : List Nat} {root mx a i m : Nat}
    (code : CompleteCode ls root mx) (positive : 1 ≤ a) (ha : a < nz ls)
    (start : startsAt ls root (a - 1)) (hi : i < nz ls)
    (hm : m < gReps ls root mx i) : gSlot ls root a ≠ gAddr ls root mx i m := by
  intro same
  have rootBound : gSlot ls root a < 2 ^ root := Canon.rev_lt _ _
  by_cases short : L ls i ≤ root
  · have residue : gAddr ls root mx i m % 2 ^ L ls i = H ls i := by
      unfold gAddr
      rw [desc_short ls hi short]
      simp only [desc, Nat.zero_add, Nat.pow_zero, Nat.div_one, Nat.sub_zero]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Canon.H_lt ls i)]
    have shortAt : Cover.ShortAt ls root (gSlot ls root a) i :=
      ⟨hi, short, by rw [same]; exact residue⟩
    have long : root < L ls a := by
      have := start.1
      simpa only [show a - 1 + 1 = a by omega] using this
    have longAt : Cover.LongAt ls root (gSlot ls root a) a := by
      refine ⟨ha, long, ?_⟩
      rw [Canon.H_mod_root ls ha (by omega)]
      rfl
    have cover := Cover.root_cover (Nat.le_of_eq code.complete)
      (Nat.le_trans code.root_le code.mx_le) rootBound
    cases cover with
    | short j _ _ noLong => exact noLong a longAt
    | long j _ noShort => exact noShort i shortAt
    | free noShort _ _ => exact noShort i shortAt
  · have region := gAddr_in_region code hi hm
    obtain ⟨_, _, _, _, drop, _, _⟩ := desc_long (mx := mx) code.min_le hi (by omega)
    have baseBound : 2 ^ root ≤ (desc ls root mx i).base := by
      rcases desc_regions ls root mx (i := 0) (j := i) (by omega) with equal | separated
      · have sameDrop := congrArg Desc.drop equal
        simp only [desc] at sameDrop
        rw [drop] at sameDrop
        have := code.root_pos
        omega
      · exact separated
    omega

/-- Complete canonical codes have disjoint replicated leaves and link
slots in the constructor's existing concrete descriptor layout. -/
theorem geometry_complete {ls : List Nat} {root mx : Nat}
    (code : CompleteCode ls root mx) : GeoOK ls root mx := by
  constructor
  · intro i j m n hi hj hm hn same
    exact gAddr_unique code hi hj hm hn same
  · intro a i m positive ha start hi hm
    exact gSlot_ne_gAddr code positive ha start hi hm
  · intro a b ha0 ha sa hb0 hb sb same
    exact gSlot_unique code ha0 ha sa hb0 hb sb same

/-- The accepted incomplete single-symbol case has one leaf family and
no subtable links. It does not require a complete Kraft partition. -/
theorem geometry_single {ls : List Nat} {root mx : Nat} (single : nz ls = 1) :
    GeoOK ls root mx := by
  constructor
  · intro i j m n hi hj hm hn same
    have iz : i = 0 := by omega
    have jz : j = 0 := by omega
    subst i
    subst j
    refine ⟨rfl, ?_⟩
    simp only [gAddr, desc, Nat.zero_add, Nat.pow_zero, Nat.div_one, Nat.sub_zero] at same
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) (Nat.add_left_cancel same)
  · intro a i m positive ha start hi hm
    omega
  · intro a b ha0 ha sa hb0 hb sb same
    omega

end Zlib.Inftrees.Proofs
