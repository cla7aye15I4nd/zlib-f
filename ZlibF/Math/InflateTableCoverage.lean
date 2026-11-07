import ZlibF.Math.InflateTableGeometry
import ZlibF.Proof.«inftrees.c.cover.group»

/-! Every cell of a complete canonical table belongs to an actual write.
Subtable descriptors agree throughout a prefix group. Their offsets fit
the 16-bit link field; this follows from the layout rather than an array
size restriction on the caller. -/

namespace Zlib.Inftrees.Proofs
open Zlib.Inftrees.Canon
set_option autoImplicit false

theorem desc_same_group {ls : List Nat} {root mx i j : Nat}
    (hi : i < nz ls) (hj : j < nz ls) (li : root < L ls i) (lj : root < L ls j)
    (same : grp ls root i = grp ls root j) : desc ls root mx i = desc ls root mx j := by
  suffices ordered : ∀ a b, a ≤ b → b < nz ls → root < L ls a →
      grp ls root a = grp ls root b → desc ls root mx a = desc ls root mx b by
    rcases Nat.le_total i j with le | le
    · exact ordered i j le hj li same
    · exact (ordered j i le hi lj same.symm).symm
  intro a b order bound long equal
  induction b with
  | zero => have : a = 0 := by omega
            subst a
            rfl
  | succ b ih =>
    by_cases last : a = b + 1
    · subst a
      rfl
    have before : a ≤ b := by omega
    have g1 := grp_mono ls root before
    have g2 := grp_mono ls root (by omega : b ≤ b + 1)
    have l := L_mono ls before (by omega : b < nz ls)
    have noStart : ¬ startsAt ls root b := by
      rintro ⟨_, short | different⟩
      · omega
      · apply different
        omega
    rw [desc_succ_of_not ls root mx b noStart]
    exact ih before (by omega) (by omega)

/-- A complete subtable has no unwritten holes. The returned replica is
one of the addresses retained by the actual constructor's Written clause. -/
theorem long_subtable_replica {ls : List Nat} {root mx i cell : Nat}
    (code : CompleteCode ls root mx) (index : i < nz ls) (long : root < L ls i)
    (inside : cell < 2 ^ (desc ls root mx i).curr) :
    ∃ j replica, j < nz ls ∧ desc ls root mx j = desc ls root mx i ∧
      replica < gReps ls root mx j ∧
      gAddr ls root mx j replica = (desc ls root mx i).base + cell := by
  obtain ⟨a, order, start, group, drop, width, _⟩ :=
    desc_long (mx := mx) code.min_le index long
  have widths := width_spec ls (by omega : a + 1 < nz ls) code.mx_le
    start.1 (code.L_le_mx (by omega))
  have fits : root + (desc ls root mx i).curr ≤ 15 := by
    have := code.mx_le
    rw [width]
    omega
  have covers : ∀ j, Cover.Group ls root (grp ls root i) j →
      L ls j ≤ root + (desc ls root mx i).curr := by
    intro j member
    have same := desc_same_group (mx := mx) member.1 index member.2.1 long member.2.2
    have fit := desc_fits code member.1
    rw [same, drop] at fit
    omega
  obtain ⟨j, member, ⟨replica, bound, address⟩, _⟩ :=
    Cover.group_cover_idx code.complete (Nat.le_trans code.root_le code.mx_le)
      (j0 := i) ⟨index, long, rfl⟩ fits covers inside
  have same := desc_same_group (mx := mx) member.1 index member.2.1 long member.2.2
  refine ⟨j, replica, member.1, same, ?_, ?_⟩
  · unfold gReps
    rw [same, drop]
    rw [show (desc ls root mx i).curr - (L ls j - root) =
      root + (desc ls root mx i).curr - L ls j by have := member.2.1; omega]
    exact bound
  · unfold gAddr
    rw [same, drop, address, Nat.add_assoc, Nat.mul_comm replica]

/-- The table budget follows the monotone prefix-group number. -/
theorem desc_group_budget {ls : List Nat} {root mx : Nat}
    (code : CompleteCode ls root mx) {i : Nat} (index : i < nz ls) :
    (desc ls root mx i).used ≤ 2 ^ root + (grp ls root i + 1) * 2 ^ (mx - root) := by
  induction i with
  | zero => simp only [desc]; omega
  | succ i ih =>
    have previous := ih (by omega)
    by_cases start : startsAt ls root i
    · have width := width_spec ls index code.mx_le start.1 (code.L_le_mx index)
      have power : 2 ^ Canon.width ls (i + 1) root mx ≤ 2 ^ (mx - root) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      rw [desc_succ_of_starts ls root mx i start]
      dsimp only
      by_cases short : L ls i ≤ root
      · rw [desc_short ls (by omega) short] at previous ⊢
        dsimp only [desc]
        have group : 1 ≤ grp ls root (i + 1) + 1 := by omega
        have budget := Nat.mul_le_mul_right (2 ^ (mx - root)) group
        omega
      · have increasing := grp_mono ls root (by omega : i ≤ i + 1)
        have strict : grp ls root i + 1 ≤ grp ls root (i + 1) := by
          rcases start.2 with impossible | different
          · contradiction
          · omega
        have budget := Nat.mul_le_mul_right (2 ^ (mx - root)) strict
        rw [Nat.add_mul, Nat.one_mul]
        omega
    · rw [desc_succ_of_not ls root mx i start]
      have monotone := Nat.mul_le_mul_right (2 ^ (mx - root))
        (Nat.succ_le_succ (grp_mono ls root (by omega : i ≤ i + 1)))
      change (grp ls root i + 1) * 2 ^ (mx - root) ≤
        (grp ls root (i + 1) + 1) * 2 ^ (mx - root) at monotone
      omega

/-- Link offsets do not truncate when stored as unsigned short. -/
theorem desc_base_lt_u16 {ls : List Nat} {root mx : Nat}
    (code : CompleteCode ls root mx) {i : Nat} (index : i < nz ls) :
    (desc ls root mx i).base < 2 ^ 16 := by
  have budget := desc_group_budget code index
  have groups := Nat.mul_le_mul_right (2 ^ (mx - root)) (grp_lt code index)
  change (grp ls root i + 1) * 2 ^ (mx - root) ≤
    2 ^ root * 2 ^ (mx - root) at groups
  have factor : 2 ^ root * 2 ^ (mx - root) = 2 ^ mx := by
    rw [← Nat.pow_add]
    congr 1
    have := code.root_le
    omega
  rw [factor] at groups
  have rootPower : 2 ^ root ≤ 2 ^ 15 :=
    Nat.pow_le_pow_right (by omega) (Nat.le_trans code.root_le code.mx_le)
  have maxPower : 2 ^ mx ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) code.mx_le
  have positive := Nat.two_pow_pos (desc ls root mx i).curr
  rw [desc_used] at budget
  omega

end Zlib.Inftrees.Proofs
