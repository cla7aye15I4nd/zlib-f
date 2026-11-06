import ZlibF.Proof.«inftrees.c.canon»
import ZlibF.Proof.«inftrees.c.link»

/-!
# The two models of the canonical construction agree

`Canon` (a list `ls` of lengths, allocation index `j`, Kraft sums `K`) and the model of the main proof
(`f`, `n`, `wsAux`, `lenAt`, `val`) describe the same objects for `ls = lensOf f n`.
-/
namespace Zlib.Inftrees.Proofs
open Zlib.Inftrees.Canon

theorem canon_rev_eq : ∀ k x, Canon.rev k x = Proofs.rev k x
  | 0, _ => rfl
  | k + 1, x => by
    rw [Canon.rev_succ, canon_rev_eq k, Proofs.rev]; omega

theorem lensOf_length (f : Nat → Nat) (n : Nat) : (lensOf f n).length = n := by simp [lensOf]

theorem lensOf_getD (f : Nat → Nat) {n s : Nat} (h : s < n) : (lensOf f n).getD s 0 = f s := by
  simp [lensOf, List.getD_eq_getElem?_getD, h]

theorem symsOf_eq (f : Nat → Nat) (n l : Nat) : symsOf (lensOf f n) l = fl f l n := by
  unfold symsOf fl
  rw [lensOf_length]
  apply List.filter_congr
  intro s hs
  rw [List.mem_range] at hs
  rw [lensOf_getD f hs]

theorem ord_eq (f : Nat → Nat) (n : Nat) : ord (lensOf f n) = wsAux f n 15 := by
  unfold ord
  have : ∀ k, (List.range k).flatMap (fun i => symsOf (lensOf f n) (i + 1)) = wsAux f n k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp [wsAux, symsOf_eq]
  exact this 15

theorem L_eq (f : Nat → Nat) (n : Nat) {j : Nat} (hj : j < Tc f n 15) :
    L (lensOf f n) j = lenAt f n j := by
  unfold L sy lenAt
  rw [ord_eq]
  have hlen : (wsAux f n 15).length = Tc f n 15 := wsAux_length 15
  have hm := List.getElem_mem (show j < (wsAux f n 15).length by omega)
  have hs := (mem_wsAux.mp hm).1
  have hg : (wsAux f n 15).getD j 0 = (wsAux f n 15)[j]'(by omega) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hg]
  exact lensOf_getD f hs

theorem K_succ (ls : List Nat) (j : Nat) : K ls (j + 1) = K ls j + 2 ^ (15 - L ls j) := by
  unfold K
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem K_eq (f : Nat → Nat) (n : Nat) : ∀ j, j < Tc f n 15 →
    K (lensOf f n) j = val f n j * 2 ^ (15 - lenAt f n j)
  | 0, h => by
    rw [val_zero h]; simp [K]
  | j + 1, h => by
    have ih := K_eq f n j (by omega)
    obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) (show j < Tc f n 15 by omega)
    obtain ⟨c1, c2⟩ := lenAt_bounds (f := f) (n := n) h
    have mono := lenAt_mono (f := f) (n := n) (show j ≤ j + 1 by omega) h
    have hs := val_succ (f := f) (n := n) h
    rw [K_succ, L_eq f n (by omega), ih, hs]
    obtain ⟨d, hd⟩ : ∃ d, lenAt f n (j + 1) = lenAt f n j + d := ⟨lenAt f n (j + 1) - lenAt f n j, by omega⟩
    have e1 : lenAt f n (j + 1) - lenAt f n j = d := by omega
    have e2 : 15 - lenAt f n j = (15 - lenAt f n (j + 1)) + d := by omega
    rw [e1, e2, Nat.pow_add, Nat.add_mul, Nat.one_mul]
    generalize (2 : Nat) ^ (15 - lenAt f n (j + 1)) = P
    generalize (2 : Nat) ^ d = Q
    generalize val f n j = V
    rw [Nat.add_mul]
    ac_rfl

theorem H_eq (f : Nat → Nat) (n : Nat) {j : Nat} (hj : j < Tc f n 15) :
    H (lensOf f n) j = Proofs.rev (lenAt f n j) (val f n j) := by
  unfold H cv
  rw [K_eq f n j hj, L_eq f n hj, Nat.mul_div_cancel _ (Nat.pow_pos (by omega)), canon_rev_eq]

end Zlib.Inftrees.Proofs
