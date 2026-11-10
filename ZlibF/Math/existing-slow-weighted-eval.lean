import ZlibF.Math.«existing-slow-weighted-sort»
import ZlibF.Math.«existing-slow-covf-certificate»
namespace ZlibF.Math.CovfSorting
open CovfCertificate
set_option autoImplicit false

/-- The zero-based integer certificate objective is exactly the natural
list cost, with every frequency/depth pairing retained. -/
theorem eval_weighted (xs : List Nat) (w : Nat → Nat) :
    eval (List.range xs.length) (fun j => (xs[j]?.getD 0 : Int)) w = (weighted w xs : Int) := by
  induction xs generalizing w with
  | nil => simp [eval,weighted]
  | cons x xs ih =>
    simp only [List.length_cons,List.range_succ_eq_map]
    unfold eval
    simp only [List.map_cons,List.sum_cons,List.getElem?_cons_zero,Option.getD_some,
      List.map_map,Function.comp_apply,List.getElem?_cons_succ]
    change (x:Int)*(w 0:Int)+
      eval (List.range xs.length) (fun j => (xs[j]?.getD 0 : Int)) (fun i => w (i+1)) =
        (w 0:Int)*(x:Int)+(weighted (fun i => w (i+1)) xs : Int)
    rw [ih,Int.mul_comm (x:Int) (w 0:Int)]

/-- The raw depth vector can be arbitrary. Only its ascending permutation
and descending rank weights are required for the exact Int objective bound. -/
theorem eval_sorted_permutation_le {xs ys : List Nat}
    (sorted : ys.Pairwise (·≤·)) (permutation : ys.Perm xs) (w : Nat → Nat)
    (descending : Descending w xs.length) :
    eval (List.range ys.length) (fun j => (ys[j]?.getD 0 : Int)) w ≤
      eval (List.range xs.length) (fun j => (xs[j]?.getD 0 : Int)) w := by
  rw [eval_weighted,eval_weighted]
  have natural := sorted_permutation_weighted_le sorted permutation w descending
  omega

/-- Equal permutation length gives the common coordinate range expected
by the overflow certificate cost interfaces. -/
theorem eval_sorted_permutation_le_same_range {xs ys : List Nat}
    (sorted : ys.Pairwise (·≤·)) (permutation : ys.Perm xs) (w : Nat → Nat)
    (descending : Descending w xs.length) :
    eval (List.range xs.length) (fun j => (ys[j]?.getD 0 : Int)) w ≤
      eval (List.range xs.length) (fun j => (xs[j]?.getD 0 : Int)) w := by
  have result := eval_sorted_permutation_le sorted permutation w descending
  simpa only [permutation.length_eq] using result

#print axioms eval_weighted
#print axioms eval_sorted_permutation_le
#print axioms eval_sorted_permutation_le_same_range
end ZlibF.Math.CovfSorting
