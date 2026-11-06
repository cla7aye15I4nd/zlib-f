import ZlibF.Proof.«trees.c.heap.gbclk»

/-!
# trees.c: the symbol-level view of the lengths (pure)

`countBefore`, `kraftSum`, `bitCost` and the bridge `gb_symbolic` from per-position facts to them, copied from the
earlier attempt (`Spec/trees/Build.lean`, `GenBitlen.lean`).
-/

namespace Zlib.Trees.Proofs.GB
open Zlib.Trees.Proofs.GB

/-- Number of symbols `m < n` with length `l`. -/
def countBefore (len : Nat → Nat) (l n : Nat) : Nat := ((List.range n).filter (fun m => len m = l)).length


theorem countBefore_succ (len : Nat → Nat) (l n : Nat) :
    countBefore len l (n + 1) = countBefore len l n + (if len n = l then 1 else 0) := by
  unfold countBefore
  rw [List.range_succ, List.filter_append]
  by_cases h : len n = l <;> simp [h]

theorem countBefore_zero (len : Nat → Nat) (l : Nat) : countBefore len l 0 = 0 := rfl

/-- Kraft sum scaled by `2 ^ maxlen` over the nonzero lengths `len n`, `n < N`. -/
def kraftSum (len : Nat → Nat) (N maxlen : Nat) : Nat :=
  ((List.range N).filter (fun n => len n ≠ 0)).foldl (fun acc n => acc + 2 ^ (maxlen - len n)) 0


/-- **Exact bit cost** accumulated by `gen_bitlen` into `opt_len`
(resp. `static_len` with the static lengths `slen`): `Σ_{n ≤ maxc} fr n * (len n + xbits n)`,
where `xbits n = extra[n - base]` for `n ≥ base` and `0` otherwise. `build_tree`
first subtracts 1 from `opt_len` (and `slen n` from `static_len`) for each
symbol it forces to frequency 1, so its net effect on `opt_len` is
`bitCost fr' len xbits maxc - #forced` modulo `2^64`, with `fr'` the frequencies
after forcing. -/
def bitCost (fr len xbits : Nat → Nat) (maxc : Nat) : Nat :=
  (List.range (maxc + 1)).foldl (fun acc n => acc + fr n * (len n + xbits n)) 0


theorem foldl_filter_add (p : Nat → Prop) [DecidablePred p] (F : Nat → Nat) (l : List Nat) (a : Nat) :
    (l.filter (fun n => decide (p n))).foldl (fun acc n => acc + F n) a =
      l.foldl (fun acc n => acc + if p n then F n else 0) a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : p x
    · simp only [List.filter_cons, hx, decide_true, if_true, List.foldl_cons]; exact ih _
    · simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, if_false, List.foldl_cons, Nat.add_zero]
      exact ih _

theorem foldl_range_add (F : Nat → Nat) (N : Nat) : (List.range N).foldl (fun acc n => acc + F n) 0 = rs F N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem kraftSum_rs (len : Nat → Nat) (N L : Nat) :
    kraftSum len N L = rs (fun n => if len n ≠ 0 then 2 ^ (L - len n) else 0) N := by
  unfold kraftSum
  rw [foldl_filter_add (fun n => len n ≠ 0) (fun n => 2 ^ (L - len n)), foldl_range_add]

theorem bitCost_rs (fr len xb : Nat → Nat) (maxc : Nat) :
    bitCost fr len xb maxc = rs (fun n => fr n * (len n + xb n)) (maxc + 1) := by
  unfold bitCost; rw [foldl_range_add]

theorem countBefore_rs (len : Nat → Nat) (l n : Nat) :
    countBefore len l n = rs (fun m => if len m = l then 1 else 0) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [countBefore_succ, ih, rs_succ]


/-- From per-position facts about node lengths `ln` to the symbol-level targets. -/
theorem gb_symbolic {H : Nat → Nat} {hm J elems maxc L : Nat} {fr : Nat → UInt16} {xb : Nat → Nat} {sl : Nat → UInt16}
    (S : PShape H hm J elems maxc) (hT : ∀ v ≤ maxc, fr v ≠ 0 ↔ ∃ q, hm < q ∧ q < 573 ∧ H q = v)
    (ln : Nat → Nat) (C : Nat → Nat)
    (hln : ∀ i < 2 * J, H (hm + 1 + i) ≤ maxc → 1 ≤ ln (H (hm + 1 + i)) ∧ ln (H (hm + 1 + i)) ≤ L)
    (hk : rs (fun i => if H (hm + 1 + i) ≤ maxc then 2 ^ (L - ln (H (hm + 1 + i))) else 0) (2 * J) = 2 ^ L)
    (hc : ∀ x, 1 ≤ x → blP H hm maxc ln (2 * J) x = C x) :
    let len := fun v => if v ≤ maxc ∧ fr v ≠ 0 then ln v else 0
    (∀ n, (maxc < n ∨ fr n = 0) → len n = 0) ∧
    (∀ n ≤ maxc, fr n ≠ 0 → 1 ≤ len n ∧ len n ≤ L ∧ len n = ln n) ∧
    kraftSum len (maxc + 1) L = 2 ^ L ∧
    (∀ x, 1 ≤ x → countBefore len x (maxc + 1) = C x) ∧
    bitCost (fun n => (fr n).toNat) len xb maxc = costP H hm maxc (fun n => (fr n).toNat) ln xb (2 * J) ∧
    bitCost (fun n => (fr n).toNat) (fun n => (sl n).toNat) xb maxc =
      costP H hm maxc (fun n => (fr n).toNat) (fun n => (sl n).toNat) xb (2 * J) := by
  intro len
  have hm_eq := S.hm_eq
  have hleafln : ∀ n ≤ maxc, fr n ≠ 0 → 1 ≤ ln n ∧ ln n ≤ L := by
    intro n hn hf
    obtain ⟨q, h1, h2, e⟩ := (hT n hn).mp hf
    have := hln (q - hm - 1) (by omega) (by rw [show hm + 1 + (q - hm - 1) = q by omega, e]; exact hn)
    rwa [show hm + 1 + (q - hm - 1) = q by omega, e] at this
  have hlen_t : ∀ n ≤ maxc, fr n ≠ 0 → len n = ln n := fun n hn hf => by simp only [len]; rw [if_pos ⟨hn, hf⟩]
  have hlen_f : ∀ n, ¬ (n ≤ maxc ∧ fr n ≠ 0) → len n = 0 := fun n h => by simp only [len]; rw [if_neg h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h
    apply hlen_f n
    intro h'
    rcases h with h | h
    · omega
    · exact h'.2 h
  · intro n hn hf
    rw [hlen_t n hn hf]
    exact ⟨(hleafln n hn hf).1, (hleafln n hn hf).2, rfl⟩
  · rw [kraftSum_rs, ← hk, S.leaf_sum (fun v => fr v ≠ 0) hT (fun v => 2 ^ (L - ln v))]
    apply rs_congr; intro n hn
    by_cases hf : fr n ≠ 0
    · rw [hlen_t n (by omega) hf, if_pos (by have := hleafln n (by omega) hf; omega), if_pos hf]
    · rw [hlen_f n (fun h => hf h.2), if_neg (by simp), if_neg hf]
  · intro x hx
    rw [countBefore_rs, ← hc x hx]
    have e3 : blP H hm maxc ln (2 * J) x = rs (fun i => if H (hm + 1 + i) ≤ maxc then
        (fun v => if ln v = x then 1 else 0) (H (hm + 1 + i)) else 0) (2 * J) := by
      unfold blP; apply rs_congr; intro i _
      by_cases a : H (hm + 1 + i) ≤ maxc
      · rw [if_pos a]
        by_cases b : ln (H (hm + 1 + i)) = x
        · rw [if_pos ⟨a, b⟩]; simp only; rw [if_pos b]
        · rw [if_neg (fun h => b h.2)]; simp only; rw [if_neg b]
      · rw [if_neg (fun h => a h.1), if_neg a]
    rw [e3, S.leaf_sum (fun v => fr v ≠ 0) hT (fun v => if ln v = x then 1 else 0)]
    apply rs_congr; intro n hn
    by_cases hf : fr n ≠ 0
    · rw [hlen_t n (by omega) hf, if_pos hf]
    · rw [hlen_f n (fun h => hf h.2), if_neg (by omega), if_neg hf]
  · rw [bitCost_rs]; unfold costP
    rw [S.leaf_sum (fun v => fr v ≠ 0) hT (fun v => (fr v).toNat * (ln v + xb v))]
    apply rs_congr; intro n hn
    by_cases hf : fr n ≠ 0
    · rw [hlen_t n (by omega) hf, if_pos hf]
    · rw [if_neg hf]; simp only [Decidable.not_not] at hf; rw [hf]; simp
  · rw [bitCost_rs]; unfold costP
    rw [S.leaf_sum (fun v => fr v ≠ 0) hT (fun v => (fr v).toNat * ((sl v).toNat + xb v))]
    apply rs_congr; intro n hn
    by_cases hf : fr n ≠ 0
    · rw [if_pos hf]
    · rw [if_neg hf]; simp only [Decidable.not_not] at hf; rw [hf]; simp

end Zlib.Trees.Proofs.GB
