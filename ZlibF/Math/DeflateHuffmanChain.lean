import ZlibF.Proof.«trees.c.heap.gbclk»
import ZlibF.Math.HuffmanFib

/-!
Pure ancestor-chain mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
Imports and the namespace use this project's existing tree-shape definitions.
No theorem here assumes execution of a translated callee.
-/

/-!
# Ancestor chains of the tree `build_tree` built (input of Lemma 2)

For a node at heap position `q` (`hm < q < 573`) of Huffman depth `d` (the unclamped depth
`dl`, i.e. `Clamped` with a bound `1000` that is never reached), `leaf_chain` gives the
weights `p 0 = w (H q), p 1, …, p d = W` of its ancestors and `s i` of their siblings with
`p (i+1) = p i + s i`, `s 0 ≥ 1` and `p i ≤ s (i+1)` (the sibling of the `(i+1)`-th ancestor
was removed after the `i`-th ancestor: the removal order is monotone in weight). These are
the hypotheses of the abstract `fibChain_bound`, which gives `w * F(d+1) + F(d) ≤ W`
(`docs/DEFLATE_OVERLAY.md` §7, Lemma 2).
-/

namespace Zlib.Trees.Proofs.GB


/-- The position paired with `q` (the two children of a node sit at `572 - 2j`, `571 - 2j`). -/
def sibP (q : Nat) : Nat := if (572 - q) % 2 = 0 then q - 1 else q + 1

section
variable {H : Nat → Nat} {hm J elems maxc : Nat} {dl : Nat → Nat}

/-- The parent of the node at position `q` sits at a position `q'` below the pair of `q`. -/
theorem parent_pos (S : PShape H hm J elems maxc) {q : Nat} (h1 : hm < q) (h2 : q < 573) :
    ∃ q', hm ≤ q' ∧ q' < 571 - 2 * ((572 - q) / 2) ∧ H q' = dadP elems q ∧ (572 - q) / 2 < J := by
  have := S.hm_eq
  obtain ⟨q', a, b, c⟩ := S.appears ((572 - q) / 2) (by omega)
  exact ⟨q', a, b, by rw [c]; rfl, by omega⟩

theorem dl_step (S : PShape H hm J elems maxc) (C : Clamped H hm J elems 1000 dl) {q : Nat} (h1 : hm < q)
    (h2 : q < 573) : dl (H q) = min (dl (dadP elems q) + 1) 1000 := by
  have := S.hm_eq
  have := C.step (q - hm - 1) (by omega)
  rw [show hm + 1 + (q - hm - 1) = q by omega] at this
  exact this

theorem dl_le (S : PShape H hm J elems maxc) (C : Clamped H hm J elems 1000 dl) :
    ∀ q, hm ≤ q → q < 573 → dl (H q) ≤ q - hm := by
  suffices h : ∀ n q, q ≤ hm + n → hm ≤ q → q < 573 → dl (H q) ≤ q - hm from fun q a b => h (q - hm) q (by omega) a b
  intro n
  induction n with
  | zero => intro q h0 a b; rw [show q = hm by omega, C.root]; omega
  | succ n ih =>
    intro q h0 a b
    by_cases e : q = hm
    · rw [e, C.root]; omega
    · obtain ⟨q', a', b', c', -⟩ := parent_pos S (q := q) (by omega) b
      rw [dl_step S C (by omega) b, ← c']
      have := ih q' (by omega) a' (by omega)
      omega

/-- **Ancestor chain** of the node at position `q`, of depth `d`. -/
theorem leaf_chain (S : PShape H hm J elems maxc) (C : Clamped H hm J elems 1000 dl) (w : Nat → Nat) (W : Nat)
    (hsum : ∀ j < J, w (elems + j) = w (H (572 - 2 * j)) + w (H (571 - 2 * j)))
    (hmono : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (hpos : ∀ q, hm < q → q < 573 → 1 ≤ w (H q)) (hroot : w (H hm) = W) :
    ∀ d q, hm < q → q < 573 → dl (H q) = d → ∃ p s : Nat → Nat, p 0 = w (H q) ∧
      (∀ i < d, p (i + 1) = p i + s i) ∧ (0 < d → 1 ≤ s 0) ∧ (∀ i, i + 1 < d → p i ≤ s (i + 1)) ∧
      p d = W ∧ (0 < d → s 0 = w (H (sibP q))) := by
  have hmq := S.hm_eq
  intro d
  induction d with
  | zero =>
    intro q h1 h2 hd
    rw [dl_step S C h1 h2] at hd; omega
  | succ d ih =>
    intro q h1 h2 hd
    obtain ⟨q', a, b, c, hj⟩ := parent_pos S h1 h2
    have hle := dl_le S C q' a (by omega)
    have hd' : dl (H q') = d := by
      rw [dl_step S C h1 h2, ← c] at hd; omega
    -- the parent weighs the node plus its sibling
    have hpar : w (H q') = w (H q) + w (H (sibP q)) := by
      rw [c]; unfold dadP sibP
      rw [hsum _ hj]
      by_cases e : (572 - q) % 2 = 0
      · rw [if_pos e, show 572 - 2 * ((572 - q) / 2) = q by omega, show 571 - 2 * ((572 - q) / 2) = q - 1 by omega]
      · rw [if_neg e, show 572 - 2 * ((572 - q) / 2) = q + 1 by omega, show 571 - 2 * ((572 - q) / 2) = q by omega,
          Nat.add_comm]
    have hsib1 : 1 ≤ w (H (sibP q)) := hpos _ (by unfold sibP; split <;> omega) (by unfold sibP; split <;> omega)
    by_cases hq' : q' = hm
    · subst hq'
      rw [C.root] at hd'
      subst hd'
      refine ⟨fun i => if i = 0 then w (H q) else W, fun _ => w (H (sibP q)), rfl, fun i hi => ?_,
        fun _ => hsib1, fun i hi => by omega, rfl, fun _ => rfl⟩
      have : i = 0 := by omega
      subst this; dsimp only
      rw [if_neg (show ¬ (0 + 1 = 0) by omega), if_pos rfl, ← hroot, hpar]
    · obtain ⟨p', s', e0, est, es0, esm, ed, esib⟩ := ih q' (by omega) (by omega) hd'
      have hd1 : 0 < d := by
        rw [← hd']; rw [dl_step S C (by omega) (by omega)]; omega
      refine ⟨fun i => if i = 0 then w (H q) else p' (i - 1), fun i => if i = 0 then w (H (sibP q)) else s' (i - 1),
        rfl, fun i hi => ?_, fun _ => hsib1, fun i hi => ?_, ?_, fun _ => rfl⟩
      · by_cases e : i = 0
        · subst e; dsimp only
          rw [if_neg (show ¬ (0 + 1 = 0) by omega), if_pos rfl, if_pos rfl, show 0 + 1 - 1 = 0 from rfl, e0, hpar]
        · simp only [if_neg (show ¬ (i + 1 = 0) by omega), if_neg e, show i + 1 - 1 = (i - 1) + 1 by omega]
          exact est (i - 1) (by omega)
      · by_cases e : i = 0
        · subst e
          dsimp only
          rw [if_neg (show ¬ (0 + 1 = 0) by omega), if_pos rfl, show 0 + 1 - 1 = 0 from rfl, esib hd1]
          -- the sibling of the parent was removed after the node
          have hs1 : hm + 1 ≤ sibP q' := by
            obtain ⟨-, -, -, -, hj'⟩ := parent_pos S (q := q') (by omega) (by omega)
            unfold sibP; split <;> omega
          exact hmono q (sibP q') hs1 (by unfold sibP; split <;> omega) h2
        · simp only [if_neg e, if_neg (show ¬ (i + 1 = 0) by omega), show i + 1 - 1 = (i - 1) + 1 by omega]
          exact esm (i - 1) (by omega)
      · simp only [if_neg (show ¬ (d + 1 = 0) by omega), Nat.add_sub_cancel]; exact ed

end

/-- Positive leaf weights and exact internal sums make every retained
node positive. No unsigned arithmetic is used in this pure statement. -/
theorem tree_weights_positive {H : Nat → Nat} {hm J elems maxc : Nat}
    (shape : PShape H hm J elems maxc) (w : Nat → Nat)
    (leaves : ∀ q, hm ≤ q → q < 573 → H q < elems → 1 ≤ w (H q))
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a))) :
    ∀ q, hm ≤ q → q < 573 → 1 ≤ w (H q) := by
  have boundary := shape.hm_eq
  have maxc := shape.maxc_lt
  suffices all : ∀ v q, hm ≤ q → q < 573 → H q = v → 1 ≤ w v from
    fun q lower upper => all _ q lower upper rfl
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro q lower upper equal
    rcases shape.kind q lower upper with leaf | internal
    · rw [← equal]
      exact leaves q lower upper (by omega)
    · obtain ⟨a, equation⟩ : ∃ a, v = elems + a := ⟨v - elems, by omega⟩
      have bound : a < J := by omega
      have child : H (572 - 2 * a) < elems + a := by
        rcases shape.kind (572 - 2 * a) (by omega) (by omega) with leaf | internal
        · omega
        · obtain ⟨pos, lo, hi, value⟩ := shape.appears (H (572 - 2 * a) - elems) (by omega)
          have same := shape.inj pos (572 - 2 * a) lo (by omega) (by omega) (by omega)
            (by rw [value]; omega)
          omega
      have positive := ih _ (by omega) (572 - 2 * a) (by omega) (by omega) rfl
      rw [equation, sums a bound]
      omega

/-- Every node in a positive, ordered Huffman tree of weight below 65536
has level at most 22. The full ancestor-chain argument precedes this bound;
it does not assume that a source UInt8 depth already represents a height. -/
theorem tree_levels_le_22 {H : Nat → Nat} {hm J elems maxc : Nat}
    (shape : PShape H hm J elems maxc) (w : Nat → Nat)
    (positive : ∀ q, hm ≤ q → q < 573 → 1 ≤ w (H q))
    (sums : ∀ a, a < J → w (elems + a) = w (H (572 - 2 * a)) + w (H (571 - 2 * a)))
    (order : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 → w (H q) ≤ w (H q'))
    (budget : w (H hm) < 2 ^ 16) :
    ∀ q, hm ≤ q → q < 573 → clK H hm elems 1000 (2 * J) (H q) ≤ 22 := by
  have clamped := clK_clamped (L := 1000) shape
  intro q lower upper
  by_cases root : q = hm
  · subst q
    rw [clamped.root]
    omega
  · obtain ⟨p, s, initial, steps, first, siblings, last, _sibling⟩ := leaf_chain shape clamped w
      (w (H hm)) sums order (fun q lo hi => positive q (by omega) hi) rfl
      _ q (by omega) upper rfl
    have bound := Zlib.Trees.HuffmanAbstract.fibChain_bound p s (w (H q))
      (clK H hm elems 1000 (2 * J) (H q)) initial steps first siblings
    rw [last] at bound
    have pos := positive q lower upper
    have product := Nat.le_mul_of_pos_left
      (Zlib.Trees.HuffmanAbstract.fib (clK H hm elems 1000 (2 * J) (H q) + 1)) pos
    have recurrence := Zlib.Trees.HuffmanAbstract.fib_add_two (clK H hm elems 1000 (2 * J) (H q))
    apply Nat.le_of_not_lt
    intro tooDeep
    have lowerFib := Zlib.Trees.HuffmanAbstract.fib_mono
      (show 25 ≤ clK H hm elems 1000 (2 * J) (H q) + 2 by omega)
    have value : Zlib.Trees.HuffmanAbstract.fib 25 = 75025 := by decide +kernel
    omega

end Zlib.Trees.Proofs.GB
