import ZlibF.Math.HuffmanRepairModel

/-!
Pure Huffman mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The mathematical statements and proof bodies are retained. Imports use this
project. No result here alone establishes refinement of the translated C.
-/

/-!
# Dynamics of `gen_bitlen`'s overflow repair (`max_length = 15`)

`docs/the reference overlay analysis` §7.2, Lemmas 4–5, on the count model `repairIter 15`. Write
`T_s = 2^(15−s) − 1`. Suppose levels `s+1 .. 14` are empty, `c s ≥ 1`, and level 15 has at
least as many units as the number of moves made.

* `exp_full`: the next `T_s` moves expand one unit of level `s` completely. The result is
  `c s − 1` at `s`, `c 15 + 1` at 15, and every other level unchanged.
* `exp_partial`: after `0 < t < T_s` moves, the levels below `s` are unchanged and level
  `s` has lost exactly one unit. If moreover `t ≤ 2^(14−s)`, level `s+1` is nonempty.
-/

namespace Zlib.Trees.HuffmanAbstract

/-- Close a goal about nested `if`s on `Nat` indices: split every `if`, substitute, `omega`. -/
local macro "ite_omega" : tactic =>
  `(tactic| ((try simp only [↓reduceIte, Nat.reduceAdd]) <;> (repeat' split) <;> (try subst_vars) <;>
    (try simp only [↓reduceIte, Nat.reduceAdd] at *) <;> omega))

theorem repairIter_add (L : Nat) : ∀ (a b : Nat) (c : Nat → Nat),
    repairIter L (a + b) c = repairIter L b (repairIter L a c)
  | 0, b, c => by simp [repairIter]
  | a + 1, b, c => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [repairIter]
    exact repairIter_add L a b (repairStep L c)

theorem deepest_eq (c : Nat → Nat) (s : Nat) (hs : c s ≠ 0) :
    ∀ b, s ≤ b → (∀ j, s < j → j ≤ b → c j = 0) → deepest c b = s
  | 0, hsb, _ => by simp [deepest]; omega
  | b + 1, hsb, hz => by
    simp only [deepest]
    rcases Nat.lt_or_ge s (b + 1) with h | h
    · rw [if_neg (by rw [hz (b + 1) h (Nat.le_refl _)]; simp)]
      exact deepest_eq c s hs b (by omega) fun j h1 h2 => hz j h1 (by omega)
    · have : s = b + 1 := by omega
      subst this; simp [hs]

/-- One move from level `s ≤ 13`. -/
theorem repairStep_lt (c : Nat → Nat) (s : Nat) (hs13 : s ≤ 13) (hcs : 1 ≤ c s)
    (hz : ∀ j, s < j → j ≤ 14 → c j = 0) :
    repairStep 15 c = fun j => if j = s then c s - 1 else if j = s + 1 then c (s + 1) + 2
      else if j = 15 then c 15 - 1 else c j := by
  have hd : deepest c 14 = s := deepest_eq c s (by omega) 14 (by omega) hz
  have hz1 : c (s + 1) = 0 := hz (s + 1) (by omega) (by omega)
  funext j
  simp only [repairStep, updC, show 15 - 1 = 14 from rfl, hd]
  ite_omega

/-- One move from level 14. -/
theorem repairStep_14 (c : Nat → Nat) (hcs : 1 ≤ c 14) :
    repairStep 15 c = fun j => if j = 14 then c 14 - 1 else if j = 15 then c 15 + 1 else c j := by
  have hd : deepest c 14 = 14 := deepest_eq c 14 (by omega) 14 (by omega) (by intros; omega)
  funext j
  simp only [repairStep, updC, show 15 - 1 = 14 from rfl, hd]
  ite_omega

theorem two_pow_split (s : Nat) (h : s ≤ 13) : 2 ^ (15 - s) = 2 * 2 ^ (14 - s) := by
  rw [show 15 - s = (14 - s) + 1 by omega, Nat.pow_succ]; omega

theorem two_pow_14_pos (s : Nat) : 1 ≤ 2 ^ (14 - s) := Nat.one_le_two_pow

/-- The counts after one move from `s ≤ 13`. -/
def mv1 (c : Nat → Nat) (s : Nat) : Nat → Nat := fun j =>
  if j = s then c s - 1 else if j = s + 1 then c (s + 1) + 2 else if j = 15 then c 15 - 1 else c j

/-- The counts after a full expansion of one unit at `s`. -/
def fx (c : Nat → Nat) (s : Nat) : Nat → Nat := fun j =>
  if j = s then c s - 1 else if j = 15 then c 15 + 1 else c j

/-- **Lemma 5, full expansion.** -/
theorem exp_full : ∀ (k s : Nat), s + k = 14 → ∀ (c : Nat → Nat), (∀ j, s < j → j ≤ 14 → c j = 0) →
    1 ≤ c s → 2 ^ (15 - s) - 1 ≤ c 15 → repairIter 15 (2 ^ (15 - s) - 1) c = fx c s
  | 0, s, hk, c, _, hcs, _ => by
    have : s = 14 := by omega
    subst this
    show repairStep 15 c = _
    rw [repairStep_14 c hcs]; rfl
  | k + 1, s, hk, c, hz, hcs, h15 => by
    have hs : s ≤ 13 := by omega
    have hP := two_pow_split s hs
    have hP1 := two_pow_14_pos s
    have hsplit : 2 ^ (15 - s) - 1 = 1 + (2 ^ (14 - s) - 1) + (2 ^ (14 - s) - 1) := by omega
    have hs1 : 15 - (s + 1) = 14 - s := by omega
    have hz1 : c (s + 1) = 0 := hz (s + 1) (by omega) (by omega)
    rw [hsplit, repairIter_add, repairIter_add]
    have hA : repairIter 15 1 c = mv1 c s := repairStep_lt c s hs hcs hz
    rw [hA]
    have hB := exp_full k (s + 1) (by omega) (mv1 c s)
      (by intro j h1 h2; have := hz j (by omega) h2; simp only [mv1]; ite_omega)
      (by simp only [mv1]; ite_omega) (by rw [hs1]; simp only [mv1]; ite_omega)
    rw [hs1] at hB; rw [hB]
    have hC := exp_full k (s + 1) (by omega) (fx (mv1 c s) (s + 1))
      (by intro j h1 h2; have := hz j (by omega) h2; simp only [mv1, fx]; ite_omega)
      (by simp only [mv1, fx]; ite_omega) (by rw [hs1]; simp only [mv1, fx]; ite_omega)
    rw [hs1] at hC; rw [hC]
    funext j
    simp only [mv1, fx]
    ite_omega

/-- **Lemma 5, partial expansion.** -/
theorem exp_partial : ∀ (k s : Nat), s + k = 14 → ∀ (c : Nat → Nat) (t : Nat),
    (∀ j, s < j → j ≤ 14 → c j = 0) → 1 ≤ c s → 0 < t → t < 2 ^ (15 - s) - 1 → t ≤ c 15 →
    (∀ j, j < s → repairIter 15 t c j = c j) ∧ repairIter 15 t c s = c s - 1 ∧
      (t ≤ 2 ^ (14 - s) → 1 ≤ repairIter 15 t c (s + 1))
  | 0, s, hk, c, t, _, _, ht0, ht, _ => by
    have : s = 14 := by omega
    subst this; simp at ht; omega
  | k + 1, s, hk, c, t, hz, hcs, ht0, ht, h15 => by
    have hs : s ≤ 13 := by omega
    have hP := two_pow_split s hs
    have hP1 := two_pow_14_pos s
    have hs1 : 15 - (s + 1) = 14 - s := by omega
    have hz1 : c (s + 1) = 0 := hz (s + 1) (by omega) (by omega)
    obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [repairIter_add]
    have hA : repairIter 15 1 c = mv1 c s := repairStep_lt c s hs hcs hz
    rw [hA]
    have ca_lt : ∀ j, j < s → mv1 c s j = c j := by intro j hj; simp only [mv1]; ite_omega
    have ca_s : mv1 c s s = c s - 1 := by simp only [mv1]; ite_omega
    have ca_s1 : mv1 c s (s + 1) = 2 := by simp only [mv1]; ite_omega
    have ca_15 : mv1 c s 15 = c 15 - 1 := by simp only [mv1]; ite_omega
    have ca_z : ∀ j, s + 1 < j → j ≤ 14 → mv1 c s j = 0 := by
      intro j h1 h2; have := hz j (by omega) h2; simp only [mv1]; ite_omega
    rcases Nat.lt_trichotomy t' (2 ^ (14 - s) - 1) with hlt | heq | hgt
    · rcases Nat.eq_zero_or_pos t' with h0 | h0
      · subst h0
        refine ⟨ca_lt, ca_s, fun _ => ?_⟩
        simp only [repairIter]; rw [ca_s1]; omega
      · have ih := exp_partial k (s + 1) (by omega) (mv1 c s) t' ca_z (by rw [ca_s1]; omega) h0
          (by rw [hs1]; omega) (by rw [ca_15]; omega)
        refine ⟨fun j hj => (ih.1 j (by omega)).trans (ca_lt j hj), ?_, fun _ => ?_⟩
        · rw [ih.1 s (by omega), ca_s]
        · rw [ih.2.1, ca_s1]; omega
    · subst heq
      have hB := exp_full k (s + 1) (by omega) (mv1 c s) ca_z (by rw [ca_s1]; omega)
        (by rw [hs1, ca_15]; omega)
      rw [hs1] at hB; rw [hB]
      refine ⟨fun j hj => ?_, ?_, fun _ => ?_⟩
      · have := ca_lt j hj; simp only [fx]; ite_omega
      · simp only [fx]; ite_omega
      · simp only [fx]; ite_omega
    · obtain ⟨t2, rfl⟩ : ∃ t2, t' = (2 ^ (14 - s) - 1) + t2 := ⟨t' - (2 ^ (14 - s) - 1), by omega⟩
      rw [repairIter_add]
      have hB := exp_full k (s + 1) (by omega) (mv1 c s) ca_z (by rw [ca_s1]; omega)
        (by rw [hs1, ca_15]; omega)
      rw [hs1] at hB; rw [hB]
      have cb_lt : ∀ j, j < s + 1 → fx (mv1 c s) (s + 1) j = mv1 c s j := by
        intro j hj; simp only [fx]; ite_omega
      have ih := exp_partial k (s + 1) (by omega) (fx (mv1 c s) (s + 1)) t2
        (by intro j h1 h2; have := ca_z j h1 h2; simp only [fx]; ite_omega)
        (by simp only [fx]; ite_omega) (by omega) (by rw [hs1]; omega)
        (by simp only [fx]; ite_omega)
      refine ⟨fun j hj => ?_, ?_, fun h => by omega⟩
      · rw [ih.1 j (by omega), cb_lt j (by omega), ca_lt j hj]
      · rw [ih.1 s (by omega), cb_lt s (by omega), ca_s]

end Zlib.Trees.HuffmanAbstract
