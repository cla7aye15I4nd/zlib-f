import ZlibF.Math.DeflateHuffmanChain

/-!
Pure depth/height mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
Imports and namespace use this project's tree shape and clamped levels.
The modular recurrence is retained until the level bound rules out wrap.
-/

namespace Zlib.Trees.Proofs.GB

section height
variable {H : Nat → Nat} {hm J elems maxc : Nat} {dl : Nat → Nat}

/-- The internal node at position `q` (`H q = elems + i`) sits below both children. -/
theorem node_below (S : PShape H hm J elems maxc) {q i : Nat} (a : hm ≤ q) (b : q < 573) (hi : i < J)
    (e : H q = elems + i) : q < 571 - 2 * i := by
  obtain ⟨q', a', b', e'⟩ := S.appears i hi
  have := S.hm_eq
  have := S.inj q q' a b a' (by omega) (by rw [e, e'])
  omega

theorem dl_child (S : PShape H hm J elems maxc) (C : Clamped H hm J elems 1000 dl) {q i : Nat}
    (a : hm ≤ q) (b : q < 573) (e : H q = elems + i) {c : Nat} (hc : c = 572 - 2 * i ∨ c = 571 - 2 * i)
    (hcq : q < c) (hc2 : c < 573) : dl (H c) = dl (H q) + 1 := by
  have := S.hm_eq
  rw [dl_step S C (by omega) hc2]
  have hd : dadP elems c = H q := by unfold dadP; rw [e]; omega
  rw [hd]
  have := dl_le S C q a b
  omega

/-- **Upper bound**: `depth + level ≤ B` when every leaf level is `≤ B ≤ 254`. -/
theorem depth_upper (S : PShape H hm J elems maxc) (C : Clamped H hm J elems 1000 dl) (D : Nat → Nat)
    (hleaf0 : ∀ q, hm ≤ q → q < 573 → H q < elems → D (H q) = 0)
    (hdep : ∀ i < J, D (elems + i) = (max (D (H (572 - 2 * i))) (D (H (571 - 2 * i))) + 1) % 256)
    (B : Nat) (hB : B ≤ 254) (hlv : ∀ q, hm ≤ q → q < 573 → H q < elems → dl (H q) ≤ B) :
    ∀ q, hm ≤ q → q < 573 → D (H q) + dl (H q) ≤ B := by
  have hmq := S.hm_eq
  suffices h : ∀ k q, 573 - q ≤ k → hm ≤ q → q < 573 → D (H q) + dl (H q) ≤ B from
    fun q a b => h _ q (Nat.le_refl _) a b
  intro k
  induction k with
  | zero => intro q h1 _ h3; omega
  | succ k ih =>
    intro q hk a b
    rcases S.kind q a b with hl | ⟨hl1, hl2⟩
    · rw [hleaf0 q a b (by have := S.maxc_lt; omega)]
      have := hlv q a b (by have := S.maxc_lt; omega); omega
    · obtain ⟨i, hi⟩ : ∃ i, H q = elems + i := ⟨H q - elems, by omega⟩
      have hiJ : i < J := by omega
      have hb := node_below S a b hiJ hi
      have d1 := dl_child S C a b hi (Or.inl rfl) (by omega) (by omega)
      have d2 := dl_child S C a b hi (Or.inr rfl) (by omega) (by omega)
      have i1 := ih (572 - 2 * i) (by omega) (by omega) (by omega)
      have i2 := ih (571 - 2 * i) (by omega) (by omega) (by omega)
      rw [hi, hdep i hiJ, ← hi]
      have : max (D (H (572 - 2 * i))) (D (H (571 - 2 * i))) + 1 < 256 := by
        rcases Nat.le_total (D (H (572 - 2 * i))) (D (H (571 - 2 * i))) with h | h
        · rw [Nat.max_eq_right h]; omega
        · rw [Nat.max_eq_left h]; omega
      rw [Nat.mod_eq_of_lt this]
      rcases Nat.le_total (D (H (572 - 2 * i))) (D (H (571 - 2 * i))) with h | h
      · rw [Nat.max_eq_right h]; omega
      · rw [Nat.max_eq_left h]; omega

/-- **Lower bound**: the root's depth is at least `depth + level` of every node. -/
theorem depth_lower (S : PShape H hm J elems maxc) (C : Clamped H hm J elems 1000 dl) (D : Nat → Nat)
    (hleaf0 : ∀ q, hm ≤ q → q < 573 → H q < elems → D (H q) = 0)
    (hdep : ∀ i < J, D (elems + i) = (max (D (H (572 - 2 * i))) (D (H (571 - 2 * i))) + 1) % 256)
    (B : Nat) (hB : B ≤ 254) (hlv : ∀ q, hm ≤ q → q < 573 → H q < elems → dl (H q) ≤ B) :
    ∀ q, hm ≤ q → q < 573 → D (H q) + dl (H q) ≤ D (H hm) := by
  have hmq := S.hm_eq
  have hU := depth_upper S C D hleaf0 hdep B hB hlv
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro a b
    by_cases e : q = hm
    · subst e; rw [C.root]; omega
    · obtain ⟨q', a', b', c', hi⟩ := parent_pos S (q := q) (by omega) b
      have hq'q : q' < q := by omega
      have hpar : H q' = elems + (572 - q) / 2 := c'
      have hc : q = 572 - 2 * ((572 - q) / 2) ∨ q = 571 - 2 * ((572 - q) / 2) := by omega
      have hd := dl_child S C a' (by omega) hpar hc (by omega) b
      have u1 := hU (572 - 2 * ((572 - q) / 2)) (by omega) (by omega)
      have u2 := hU (571 - 2 * ((572 - q) / 2)) (by omega) (by omega)
      have hdq := hdep _ hi
      rw [← hpar] at hdq
      have : max (D (H (572 - 2 * ((572 - q) / 2)))) (D (H (571 - 2 * ((572 - q) / 2)))) + 1 < 256 := by
        rcases Nat.le_total (D (H (572 - 2 * ((572 - q) / 2)))) (D (H (571 - 2 * ((572 - q) / 2)))) with h | h
        · rw [Nat.max_eq_right h]; omega
        · rw [Nat.max_eq_left h]; omega
      rw [Nat.mod_eq_of_lt this] at hdq
      have hge : D (H q) + 1 ≤ D (H q') := by
        rw [hdq]
        have m1 := Nat.le_max_left (D (H (572 - 2 * ((572 - q) / 2)))) (D (H (571 - 2 * ((572 - q) / 2))))
        have m2 := Nat.le_max_right (D (H (572 - 2 * ((572 - q) / 2)))) (D (H (571 - 2 * ((572 - q) / 2))))
        rcases hc with hc | hc
        · have := congrArg (fun t => D (H t)) hc; omega
        · have := congrArg (fun t => D (H t)) hc; omega
      have := ih q' hq'q a' (by omega)
      omega

end height

end Zlib.Trees.Proofs.GB
