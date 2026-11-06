/-!
# deflate.c, engine: the match length of `longest_match`

For a candidate match at window position `C` and the string at `S = strstart`, `longest_match` first compares
`match[best_len]`, `match[best_len - 1]`, `match[0]`, `match[1]` with the scan; if all agree it assumes
`match[2] = scan[2]` (the hash chain guarantees this, `hkey_third`) and compares from index 3 on, up to `MAX_MATCH = 258`.
The unrolled loop compares eight positions per round and stops at the first mismatch or at `strend = S + 258`.
The length is `258 - (strend - scan)`, that is the scan offset at which the loop stopped.

`firstMis w S C j` is that offset when the loop is at offset `j - 1` and no position below `j` is known to
differ: the first `k >= j` below 258 where the two strings differ, or 258. `firstMis_spec` is the characterisation
the heap proof of the loop maintains step by step.
-/

namespace Zlib.Deflate.Engine.Proofs

/-- The first `k` with `j <= k < 258` where `w (S + k) != w (C + k)`, or `258` when there is none. -/
def firstMis (w : Nat → UInt8) (S C j : Nat) : Nat :=
  if h : j < 258 then (if w (S + j) = w (C + j) then firstMis w S C (j + 1) else j) else 258
termination_by 258 - j

theorem firstMis_ge (w : Nat → UInt8) (S C : Nat) : ∀ n j, 258 - j = n → j ≤ 258 → j ≤ firstMis w S C j := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j hn hj
    unfold firstMis
    split
    · rename_i h
      split
      · have := ih (258 - (j + 1)) (by omega) (j + 1) rfl (by omega)
        omega
      · omega
    · omega

theorem firstMis_le (w : Nat → UInt8) (S C : Nat) : ∀ n j, 258 - j = n → firstMis w S C j ≤ 258 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j hn
    unfold firstMis
    split
    · rename_i h
      split
      · exact ih (258 - (j + 1)) (by omega) (j + 1) rfl
      · omega
    · omega

/-- The characterisation of `firstMis`: the strings agree on `[j, r)` and, when `r < 258`, differ at `r`. -/
theorem firstMis_spec (w : Nat → UInt8) (S C : Nat) : ∀ n j, 258 - j = n → j ≤ 258 →
    (∀ k, j ≤ k → k < firstMis w S C j → w (S + k) = w (C + k)) ∧
    (firstMis w S C j < 258 → w (S + firstMis w S C j) ≠ w (C + firstMis w S C j)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j hn hj
    have e : firstMis w S C j = if j < 258 then (if w (S + j) = w (C + j) then firstMis w S C (j + 1) else j) else 258 := by
      rw [firstMis]; rfl
    by_cases h : j < 258
    · by_cases hw : w (S + j) = w (C + j)
      · have e2 : firstMis w S C j = firstMis w S C (j + 1) := by rw [e]; simp [h, hw]
        obtain ⟨a, b⟩ := ih (258 - (j + 1)) (by omega) (j + 1) rfl (by omega)
        rw [e2]
        refine ⟨fun k hk1 hk2 => ?_, b⟩
        by_cases hkj : k = j
        · subst hkj; exact hw
        · exact a k (by omega) hk2
      · have e2 : firstMis w S C j = j := by rw [e]; simp [h, hw]
        rw [e2]
        exact ⟨fun k hk1 hk2 => by omega, fun _ => hw⟩
    · have e2 : firstMis w S C j = 258 := by rw [e]; simp [h]
      rw [e2]
      exact ⟨fun k hk1 hk2 => by omega, fun h' => by omega⟩

/-- The scan offset the loop reaches is determined by agreement below it and disagreement at it: if the strings
agree on `[j, r)`, `j <= r <= 258`, and differ at `r` when `r < 258`, then `r = firstMis j`. -/
theorem firstMis_unique (w : Nat → UInt8) (S C : Nat) {j r : Nat} (hj : j ≤ r) (hr : r ≤ 258)
    (hag : ∀ k, j ≤ k → k < r → w (S + k) = w (C + k)) (hst : r < 258 → w (S + r) ≠ w (C + r)) :
    firstMis w S C j = r := by
  obtain ⟨a, b⟩ := firstMis_spec w S C _ j rfl (by omega)
  have hge := firstMis_ge w S C _ j rfl (by omega)
  have hle := firstMis_le w S C _ j rfl
  refine Classical.byContradiction fun hne => ?_
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact b (by omega) (hag _ hge hlt)
  · by_cases h258 : r < 258
    · exact hst h258 (a r hj hgt)
    · omega

/-- The length that `longest_match` computes for a candidate that passed the four early tests and whose third
byte agrees: `firstMis` from index 3. It is at least 3 and at most 258, and the strings agree on `[0, len)`
given they agree on `[0, 3)`. -/
def matchLen (w : Nat → UInt8) (S C : Nat) : Nat := firstMis w S C 3

theorem matchLen_bounds (w : Nat → UInt8) (S C : Nat) : 3 ≤ matchLen w S C ∧ matchLen w S C ≤ 258 :=
  ⟨firstMis_ge w S C _ 3 rfl (by omega), firstMis_le w S C _ 3 rfl⟩

theorem matchLen_agree (w : Nat → UInt8) (S C : Nat)
    (h0 : w S = w C) (h1 : w (S + 1) = w (C + 1)) (h2 : w (S + 2) = w (C + 2)) :
    ∀ j, j < matchLen w S C → w (S + j) = w (C + j) := by
  intro j hj
  by_cases h3 : j < 3
  · obtain h | h | h : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · subst h; simpa using h0
    · subst h; exact h1
    · subst h; exact h2
  · exact (firstMis_spec w S C _ 3 rfl (by omega)).1 j (by omega) hj

theorem matchLen_stop (w : Nat → UInt8) (S C : Nat) (h : matchLen w S C < 258) :
    w (S + matchLen w S C) ≠ w (C + matchLen w S C) :=
  (firstMis_spec w S C _ 3 rfl (by omega)).2 h

/-! ## The best length

`best_len` only grows, and only to a length the loop measured. The cap at `lookahead` at the end keeps a
returned length below the valid data. -/

/-- The result `longest_match` returns: `best_len` if it is at most `lookahead`, else `lookahead`. -/
def lmResult (best la : Nat) : Nat := if best ≤ la then best else la

theorem lmResult_le (best la : Nat) : lmResult best la ≤ best ∧ lmResult best la ≤ la := by
  unfold lmResult; split <;> omega

end Zlib.Deflate.Engine.Proofs
