/-!
# inftrees.c: the arithmetic of canonical codes

Statements about natural numbers that the proofs about `inflate_table` use: bit reversal (`huff` is the reversed
canonical code), the step that computes the reversed successor, the Kraft sums, and the canonical code values of
the symbols sorted by length. Nothing here mentions the heap or the translation.
-/

namespace Zlib.Inftrees.Proofs

/-! ### Bit reversal -/

/-- The `n` low bits of `v` in reverse order. -/
def rev : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => (v % 2) * 2 ^ n + rev n (v / 2)

theorem rev_lt : ∀ n v, rev n v < 2 ^ n
  | 0, _ => by simp [rev]
  | n + 1, v => by
    have := rev_lt n (v / 2)
    simp only [rev, Nat.pow_succ]
    have : v % 2 ≤ 1 := by omega
    have h2 : v % 2 * 2 ^ n ≤ 2 ^ n := by
      calc v % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ this
        _ = 2 ^ n := by simp
    omega

theorem rev_mul_pow : ∀ k n w, rev (n + k) (w * 2 ^ k) = rev n w
  | 0, n, w => by simp
  | k + 1, n, w => by
    have e : n + (k + 1) = (n + k) + 1 := by omega
    rw [e, rev]
    have h1 : w * 2 ^ (k + 1) % 2 = 0 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; simp [Nat.mul_mod_left]
    have h2 : w * 2 ^ (k + 1) / 2 = w * 2 ^ k := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by omega)]
    rw [h1, h2, rev_mul_pow k n w]; simp

theorem rev_mod_pow : ∀ d R v, rev (R + d) v % 2 ^ R = rev R (v / 2 ^ d)
  | 0, R, v => by
    simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (rev_lt R v)
  | d + 1, R, v => by
    have e : R + (d + 1) = (R + d) + 1 := by omega
    rw [e, rev]
    have hR : 2 ^ R ∣ 2 ^ (R + d) := Nat.pow_dvd_pow 2 (by omega)
    have h0 : v % 2 * 2 ^ (R + d) % 2 ^ R = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact Nat.dvd_trans hR (Nat.dvd_mul_left _ _)
    rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, rev_mod_pow d R (v / 2)]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (2 ^ d) 2]

theorem rev_inj : ∀ n a b, rev n a = rev n b → a % 2 ^ n = b % 2 ^ n
  | 0, a, b, _ => by simp [Nat.mod_one]
  | n + 1, a, b, h => by
    simp only [rev] at h
    have ha := rev_lt n (a / 2)
    have hb := rev_lt n (b / 2)
    have h1 : a % 2 = b % 2 := by
      have : a % 2 < 2 := by omega
      have : b % 2 < 2 := by omega
      rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with h2 | h2 <;>
        rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with h3 | h3 <;>
        simp [h2, h3] at h <;> omega
    rw [h1] at h
    have h2 : rev n (a / 2) = rev n (b / 2) := by omega
    have := rev_inj n _ _ h2
    have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [e, Nat.mod_mul, Nat.mod_mul]
    rw [h1, this]


/-! ### The step of `huff`

`incr = 1U << e; while (huff & incr) incr >>= 1;` ends with `incr = incrLoop huff e` (0 if every bit down to bit 0
is set). -/

def incrLoop (h : Nat) : Nat → Nat
  | 0 => if h.testBit 0 then 0 else 1
  | e + 1 => if h.testBit (e + 1) then incrLoop h e else 2 ^ (e + 1)

theorem incrLoop_mod : ∀ e h, incrLoop h e = incrLoop (h % 2 ^ (e + 1)) e
  | 0, h => by simp [incrLoop]
  | e + 1, h => by
    simp only [incrLoop, Nat.testBit_mod_two_pow]
    have := incrLoop_mod e h
    have h2 := incrLoop_mod e (h % 2 ^ (e + 1 + 1))
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))] at h2
    simp [this, h2]

/-- Adding one to a number of `n + 1` bits, in the reversed representation. -/
theorem succ_rev : ∀ n v, v < 2 ^ (n + 1) →
    (v + 1 < 2 ^ (n + 1) → ∃ e ≤ n, incrLoop (rev (n + 1) v) n = 2 ^ e ∧
        rev (n + 1) v % 2 ^ e + 2 ^ e = rev (n + 1) (v + 1)) ∧
    (v + 1 = 2 ^ (n + 1) → incrLoop (rev (n + 1) v) n = 0)
  | 0, v, hv => by
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · have : v = 0 := by simp at hv h1; omega
      subst this
      refine ⟨0, Nat.le_refl _, ?_, ?_⟩ <;> simp [rev, incrLoop]
    · have : v = 1 := by simp at h1; omega
      subst this
      simp [rev, incrLoop]
  | n + 1, v, hv => by
    have hlt := rev_lt (n + 1) (v / 2)
    have hP : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hP' : 0 < 2 ^ (n + 1) := Nat.pow_pos (by omega)
    have hrv : ∀ x, rev (n + 1 + 1) x = x % 2 * 2 ^ (n + 1) + rev (n + 1) (x / 2) := fun x => rfl
    have ih := succ_rev n (v / 2) (by omega)
    rcases (by omega : v % 2 = 0 ∨ v % 2 = 1) with h0 | h0
    · -- the top bit is 0: incr stops at once
      have hh : rev (n + 1 + 1) v = rev (n + 1) (v / 2) := by rw [hrv, h0]; simp
      have hbit : (rev (n + 1 + 1) v).testBit (n + 1) = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        rw [hh]
        have : rev (n + 1) (v / 2) / 2 ^ (n + 1) = 0 := Nat.div_eq_of_lt hlt
        simp [this]
      have hv1 : rev (n + 1 + 1) (v + 1) = 2 ^ (n + 1) + rev (n + 1) (v / 2) := by
        rw [hrv]
        have : (v + 1) % 2 = 1 := by omega
        have : (v + 1) / 2 = v / 2 := by omega
        simp [*]
      refine ⟨fun _ => ⟨n + 1, Nat.le_refl _, ?_, ?_⟩, fun h1 => by omega⟩
      · simp [incrLoop, hbit]
      · rw [hv1, hh]
        have : rev (n + 1) (v / 2) % 2 ^ (n + 1) = rev (n + 1) (v / 2) := Nat.mod_eq_of_lt hlt
        omega
    · -- the top bit is 1: look at the lower bits
      have hh : rev (n + 1 + 1) v = 2 ^ (n + 1) + rev (n + 1) (v / 2) := by rw [hrv, h0]; simp
      have hbit : (rev (n + 1 + 1) v).testBit (n + 1) = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, hh]
        have : (2 ^ (n + 1) + rev (n + 1) (v / 2)) / 2 ^ (n + 1) = 1 := by
          rw [Nat.add_comm, Nat.add_div_right _ hP', Nat.div_eq_of_lt hlt]
        simp [this]
      have hmod : rev (n + 1 + 1) v % 2 ^ (n + 1) = rev (n + 1) (v / 2) := by
        rw [hh, Nat.add_comm, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hlt
      have hloop : incrLoop (rev (n + 1 + 1) v) (n + 1) = incrLoop (rev (n + 1) (v / 2)) n := by
        simp only [incrLoop, hbit, ite_true]
        rw [incrLoop_mod n (rev (n + 1 + 1) v), hmod]
      have hv1 : rev (n + 1 + 1) (v + 1) = rev (n + 1) (v / 2 + 1) := by
        rw [hrv]
        have : (v + 1) % 2 = 0 := by omega
        have : (v + 1) / 2 = v / 2 + 1 := by omega
        simp [*]
      refine ⟨fun h1 => ?_, fun h1 => ?_⟩
      · obtain ⟨e, he, h2, h3⟩ := ih.1 (by omega)
        refine ⟨e, by omega, by rw [hloop]; exact h2, ?_⟩
        rw [hv1, ← h3, hh]
        have hd : 2 ^ e ∣ 2 ^ (n + 1) := Nat.pow_dvd_pow 2 (by omega)
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.zero_add, Nat.mod_mod]
      · rw [hloop]; exact ih.2 (by omega)


/-! ### The symbols sorted by length

`f s` is the length of symbol `s` (`lens[s]`); the first `n` symbols are the ones the call looks at. -/

section Model
variable (f : Nat → Nat) (n : Nat)

/-- The symbols below `k` of length `l`, in increasing order. -/
def fl (l k : Nat) : List Nat := (List.range k).filter (fun s => f s == l)

/-- `count[l]` after the counting loop has looked at the symbols below `n`. -/
def cnt (l : Nat) : Nat := (fl f l n).length

/-- `work[0 ..]` after the sort loop, for the lengths `1 .. l`: the symbols sorted by (length, symbol). -/
def wsAux : Nat → List Nat
  | 0 => []
  | l + 1 => wsAux l ++ fl f (l + 1) n

/-- The number of symbols of length at most `l` (and at least 1). -/
def Tc : Nat → Nat
  | 0 => 0
  | l + 1 => Tc l + cnt f n (l + 1)

/-- Kraft: `K l = sum_{j <= l} cnt j 2^(l - j)`; `2^l - K l` is the C variable `left` after step `l`. -/
def Kc : Nat → Nat
  | 0 => 0
  | l + 1 => 2 * Kc l + cnt f n (l + 1)

/-- `lens[work[i]]` once the sort loop is done. -/
def lenAt (i : Nat) : Nat := f ((wsAux f n 15).getD i 0)

/-- The canonical code of the `i`-th symbol in the sorted order (RFC 1951, 3.2.2): the `k`-th of length `l` is
`2 K(l-1) + k`. -/
def val (i : Nat) : Nat := 2 * Kc f n (lenAt f n i - 1) + (i - Tc f n (lenAt f n i - 1))

variable {f n}

theorem mem_fl {l k x : Nat} : x ∈ fl f l k ↔ x < k ∧ f x = l := by
  simp [fl]

theorem wsAux_length : ∀ l, (wsAux f n l).length = Tc f n l
  | 0 => rfl
  | l + 1 => by simp [wsAux, Tc, cnt, wsAux_length l]

theorem mem_wsAux : ∀ {l x}, x ∈ wsAux f n l ↔ x < n ∧ 1 ≤ f x ∧ f x ≤ l
  | 0, x => by simp [wsAux]; omega
  | l + 1, x => by
    simp only [wsAux, List.mem_append, mem_fl, mem_wsAux (l := l)]
    omega

theorem wsAux_split {l L : Nat} (h : l ≤ L) : ∃ rest, wsAux f n L = wsAux f n l ++ rest ∧ ∀ x ∈ rest, l < f x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ d ih =>
    obtain ⟨rest, h1, h2⟩ := ih (by omega)
    refine ⟨rest ++ fl f (l + d + 1) n, by simp [wsAux, h1], ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h2 x hx
    · have := (mem_fl.mp hx).2; omega

theorem Tc_mono {a b : Nat} (h : a ≤ b) : Tc f n a ≤ Tc f n b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := ih (by omega)
    show Tc f n a ≤ Tc f n (a + d) + cnt f n (a + d + 1)
    omega

/-- For `i < T 15` and `l <= 15`: the `i`-th symbol has length at most `l` iff `i < T l`. -/
theorem lenAt_le_iff {i l : Nat} (hl : l ≤ 15) (hi : i < Tc f n 15) : lenAt f n i ≤ l ↔ i < Tc f n l := by
  obtain ⟨rest, h1, h2⟩ := wsAux_split (f := f) (n := n) hl
  have hlen : (wsAux f n l).length = Tc f n l := wsAux_length l
  unfold lenAt
  rw [h1]
  by_cases hil : i < Tc f n l
  · have hi' : i < (wsAux f n l).length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi', List.getElem?_eq_getElem hi']
    have hm := List.getElem_mem hi'
    have := (mem_wsAux.mp hm).2.2
    simp only [Option.getD_some]
    constructor <;> intro _ <;> omega
  · have hge : (wsAux f n l).length ≤ i := by omega
    have hi2 : i - (wsAux f n l).length < rest.length := by
      have := wsAux_length (f := f) (n := n) 15
      rw [h1, List.length_append] at this; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, List.getElem?_eq_getElem hi2]
    have hm := List.getElem_mem hi2
    have := h2 _ hm
    simp only [Option.getD_some]
    constructor <;> intro _ <;> omega

theorem lenAt_bounds {i : Nat} (hi : i < Tc f n 15) :
    1 ≤ lenAt f n i ∧ lenAt f n i ≤ 15 := by
  have hlen : (wsAux f n 15).length = Tc f n 15 := wsAux_length 15
  have hm := List.getElem_mem (show i < (wsAux f n 15).length by omega)
  have := mem_wsAux.mp hm
  unfold lenAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  omega

/-- The block of lengths: `T(l-1) <= i < T l` iff the `i`-th symbol has length `l`. -/
theorem lenAt_eq_iff {i l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ 15) (hi : i < Tc f n 15) :
    lenAt f n i = l ↔ Tc f n (l - 1) ≤ i ∧ i < Tc f n l := by
  have a := lenAt_le_iff (f := f) (n := n) hl hi
  have b := lenAt_le_iff (f := f) (n := n) (l := l - 1) (by omega) hi
  omega

theorem lenAt_mono {i j : Nat} (hij : i ≤ j) (hj : j < Tc f n 15) :
    lenAt f n i ≤ lenAt f n j := by
  have hi : i < Tc f n 15 := by omega
  obtain ⟨b1, b2⟩ := lenAt_bounds hj
  have a := (lenAt_le_iff (f := f) (n := n) (l := lenAt f n j - 1) (by omega) hj)
  have b := (lenAt_le_iff (f := f) (n := n) (l := lenAt f n j) b2 hi)
  have c := (lenAt_le_iff (f := f) (n := n) (l := lenAt f n j) b2 hj)
  by_cases h : lenAt f n i ≤ lenAt f n j
  · exact h
  · exfalso
    -- i is not in the block of lengths <= len j, so j (later) is not either
    have : ¬ i < Tc f n (lenAt f n j) := fun h' => h (b.mpr h')
    have := c.mp (Nat.le_refl _)
    omega


theorem Tc_succ' {l : Nat} (hl : 1 ≤ l) : Tc f n l = Tc f n (l - 1) + cnt f n l := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp [Tc]

theorem Kc_succ' {l : Nat} (hl : 1 ≤ l) : Kc f n l = 2 * Kc f n (l - 1) + cnt f n l := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp [Kc]

theorem Kc_gap : ∀ a d, Tc f n (a + d) = Tc f n a → Kc f n (a + d) = 2 ^ d * Kc f n a
  | a, 0, _ => by simp
  | a, d + 1, h => by
    have m1 := Tc_mono (f := f) (n := n) (show a ≤ a + d by omega)
    have e : Tc f n (a + d + 1) = Tc f n (a + d) + cnt f n (a + d + 1) := rfl
    have h1 : Tc f n (a + d) = Tc f n a := by
      have : a + (d + 1) = a + d + 1 := by omega
      rw [this] at h; omega
    have h2 : cnt f n (a + d + 1) = 0 := by
      have : a + (d + 1) = a + d + 1 := by omega
      rw [this] at h; omega
    have ih := Kc_gap a d h1
    have : a + (d + 1) = a + d + 1 := by omega
    rw [this]
    show 2 * Kc f n (a + d) + cnt f n (a + d + 1) = _
    rw [h2, ih, Nat.pow_succ]
    have : 2 ^ d * 2 * Kc f n a = 2 * (2 ^ d * Kc f n a) := by rw [Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    omega

/-- No code overflows its length (RFC 1951; `F-code-fits`). -/
def Fits (f : Nat → Nat) (n : Nat) : Prop := ∀ l, 1 ≤ l → l ≤ 15 → Kc f n l ≤ 2 ^ l

theorem val_lt (hfit : Fits f n) {i : Nat} (hi : i < Tc f n 15) : val f n i < 2 ^ lenAt f n i := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi
  have := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n i) b1 b2 hi).mp rfl
  have t := Tc_succ' (f := f) (n := n) b1
  have k := Kc_succ' (f := f) (n := n) b1
  have := hfit _ b1 b2
  unfold val
  omega

theorem val_succ {i : Nat} (hi : i + 1 < Tc f n 15) :
    val f n (i + 1) = (val f n i + 1) * 2 ^ (lenAt f n (i + 1) - lenAt f n i) := by
  have hi0 : i < Tc f n 15 := by omega
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi0
  obtain ⟨c1, c2⟩ := lenAt_bounds (f := f) (n := n) hi
  have mono := lenAt_mono (f := f) (n := n) (show i ≤ i + 1 by omega) hi
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n i) b1 b2 hi0).mp rfl
  have blk' := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n (i + 1)) c1 c2 hi).mp rfl
  have t := Tc_succ' (f := f) (n := n) b1
  have k := Kc_succ' (f := f) (n := n) b1
  rcases Nat.eq_or_lt_of_le mono with heq | hlt
  · rw [heq] at blk ⊢
    simp only [val, heq, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    omega
  · -- the symbol i is the last of its length
    have hge : Tc f n (lenAt f n i) ≤ i + 1 := by
      by_cases hc : Tc f n (lenAt f n i) ≤ i + 1
      · exact hc
      · have := (lenAt_le_iff (f := f) (n := n) (l := lenAt f n i) b2 hi).mpr (by omega)
        omega
    have hT : Tc f n (lenAt f n (i + 1) - 1) = Tc f n (lenAt f n i) := by
      have := Tc_mono (f := f) (n := n) (show lenAt f n i ≤ lenAt f n (i + 1) - 1 by omega)
      omega
    have hg := Kc_gap (f := f) (n := n) (lenAt f n i) (lenAt f n (i + 1) - 1 - lenAt f n i)
      (by have e : lenAt f n i + (lenAt f n (i + 1) - 1 - lenAt f n i) = lenAt f n (i + 1) - 1 := by omega
          rw [e]; exact hT)
    have e : lenAt f n i + (lenAt f n (i + 1) - 1 - lenAt f n i) = lenAt f n (i + 1) - 1 := by omega
    rw [e] at hg
    have ep : lenAt f n (i + 1) - lenAt f n i = (lenAt f n (i + 1) - 1 - lenAt f n i) + 1 := by omega
    have hKl : Kc f n (lenAt f n i) = 2 * Kc f n (lenAt f n i - 1) + cnt f n (lenAt f n i) := k
    unfold val
    rw [ep, Nat.pow_succ, hg, hT]
    have : i + 1 - Tc f n (lenAt f n i) = 0 := by omega
    rw [this]
    have h3 : (2 * Kc f n (lenAt f n i - 1) + (i - Tc f n (lenAt f n i - 1)) + 1) = Kc f n (lenAt f n i) := by omega
    rw [h3]
    generalize 2 ^ (lenAt f n (i + 1) - 1 - lenAt f n i) = P
    generalize Kc f n (lenAt f n i) = KK
    simp only [Nat.add_zero]
    rw [Nat.mul_comm KK, Nat.mul_assoc, Nat.mul_left_comm]

/-- The last code of a complete code is all ones. -/
theorem val_last (hc : Kc f n 15 = 2 ^ 15) {m : Nat} (hm : Tc f n 15 = m + 1) :
    val f n m + 1 = 2 ^ lenAt f n m := by
  have hi : m < Tc f n 15 := by omega
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n m) b1 b2 hi).mp rfl
  have t := Tc_succ' (f := f) (n := n) b1
  have k := Kc_succ' (f := f) (n := n) b1
  have hTl : Tc f n (lenAt f n m) = Tc f n 15 := by
    have := Tc_mono (f := f) (n := n) b2
    omega
  have hg := Kc_gap (f := f) (n := n) (lenAt f n m) (15 - lenAt f n m)
    (by have e : lenAt f n m + (15 - lenAt f n m) = 15 := by omega
        rw [e]; exact hTl.symm)
  have e : lenAt f n m + (15 - lenAt f n m) = 15 := by omega
  rw [e, hc] at hg
  have hp : 2 ^ 15 = 2 ^ (15 - lenAt f n m) * 2 ^ lenAt f n m := by
    rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (15 - lenAt f n m) := Nat.pow_pos (by omega)
  have hK : Kc f n (lenAt f n m) = 2 ^ lenAt f n m := by
    rw [hp] at hg
    exact (Nat.eq_of_mul_eq_mul_left hpos hg).symm
  unfold val
  omega


/-- `count[l]` once the symbols before the `i`-th (in the sorted order) have been taken off. -/
def rem (f : Nat → Nat) (n i l : Nat) : Nat := Tc f n l - max i (Tc f n (l - 1))

theorem rem_zero {l : Nat} (hl : 1 ≤ l) : rem f n 0 l = cnt f n l := by
  have := Tc_succ' (f := f) (n := n) hl
  unfold rem; omega

/-- Taking off the `i`-th symbol lowers the count of its length by one and changes no other. -/
theorem rem_succ {i l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ 15) (hi : i < Tc f n 15) :
    rem f n (i + 1) l = rem f n i l - (if lenAt f n i = l then 1 else 0) := by
  have a := lenAt_eq_iff (f := f) (n := n) (l := l) hl1 hl hi
  have m1 := Tc_mono (f := f) (n := n) (show l - 1 ≤ l by omega)
  unfold rem
  by_cases h : lenAt f n i = l
  · have := a.mp h
    simp only [h, ite_true]
    omega
  · simp only [h, ite_false]
    have : ¬ (Tc f n (l - 1) ≤ i ∧ i < Tc f n l) := fun hh => h (a.mpr hh)
    omega

/-! ### The sub-table sizing loop -/

/-- `while (R + curr < mx) { left -= r[R + curr]; if (left <= 0) break; curr++; left <<= 1; }` with a fuel. -/
def sizeLoop (r : Nat → Nat) (R mx : Nat) : Nat → Nat → Int → Nat × Int
  | 0, curr, left => (curr, left)
  | k + 1, curr, left =>
    if R + curr < mx then
      if left - (r (R + curr) : Int) ≤ 0 then (curr, left - (r (R + curr) : Int))
      else sizeLoop r R mx k (curr + 1) ((left - (r (R + curr) : Int)) * 2)
    else (curr, left)

/-- The sizing loop started at `curr` with just enough fuel. -/
def SL (r : Nat → Nat) (R mx curr : Nat) (left : Int) : Nat × Int := sizeLoop r R mx (mx - R - curr) curr left

theorem SL_lt {r : Nat → Nat} {R mx curr : Nat} {left : Int} (h : R + curr < mx) :
    SL r R mx curr left =
      (if left - (r (R + curr) : Int) ≤ 0 then (curr, left - (r (R + curr) : Int))
       else SL r R mx (curr + 1) ((left - (r (R + curr) : Int)) * 2)) := by
  obtain ⟨k, hk⟩ : ∃ k, mx - R - curr = k + 1 := ⟨mx - R - curr - 1, by omega⟩
  have hk2 : mx - R - (curr + 1) = k := by omega
  unfold SL
  rw [hk, hk2]
  simp only [sizeLoop, h, ite_true]

theorem SL_ge {r : Nat → Nat} {R mx curr : Nat} {left : Int} (h : mx ≤ R + curr) :
    SL r R mx curr left = (curr, left) := by
  have : mx - R - curr = 0 := by omega
  unfold SL
  rw [this]
  simp only [sizeLoop]

theorem sizeLoop_spec (r N : Nat → Nat) (R mx p d0 : Nat) (hN : ∀ d, d0 ≤ d → N (d + 1) = 2 * (N d + r d)) :
    ∀ k curr left, d0 ≤ R + curr → R + curr ≤ mx → mx - (R + curr) ≤ k →
      left = ((p + 1) * 2 ^ curr : Nat) - (N (R + curr) : Int) →
      curr ≤ (sizeLoop r R mx k curr left).1 ∧ R + (sizeLoop r R mx k curr left).1 ≤ mx ∧
      (R + (sizeLoop r R mx k curr left).1 = mx ∨
        (p + 1) * 2 ^ (sizeLoop r R mx k curr left).1 ≤ N (R + (sizeLoop r R mx k curr left).1) +
          r (R + (sizeLoop r R mx k curr left).1))
  | 0, curr, left, h0, h1, h2, h3 => by
    simp only [sizeLoop]; omega
  | k + 1, curr, left, h0, h1, h2, h3 => by
    simp only [sizeLoop]
    by_cases hc : R + curr < mx
    · simp only [hc, ite_true]
      by_cases hb : left - (r (R + curr) : Int) ≤ 0
      · simp only [hb, ite_true]
        refine ⟨Nat.le_refl _, h1, Or.inr ?_⟩
        rw [h3] at hb
        omega
      · simp only [hb, ite_false]
        have := sizeLoop_spec r N R mx p d0 hN k (curr + 1) ((left - (r (R + curr) : Int)) * 2)
          (by omega) (by omega) (by omega) (by
            have e : R + (curr + 1) = (R + curr) + 1 := by omega
            rw [e, hN _ h0, h3, Nat.pow_succ]
            push_cast
            rw [← Int.mul_assoc]
            omega)
        omega
    · simp only [hc, ite_false]
      omega


/-- The first `R` bits of the `j`-th code, when it is longer than `R` (the index of its root entry, before reversal). -/
def pre (f : Nat → Nat) (n R j : Nat) : Nat := val f n j / 2 ^ (lenAt f n j - R)

/-- `max`: the longest length. -/
def mxl (f : Nat → Nat) (n : Nat) : Nat := lenAt f n (Tc f n 15 - 1)

/-- The sub-table sized when the code `i0` (longer than `R` bits, and the first with its prefix) opens a table:
`curr` after the loop. -/
def currOf (f : Nat → Nat) (n R i0 : Nat) : Nat :=
  (SL (rem f n i0) R (mxl f n) (lenAt f n i0 - R) ((2 ^ (lenAt f n i0 - R) : Nat) : Int)).1

theorem block_bound {R i0 : Nat} (hi0 : i0 < Tc f n 15) (hR : R < lenAt f n i0)
    (halign : val f n i0 % 2 ^ (lenAt f n i0 - R) = 0) :
    lenAt f n i0 ≤ R + currOf f n R i0 ∧ R + currOf f n R i0 ≤ mxl f n ∧
    ∀ j, j < Tc f n 15 → R < lenAt f n j → pre f n R j = pre f n R i0 →
      lenAt f n j ≤ R + currOf f n R i0 := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi0
  have hm : 0 < Tc f n 15 := by omega
  have hmx : lenAt f n i0 ≤ mxl f n := lenAt_mono (f := f) (n := n) (show i0 ≤ Tc f n 15 - 1 by omega) (by omega)
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n i0) b1 b2 hi0).mp rfl
  have t0 := Tc_succ' (f := f) (n := n) b1
  have k0 := Kc_succ' (f := f) (n := n) b1
  generalize hl0 : lenAt f n i0 = ℓ0 at *
  generalize hv0 : val f n i0 = v0 at *
  have hv0def : v0 = 2 * Kc f n (ℓ0 - 1) + (i0 - Tc f n (ℓ0 - 1)) := by
    rw [← hv0, ← hl0]; rfl
  obtain ⟨p, hp⟩ : ∃ p, v0 = p * 2 ^ (ℓ0 - R) := ⟨v0 / 2 ^ (ℓ0 - R), (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero halign)).symm⟩
  have hpos : 0 < 2 ^ (ℓ0 - R) := Nat.pow_pos (by omega)
  have hpdef : pre f n R i0 = p := by
    unfold pre; rw [hl0, hv0, hp]; exact Nat.mul_div_cancel _ hpos
  let N : Nat → Nat := fun d => if d ≤ ℓ0 then v0 else 2 * Kc f n (d - 1)
  have hNgt : ∀ d, ℓ0 < d → N d = 2 * Kc f n (d - 1) := fun d h => by
    simp only [N]; rw [ite_eq_right (by omega)]
  have hNle : ∀ d, d ≤ ℓ0 → N d = v0 := fun d h => by
    simp only [N]; rw [ite_eq_left h]
  have hN : ∀ d, ℓ0 ≤ d → N (d + 1) = 2 * (N d + rem f n i0 d) := by
    intro d hd
    rcases Nat.eq_or_lt_of_le hd with h | h
    · subst h
      have : N (ℓ0 + 1) = 2 * Kc f n ℓ0 := by rw [hNgt _ (by omega)]; rfl
      have h2 : N ℓ0 = v0 := hNle _ (Nat.le_refl _)
      have h3 : rem f n i0 ℓ0 = Tc f n ℓ0 - i0 := by unfold rem; omega
      rw [this, h2, h3]; omega
    · have e1 : N (d + 1) = 2 * Kc f n d := by rw [hNgt _ (by omega)]; rfl
      have e2 : N d = 2 * Kc f n (d - 1) := hNgt _ h
      have hd1 : 1 ≤ d := by omega
      have h3 : rem f n i0 d = cnt f n d := by
        have := Tc_mono (f := f) (n := n) (show ℓ0 ≤ d - 1 by omega)
        have := Tc_succ' (f := f) (n := n) hd1
        unfold rem; omega
      rw [e1, e2, h3, Kc_succ' (f := f) (n := n) hd1]
  have spec := sizeLoop_spec (rem f n i0) N R (mxl f n) p ℓ0 hN (mxl f n - R - (ℓ0 - R)) (ℓ0 - R) ((2 ^ (ℓ0 - R) : Nat) : Int)
    (by omega) (by omega) (by omega) (by
      have : N (R + (ℓ0 - R)) = v0 := hNle _ (by omega)
      rw [this, hp]
      push_cast
      rw [Int.add_mul, Int.one_mul]; omega)
  unfold currOf SL
  rw [hl0]
  generalize hc : (sizeLoop (rem f n i0) R (mxl f n) (mxl f n - R - (ℓ0 - R)) (ℓ0 - R) ((2 ^ (ℓ0 - R) : Nat) : Int)).1 = c' at spec ⊢
  obtain ⟨s1, s2, s3⟩ := spec
  refine ⟨by omega, s2, ?_⟩
  intro j hj hRj hpre
  by_cases hle : lenAt f n j ≤ R + c'
  · exact hle
  exfalso
  obtain ⟨j1, j2⟩ := lenAt_bounds (f := f) (n := n) hj
  have hjm : lenAt f n j ≤ mxl f n := lenAt_mono (f := f) (n := n) (show j ≤ Tc f n 15 - 1 by omega) (by omega)
  have hbrk : (p + 1) * 2 ^ c' ≤ N (R + c') + rem f n i0 (R + c') := by
    rcases s3 with h | h
    · omega
    · exact h
  -- N grows past the end of the sub-tree of `p`
  have grow : ∀ t, (p + 1) * 2 ^ (c' + 1 + t) ≤ N (R + c' + 1 + t) := by
    intro t
    induction t with
    | zero =>
      have := hN (R + c') (by omega)
      have e : (p + 1) * 2 ^ (c' + 1 + 0) = 2 * ((p + 1) * 2 ^ c') := by
        rw [Nat.add_zero, Nat.pow_succ, Nat.mul_comm (2 ^ c') 2, ← Nat.mul_assoc, Nat.mul_comm (p + 1) 2, Nat.mul_assoc]
      rw [e]; simp only [Nat.add_zero]; omega
    | succ t ih =>
      have := hN (R + c' + 1 + t) (by omega)
      have e : (p + 1) * 2 ^ (c' + 1 + (t + 1)) = 2 * ((p + 1) * 2 ^ (c' + 1 + t)) := by
        rw [← Nat.add_assoc, Nat.pow_succ, Nat.mul_comm (2 ^ (c' + 1 + t)) 2, ← Nat.mul_assoc, Nat.mul_comm (p + 1) 2, Nat.mul_assoc]
      have e2 : R + c' + 1 + (t + 1) = R + c' + 1 + t + 1 := by omega
      rw [e2, this, e]; omega
  have hg := grow (lenAt f n j - (R + c') - 1)
  have e3 : R + c' + 1 + (lenAt f n j - (R + c') - 1) = lenAt f n j := by omega
  have e4 : c' + 1 + (lenAt f n j - (R + c') - 1) = lenAt f n j - R := by omega
  rw [e3, e4] at hg
  have hNj : N (lenAt f n j) = 2 * Kc f n (lenAt f n j - 1) := hNgt _ (by omega)
  have hvj : 2 * Kc f n (lenAt f n j - 1) ≤ val f n j := by unfold val; omega
  have hge : (p + 1) * 2 ^ (lenAt f n j - R) ≤ val f n j := by omega
  have hdiv : p + 1 ≤ val f n j / 2 ^ (lenAt f n j - R) := (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).mpr hge
  have : pre f n R j = val f n j / 2 ^ (lenAt f n j - R) := rfl
  omega


/-! ### `huff` follows the canonical code -/

theorem huff_step (hfit : Fits f n) {i : Nat} (hi : i + 1 < Tc f n 15) :
    ∃ e, e < lenAt f n i ∧ incrLoop (rev (lenAt f n i) (val f n i)) (lenAt f n i - 1) = 2 ^ e ∧
      rev (lenAt f n i) (val f n i) % 2 ^ e + 2 ^ e = rev (lenAt f n (i + 1)) (val f n (i + 1)) := by
  have hi0 : i < Tc f n 15 := by omega
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi0
  have mono := lenAt_mono (f := f) (n := n) (show i ≤ i + 1 by omega) hi
  have hs := val_succ (f := f) (n := n) hi
  have hl := val_lt hfit hi
  generalize lenAt f n (i + 1) = ℓ' at *
  generalize hv : val f n (i + 1) = v' at *
  generalize hl0 : lenAt f n i = ℓ at *
  generalize hv0 : val f n i = v at *
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨Δ, rfl⟩ : ∃ Δ, ℓ' = k + 1 + Δ := ⟨ℓ' - (k + 1), by omega⟩
  have e1 : k + 1 + Δ - (k + 1) = Δ := by omega
  rw [e1] at hs
  have hvlt : v < 2 ^ (k + 1) := by
    have := val_lt hfit hi0
    rw [hl0, hv0] at this; exact this
  have hlt2 : (v + 1) * 2 ^ Δ < 2 ^ (k + 1) * 2 ^ Δ := by
    rw [← hs, ← Nat.pow_add]; exact hl
  have hv1 : v + 1 < 2 ^ (k + 1) := Nat.lt_of_mul_lt_mul_right hlt2
  obtain ⟨e, he, h1, h2⟩ := (succ_rev k v hvlt).1 hv1
  refine ⟨e, by omega, ?_, ?_⟩
  · simpa using h1
  · rw [h2, hs, rev_mul_pow]

theorem huff_last (hc : Kc f n 15 = 2 ^ 15) {m : Nat} (hm : Tc f n 15 = m + 1) :
    incrLoop (rev (lenAt f n m) (val f n m)) (lenAt f n m - 1) = 0 := by
  have hi : m < Tc f n 15 := by omega
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi
  have hl := val_last hc hm
  generalize lenAt f n m = ℓ at *
  generalize val f n m = v at *
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have := (succ_rev k v (by omega)).2 (by omega)
  simpa using this

/-- The low `R` bits of `huff` are the reversed prefix of the code. -/
theorem huff_low {R j : Nat} (hR : R ≤ lenAt f n j) :
    rev (lenAt f n j) (val f n j) % 2 ^ R = rev R (pre f n R j) := by
  unfold pre
  have h := rev_mod_pow (lenAt f n j - R) R (val f n j)
  rwa [Nat.add_sub_cancel' hR] at h

theorem pre_lt (hfit : Fits f n) {R j : Nat} (hj : j < Tc f n 15) (hR : R ≤ lenAt f n j) :
    pre f n R j < 2 ^ R := by
  unfold pre
  have := val_lt hfit hj
  have e : 2 ^ lenAt f n j = 2 ^ R * 2 ^ (lenAt f n j - R) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e] at this
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).mpr this

/-- A new root prefix starts at an aligned code. -/
theorem align_succ (hfit : Fits f n) {R i : Nat} (hi : i + 1 < Tc f n 15) (hR : R < lenAt f n (i + 1))
    (hnew : lenAt f n i ≤ R ∨ (R < lenAt f n i ∧ pre f n R (i + 1) ≠ pre f n R i)) :
    val f n (i + 1) % 2 ^ (lenAt f n (i + 1) - R) = 0 := by
  have hi0 : i < Tc f n 15 := by omega
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi0
  have mono := lenAt_mono (f := f) (n := n) (show i ≤ i + 1 by omega) hi
  have hs := val_succ (f := f) (n := n) hi
  unfold pre at hnew
  generalize lenAt f n (i + 1) = ℓ' at *
  generalize val f n (i + 1) = v' at *
  generalize lenAt f n i = ℓ at *
  generalize val f n i = v at *
  obtain ⟨Δ, rfl⟩ : ∃ Δ, ℓ' = ℓ + Δ := ⟨ℓ' - ℓ, by omega⟩
  have e1 : ℓ + Δ - ℓ = Δ := by omega
  rw [e1] at hs
  rcases hnew with h | h
  · -- 2^(ℓ' - R) divides 2^Δ
    have : ℓ + Δ - R ≤ Δ := Nat.sub_le_of_le_add (by omega)
    rw [hs]
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 this) _
  · -- the prefix changes: v + 1 crosses a multiple of 2^(ℓ - R)
    obtain ⟨hℓ, h⟩ := h
    have e2 : ℓ + Δ - R = Δ + (ℓ - R) := by omega
    have hq : (v + 1) * 2 ^ Δ / 2 ^ (ℓ + Δ - R) = (v + 1) / 2 ^ (ℓ - R) := by
      rw [e2, Nat.pow_add, Nat.mul_comm (2 ^ Δ) (2 ^ (ℓ - R))]
      exact Nat.mul_div_mul_right _ _ (Nat.pow_pos (by omega))
    rw [hs, hq] at h
    have hcr : (v + 1) % 2 ^ (ℓ - R) = 0 := by
      apply Classical.byContradiction
      intro hne
      apply h
      have hP : 0 < 2 ^ (ℓ - R) := Nat.pow_pos (by omega)
      have hlt : (v + 1) % 2 ^ (ℓ - R) ≠ 0 := hne
      have hv1 := Nat.div_add_mod v (2 ^ (ℓ - R))
      have hv2 := Nat.div_add_mod (v + 1) (2 ^ (ℓ - R))
      have hr0 := Nat.mod_lt v hP
      have hr1 := Nat.mod_lt (v + 1) hP
      generalize 2 ^ (ℓ - R) = P at *
      have : (v + 1) / P = v / P := by
        rcases Nat.lt_trichotomy ((v + 1) / P) (v / P) with hlt2 | heq | hgt
        · have := Nat.mul_le_mul_left P (show (v + 1) / P + 1 ≤ v / P by omega)
          rw [Nat.mul_succ] at this; omega
        · exact heq
        · have := Nat.mul_le_mul_left P (show v / P + 1 ≤ (v + 1) / P by omega)
          rw [Nat.mul_succ] at this; omega
      exact this
    -- (v+1) * 2^Δ is a multiple of 2^(Δ + (ℓ - R))
    rw [hs, e2, Nat.pow_add]
    apply Nat.mod_eq_zero_of_dvd
    have := Nat.mul_dvd_mul (Nat.dvd_of_mod_eq_zero hcr) (Nat.dvd_refl (2 ^ Δ))
    rw [Nat.mul_comm (2 ^ Δ) (2 ^ (ℓ - R))]
    exact this


/-! ### Counting -/

theorem fl_succ (t k : Nat) : fl f t (k + 1) = fl f t k ++ (if f k = t then [k] else []) := by
  unfold fl
  rw [List.range_succ, List.filter_append]
  by_cases h : f k = t <;> simp [h]

theorem cnt_succ (t k : Nat) : cnt f k t = cnt f k t ∧ True := ⟨rfl, trivial⟩

theorem cnt_step (t k : Nat) : cnt f (k + 1) t = cnt f k t + (if f k = t then 1 else 0) := by
  unfold cnt
  rw [fl_succ]
  by_cases h : f k = t <;> simp [h]

theorem cnt_le (t k : Nat) : cnt f k t ≤ k := by
  unfold cnt fl
  calc _ ≤ (List.range k).length := List.length_filter_le _ _
    _ = k := by simp

theorem Tc_step (k l : Nat) :
    Tc f (k + 1) l = Tc f k l + (if 1 ≤ f k ∧ f k ≤ l then 1 else 0) := by
  induction l with
  | zero => simp [Tc]; omega
  | succ l ih =>
    show Tc f (k + 1) l + cnt f (k + 1) (l + 1) = Tc f k l + cnt f k (l + 1) + _
    rw [ih, cnt_step]
    split <;> split <;> split <;> omega

theorem Tc_le (l : Nat) : ∀ k, Tc f k l ≤ k
  | 0 => by
    induction l with
    | zero => simp [Tc]
    | succ l ih => show Tc f 0 l + cnt f 0 (l + 1) ≤ 0; have := cnt_le (f := f) (l + 1) 0; omega
  | k + 1 => by
    have := Tc_le l k
    rw [Tc_step]
    split <;> omega


theorem fl_succ_ne {l k : Nat} (h : f k ≠ l) : fl f l (k + 1) = fl f l k := by
  rw [fl_succ, ite_eq_right h]; simp

theorem cnt_mono {l k n : Nat} (h : k ≤ n) : cnt f k l ≤ cnt f n l := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := ih (by omega)
    rw [← Nat.add_assoc, cnt_step]
    split <;> omega

theorem cnt_lt {l k n : Nat} (h : k < n) (hf : f k = l) : cnt f k l < cnt f n l := by
  have := cnt_mono (f := f) (l := l) (show k + 1 ≤ n by omega)
  rw [cnt_step, ite_eq_left hf] at this
  omega

theorem fl_getD_new {l k : Nat} (hf : f k = l) :
    (fl f l (k + 1)).getD (cnt f k l) 0 = k := by
  rw [fl_succ, ite_eq_left hf]
  have : (fl f l k).length = cnt f k l := rfl
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_eq this), this]

theorem fl_getD_old {l k j : Nat} (hf : f k = l) (hj : j < cnt f k l) :
    (fl f l (k + 1)).getD j 0 = (fl f l k).getD j 0 := by
  rw [fl_succ, ite_eq_left hf]
  have : (fl f l k).length = cnt f k l := rfl
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < (fl f l k).length by omega)]

theorem rev_zero : ∀ n, rev n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [rev, rev_zero n]

theorem val_zero (h : 0 < Tc f n 15) : val f n 0 = 0 := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) h
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n 0) b1 b2 h).mp rfl
  have hT : Tc f n (0 + (lenAt f n 0 - 1)) = Tc f n 0 := by
    have : Tc f n 0 = 0 := rfl
    simp only [Nat.zero_add]; omega
  have := Kc_gap (f := f) (n := n) 0 (lenAt f n 0 - 1) hT
  have hK0 : Kc f n 0 = 0 := rfl
  rw [hK0, Nat.mul_zero] at this
  unfold val
  simp only [Nat.zero_add] at this
  rw [this]
  omega


/-! ### The canonical code is prefix-free -/

/-- Later codes are above the end of the interval of an earlier one: `(v_i + 1) 2^(l_j - l_i) <= v_j`. -/
theorem val_ge {i : Nat} : ∀ d, i + 1 + d < Tc f n 15 →
    (val f n i + 1) * 2 ^ (lenAt f n (i + 1 + d) - lenAt f n i) ≤ val f n (i + 1 + d)
  | 0, h => by
    have := val_succ (f := f) (n := n) (i := i) (by omega)
    simp only [Nat.add_zero]; omega
  | d + 1, h => by
    have ih := val_ge (i := i) d (by omega)
    have hs := val_succ (f := f) (n := n) (i := i + 1 + d) (by omega)
    have m1 := lenAt_mono (f := f) (n := n) (show i ≤ i + 1 + d by omega) (by omega)
    have m2 := lenAt_mono (f := f) (n := n) (show i + 1 + d ≤ i + 1 + d + 1 by omega) (by omega)
    have e : i + 1 + (d + 1) = i + 1 + d + 1 := by omega
    rw [e, hs]
    have hp : 2 ^ (lenAt f n (i + 1 + d + 1) - lenAt f n i) =
        2 ^ (lenAt f n (i + 1 + d) - lenAt f n i) * 2 ^ (lenAt f n (i + 1 + d + 1) - lenAt f n (i + 1 + d)) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hp, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by
      have := Nat.mul_le_mul_right (2 ^ 0) ih
      omega)

/-- No canonical code is a prefix of a later one. -/
theorem prefix_free {i j : Nat} (hij : i < j) (hj : j < Tc f n 15) :
    val f n j / 2 ^ (lenAt f n j - lenAt f n i) ≠ val f n i := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
  have h := val_ge (f := f) (n := n) (i := i) d hj
  have hpos : 0 < 2 ^ (lenAt f n (i + 1 + d) - lenAt f n i) := Nat.pow_pos (by omega)
  intro heq
  have : val f n (i + 1 + d) / 2 ^ (lenAt f n (i + 1 + d) - lenAt f n i) ≥ val f n i + 1 :=
    (Nat.le_div_iff_mul_le hpos).mpr h
  omega


/-- The sets of table indices that two different codes fill are disjoint: the indices that fill the entries of the
`i`-th code are those `x` with `x mod 2^l_i = rev l_i v_i` (the first `l_i` bits that the decoder reads). -/
theorem entries_disjoint (hfit : Fits f n) {i j : Nat} (hij : i < j) (hj : j < Tc f n 15) (x : Nat) :
    ¬ (x % 2 ^ lenAt f n i = rev (lenAt f n i) (val f n i) ∧ x % 2 ^ lenAt f n j = rev (lenAt f n j) (val f n j)) := by
  rintro ⟨h1, h2⟩
  have hi : i < Tc f n 15 := by omega
  have m := lenAt_mono (f := f) (n := n) (show i ≤ j by omega) hj
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, lenAt f n j = lenAt f n i + Δ := ⟨lenAt f n j - lenAt f n i, by omega⟩
  have hd : lenAt f n j - lenAt f n i = Δ := by omega
  have h3 : x % 2 ^ lenAt f n i = rev (lenAt f n i) (val f n j / 2 ^ Δ) := by
    have e1 : x % 2 ^ lenAt f n i = (x % 2 ^ lenAt f n j) % 2 ^ lenAt f n i :=
      (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))).symm
    rw [e1, h2]
    have := rev_mod_pow Δ (lenAt f n i) (val f n j)
    rw [← hΔ] at this
    exact this
  have h4 := rev_inj _ _ _ (h1.symm.trans h3)
  have vi := val_lt hfit hi
  have vj := val_lt hfit hj
  have hlt : val f n j / 2 ^ Δ < 2 ^ lenAt f n i := by
    apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).mpr
    rw [← Nat.pow_add, ← hΔ]; exact vj
  rw [Nat.mod_eq_of_lt vi, Nat.mod_eq_of_lt hlt] at h4
  exact prefix_free (f := f) (n := n) hij hj (by rw [hd]; exact h4.symm)


/-- The reversed code is its root part plus `2^R` times the sub-table part. -/
theorem rev_split {R j : Nat} (hR : R ≤ lenAt f n j) :
    rev (lenAt f n j) (val f n j) = rev R (pre f n R j) + 2 ^ R * (rev (lenAt f n j) (val f n j) / 2 ^ R) := by
  have h := huff_low (f := f) (n := n) (R := R) (j := j) hR
  have := Nat.mod_add_div (rev (lenAt f n j) (val f n j)) (2 ^ R)
  omega

/-- Two different codes under the same root prefix fill different entries of their sub-table: the entries of the
`j`-th code are `hd_j + 2^(l_j - R) t` with `hd_j = rev l_j v_j / 2^R`. -/
theorem block_disjoint (hfit : Fits f n) {R i j : Nat} (hij : j < i) (hi : i < Tc f n 15)
    (hRj : R < lenAt f n j) (hp : pre f n R j = pre f n R i) (t t' : Nat) :
    rev (lenAt f n j) (val f n j) / 2 ^ R + 2 ^ (lenAt f n j - R) * t' ≠
      rev (lenAt f n i) (val f n i) / 2 ^ R + 2 ^ (lenAt f n i - R) * t := by
  intro heq
  have hj : j < Tc f n 15 := by omega
  have mono := lenAt_mono (f := f) (n := n) (show j ≤ i by omega) hi
  have sj := rev_split (f := f) (n := n) (R := R) (j := j) (by omega)
  have si := rev_split (f := f) (n := n) (R := R) (j := i) (by omega)
  have lj := rev_lt (lenAt f n j) (val f n j)
  have li := rev_lt (lenAt f n i) (val f n i)
  apply entries_disjoint hfit hij hi (rev R (pre f n R i) + 2 ^ R * (rev (lenAt f n j) (val f n j) / 2 ^ R + 2 ^ (lenAt f n j - R) * t'))
  have ej : 2 ^ R * 2 ^ (lenAt f n j - R) = 2 ^ lenAt f n j := by rw [← Nat.pow_add]; congr 1; omega
  have ei : 2 ^ R * 2 ^ (lenAt f n i - R) = 2 ^ lenAt f n i := by rw [← Nat.pow_add]; congr 1; omega
  constructor
  · -- modulo 2^l_j
    have : rev R (pre f n R i) + 2 ^ R * (rev (lenAt f n j) (val f n j) / 2 ^ R + 2 ^ (lenAt f n j - R) * t') =
        rev (lenAt f n j) (val f n j) + 2 ^ lenAt f n j * t' := by
      rw [← hp] at *
      rw [Nat.mul_add, ← Nat.mul_assoc, ej]
      omega
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt lj
  · rw [heq]
    have : rev R (pre f n R i) + 2 ^ R * (rev (lenAt f n i) (val f n i) / 2 ^ R + 2 ^ (lenAt f n i - R) * t) =
        rev (lenAt f n i) (val f n i) + 2 ^ lenAt f n i * t := by
      rw [Nat.mul_add, ← Nat.mul_assoc, ei]
      omega
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt li

end Model

end Zlib.Inftrees.Proofs
