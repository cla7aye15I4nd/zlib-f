/-!
# The canonical construction in the list model

Pure mathematics about the lengths `ls`, migrated from an earlier development: the allocation order, the Kraft
sums `K`, the canonical code values `cv`, `H = rev (L j) (cv j)` (the table index of the first entry of code `j`),
the group widths of the sub-tables (`look`, `width`) and the closed form `desc` of the table geometry. The names are
in the namespace `Zlib.Inftrees.Canon` so that they do not clash with the model used by the main proof.
-/

/-!
# Bit reversal and the backwards increment of inflate_table

Pure mathematics. `rev k x` reverses the low `k` bits of `x`; inflate_table
keeps the current canonical code `x` of length `k` bit-reversed in `huff`
(DEFLATE sends Huffman codes most-significant bit first, while table indices
are read least-significant bit first). The C "backwards increment" turns
`rev k x` into `rev k (x + 1)`.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Canon

/-- Reverse the low `k` bits of `x`. -/
def rev : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => rev k (x / 2) + (x % 2) * 2 ^ k

theorem rev_zero (x : Nat) : rev 0 x = 0 := rfl

theorem rev_succ (k x : Nat) : rev (k + 1) x = rev k (x / 2) + (x % 2) * 2 ^ k := rfl

theorem rev_lt (k x : Nat) : rev k x < 2 ^ k := by
  induction k generalizing x with
  | zero => simp [rev]
  | succ k ih =>
    rw [rev_succ, Nat.pow_succ]
    have := ih (x / 2)
    have : x % 2 ≤ 1 := by omega
    have : (x % 2) * 2 ^ k ≤ 2 ^ k := by
      calc (x % 2) * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ this
        _ = 2 ^ k := Nat.one_mul _
    omega

theorem rev_split (a b x : Nat) :
    rev (a + b) x = rev a (x / 2 ^ b) + rev b (x % 2 ^ b) * 2 ^ a := by
  induction b generalizing x with
  | zero => simp [rev]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, rev_succ, ih, rev_succ]
    have h1 : x / 2 / 2 ^ b = x / 2 ^ (b + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have h2 : x % 2 ^ (b + 1) / 2 = x / 2 % 2 ^ b := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    have h3 : x % 2 ^ (b + 1) % 2 = x % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    rw [h1, h2, h3, Nat.pow_add 2 a b, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ b) (2 ^ a)]
    omega

theorem rev_mod (k x : Nat) : rev k (x % 2 ^ k) = rev k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [rev_succ, rev_succ]
    have h2 : x % 2 ^ (k + 1) / 2 = x / 2 % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    have h3 : x % 2 ^ (k + 1) % 2 = x % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    rw [h2, h3, ih]

theorem rev_of_zero (k : Nat) : rev k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rev_succ, ih]

/-- Appending low zero bits (a code shifted left by `d`) adds high zero bits
to the reversed value. -/
theorem rev_shift (k d x : Nat) : rev (k + d) (x * 2 ^ d) = rev k x := by
  rw [rev_split, Nat.mul_div_cancel _ (Nat.two_pow_pos d), Nat.mul_mod_left, rev_of_zero]
  simp

theorem rev_two_pow (i : Nat) : rev (i + 1) (2 ^ i) = 1 := by
  have := rev_split 1 i (2 ^ i)
  rw [show 1 + i = i + 1 by omega] at this
  rw [this, Nat.div_self (Nat.two_pow_pos i), Nat.mod_self, rev_of_zero]
  simp [rev]

/-- Bit `k-1-i` of `rev k x` is bit `i` of `x`. -/
theorem rev_bit (k i x : Nat) (hi : i < k) :
    rev k x / 2 ^ (k - 1 - i) % 2 = x / 2 ^ i % 2 := by
  have hs := rev_split (k - 1 - i) (i + 1) x
  rw [show k - 1 - i + (i + 1) = k by omega] at hs
  rw [hs]
  have hlt := rev_lt (k - 1 - i) (x / 2 ^ (i + 1))
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [rev_succ]
  have hlt2 := rev_lt i (x % 2 ^ (i + 1) / 2)
  have : (x % 2 ^ (i + 1)) % 2 = x / 2 ^ i % 2 ∨ True := Or.inr trivial
  -- rev (i+1) y % 2 is the top bit of y
  have htop : ∀ (j y : Nat), y < 2 ^ (j + 1) → rev (j + 1) y % 2 = y / 2 ^ j := by
    intro j
    induction j with
    | zero => intro y hy; simp [rev] at *; omega
    | succ j ih =>
      intro y hy
      rw [rev_succ, Nat.pow_succ]
      have hy2 : y / 2 < 2 ^ (j + 1) := by
        rw [Nat.pow_succ] at hy ⊢; omega
      have := ih (y / 2) hy2
      have hpar : (rev (j + 1) (y / 2) + y % 2 * (2 ^ j * 2)) % 2 = rev (j + 1) (y / 2) % 2 := by
        rw [Nat.add_mod]; simp [← Nat.mul_assoc, Nat.mul_mod_left]
      rw [hpar, this, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have hy : x % 2 ^ (i + 1) < 2 ^ (i + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have ht := htop i (x % 2 ^ (i + 1)) hy
  rw [← rev_succ, ht]
  rw [Nat.pow_succ, Nat.mod_mul_right_div_self]

/-- Backwards increment, carry case: if bits `0..i-1` of `x` are ones and bit
`i` is zero (`i < k`), then `rev k (x+1)` keeps the top `k-1-i` reversed bits
and sets bit `k-1-i`. -/
theorem rev_succ_of_trailing (k i x : Nat) (hi : i < k)
    (hlow : x % 2 ^ i = 2 ^ i - 1) (hbit : x / 2 ^ i % 2 = 0) :
    rev k (x + 1) = rev k x % 2 ^ (k - 1 - i) + 2 ^ (k - 1 - i) := by
  have hk : k = (k - 1 - i) + (i + 1) := by omega
  have hs1 := rev_split (k - 1 - i) (i + 1) x
  have hs2 := rev_split (k - 1 - i) (i + 1) (x + 1)
  rw [← hk] at hs1 hs2
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have hm : x % 2 ^ (i + 1) = 2 ^ i - 1 := by
    have := Nat.mod_add_div (x % 2 ^ (i + 1)) (2 ^ i)
    have e1 : x % 2 ^ (i + 1) % 2 ^ i = x % 2 ^ i := by
      rw [Nat.pow_succ, Nat.mod_mul_right_mod]
    have e2 : x % 2 ^ (i + 1) / 2 ^ i = x / 2 ^ i % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_right_div_self]
    rw [e1, e2, hbit, hlow] at this
    omega
  have hq : (x + 1) / 2 ^ (i + 1) = x / 2 ^ (i + 1) := by
    have := Nat.div_add_mod x (2 ^ (i + 1))
    have hp2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
    have : x + 1 = 2 ^ (i + 1) * (x / 2 ^ (i + 1)) + 2 ^ i := by omega
    rw [this, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
    simp
  have hr : (x + 1) % 2 ^ (i + 1) = 2 ^ i := by
    have := Nat.div_add_mod x (2 ^ (i + 1))
    have hp2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
    have : x + 1 = 2 ^ (i + 1) * (x / 2 ^ (i + 1)) + 2 ^ i := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
  rw [hs2, hq, hr, rev_two_pow, Nat.one_mul, hs1]
  have hlt := rev_lt (k - 1 - i) (x / 2 ^ (i + 1))
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- Backwards increment, overflow case: all `k` bits ones. -/
theorem rev_all_ones (k x : Nat) (hlow : x % 2 ^ k = 2 ^ k - 1) (hx : x < 2 ^ k) :
    x + 1 = 2 ^ k := by
  rw [Nat.mod_eq_of_lt hx] at hlow
  have := Nat.two_pow_pos k
  omega

/-- Extending the low run of ones by one bit. -/
theorem low_ones_succ (x i : Nat) (hlow : x % 2 ^ i = 2 ^ i - 1) (hbit : x / 2 ^ i % 2 = 1) :
    x % 2 ^ (i + 1) = 2 ^ (i + 1) - 1 := by
  have := Nat.mod_add_div (x % 2 ^ (i + 1)) (2 ^ i)
  have e1 : x % 2 ^ (i + 1) % 2 ^ i = x % 2 ^ i := by
    rw [Nat.pow_succ, Nat.mod_mul_right_mod]
  have e2 : x % 2 ^ (i + 1) / 2 ^ i = x / 2 ^ i % 2 := by
    rw [Nat.pow_succ, Nat.mod_mul_right_div_self]
  rw [e1, e2, hbit, hlow] at this
  have hp2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
  have := Nat.two_pow_pos i
  omega

/-! ## Bitwise helpers -/

theorem and_two_pow (x p : Nat) : x &&& 2 ^ p = if x / 2 ^ p % 2 = 1 then 2 ^ p else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  split
  · rename_i hb
    rw [Nat.testBit_two_pow]
    by_cases hj : p = j
    · subst hj; simp [Nat.testBit_eq_decide_div_mod_eq, hb]
    · simp [hj]
  · rename_i hb
    simp only [Nat.zero_testBit]
    by_cases hj : p = j
    · subst hj; simp [Nat.testBit_eq_decide_div_mod_eq]; omega
    · simp [hj]

end Zlib.Inftrees.Canon

/-!
# Allocation order of the code lengths (counting sort in inflate_table)

Pure mathematics, independent of the C translation. For a length vector
`ls` (entries `0..15`), `symsOf ls l` lists the symbols of length `l` in
increasing order and `ord ls` concatenates them for `l = 1..15`. This is the
order in which inflate_table's counting sort leaves the symbols in `work[]`,
and the order in which its main loop assigns canonical codes.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Canon

/-- Symbols of length `l`, increasing. -/
def symsOf (ls : List Nat) (l : Nat) : List Nat :=
  (List.range ls.length).filter fun s => ls.getD s 0 == l

/-- Number of symbols with nonzero length below `l` (`offs[l]` in the C). -/
def offL (ls : List Nat) (l : Nat) : Nat :=
  ((List.range l).map fun l' => if l' = 0 then 0 else ls.count l').sum

/-- Allocation order: lengths 1..15, increasing symbol within a length. -/
def ord (ls : List Nat) : List Nat :=
  (List.range 15).flatMap fun i => symsOf ls (i + 1)

/-- Number of coded (nonzero-length) symbols. -/
def nz (ls : List Nat) : Nat := (ord ls).length

/-- `j`-th symbol in allocation order. -/
def sy (ls : List Nat) (j : Nat) : Nat := (ord ls).getD j 0

/-- Length of the `j`-th symbol in allocation order. -/
def L (ls : List Nat) (j : Nat) : Nat := ls.getD (sy ls j) 0

/-! ## Filter/count over ranges -/

theorem countP_range_succ (p : Nat → Bool) (k : Nat) :
    (List.range (k + 1)).countP p = (List.range k).countP p + (if p k then 1 else 0) := by
  rw [List.range_succ, List.countP_append]
  simp [List.countP_cons]

theorem filter_range_getElem? (p : Nat → Bool) (n k : Nat) (hk : k < n) (hp : p k = true) :
    ((List.range n).filter p)[(List.range k).countP p]? = some k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    by_cases hkn : k < n
    · rw [List.getElem?_append_left]
      · exact ih hkn
      · have : (List.range k).countP p < (List.range (k + 1)).countP p := by
          rw [countP_range_succ]; simp [hp]
        have h2 : (List.range (k + 1)).countP p ≤ (List.range n).countP p := by
          apply List.Sublist.countP_le
          exact (List.range_sublist).mpr (by omega)
        rw [← List.countP_eq_length_filter]
        omega
    · have hk' : k = n := by omega
      subst hk'
      rw [List.getElem?_append_right (by simp [List.countP_eq_length_filter])]
      simp [hp, List.countP_eq_length_filter]

theorem filter_range_length (p : Nat → Bool) (n : Nat) :
    ((List.range n).filter p).length = (List.range n).countP p :=
  (List.countP_eq_length_filter).symm

theorem countP_range_getD (ls : List Nat) (l k : Nat) (hk : k ≤ ls.length) :
    (List.range k).countP (fun s => ls.getD s 0 == l) = (ls.take k).count l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [countP_range_succ, ih (by omega)]
    rw [List.take_add_one]
    rw [List.count_append]
    have hk' : k < ls.length := by omega
    simp [List.getElem?_eq_getElem hk', List.getD_eq_getElem?_getD, List.count_singleton]

theorem symsOf_length (ls : List Nat) (l : Nat) : (symsOf ls l).length = ls.count l := by
  unfold symsOf
  rw [filter_range_length, countP_range_getD ls l _ (Nat.le_refl _), List.take_length]

/-- Position of symbol `k` within `symsOf`. -/
theorem symsOf_getElem? (ls : List Nat) (l k : Nat) (hk : k < ls.length)
    (hl : ls.getD k 0 = l) : (symsOf ls l)[(ls.take k).count l]? = some k := by
  unfold symsOf
  rw [← countP_range_getD ls l k (by omega)]
  exact filter_range_getElem? _ _ _ hk (by simp only [beq_iff_eq]; exact hl)

theorem mem_symsOf (ls : List Nat) (l s : Nat) :
    s ∈ symsOf ls l ↔ s < ls.length ∧ ls.getD s 0 = l := by
  simp [symsOf]

/-! ## flatMap over a range -/

theorem sum_range_le (g : Nat → Nat) (j m : Nat) (h : j ≤ m) :
    ((List.range j).map g).sum ≤ ((List.range m).map g).sum := by
  induction m with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    by_cases hj : j = m + 1
    · subst hj; exact Nat.le_refl _
    · have := ih (by omega)
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

theorem flatMap_range_getElem? (f : Nat → List Nat) (m j r : Nat) (hj : j < m)
    (hr : r < (f j).length) :
    ((List.range m).flatMap f)[((List.range j).map fun i => (f i).length).sum + r]? =
      (f j)[r]? := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hjm : j < m
    · rw [List.getElem?_append_left]
      · exact ih hjm
      · have hsub : ((List.range j).map fun i => (f i).length).sum + (f j).length ≤
            ((List.range m).flatMap f).length := by
          rw [List.length_flatMap]
          have h1 := sum_range_le (fun i => (f i).length) (j + 1) m (by omega)
          rw [List.range_succ, List.map_append, List.sum_append] at h1
          simpa using h1
        omega
    · have : j = m := by omega
      subst this
      rw [List.getElem?_append_right]
      · simp [List.length_flatMap]
      · simp [List.length_flatMap]

end Zlib.Inftrees.Canon


/-!
# Length intervals of the allocation order

Pure mathematics: allocation index `j` has length `l` exactly when
`offL l ≤ j < offL (l+1)`; lengths are nondecreasing along the order; the
counting sort places symbol `s` of length `l` at `offL l + #{s' < s : ls[s'] = l}`.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Canon

theorem offL_succ (ls : List Nat) (l : Nat) :
    offL ls (l + 1) = offL ls l + (if l = 0 then 0 else ls.count l) := by
  unfold offL
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem offL_zero (ls : List Nat) : offL ls 0 = 0 := rfl
theorem offL_one (ls : List Nat) : offL ls 1 = 0 := by simp [offL_succ, offL_zero]

theorem offL_succ_pos (ls : List Nat) {l : Nat} (hl : 1 ≤ l) :
    offL ls (l + 1) = offL ls l + ls.count l := by
  rw [offL_succ]; simp; omega

theorem offL_mono (ls : List Nat) {a b : Nat} (h : a ≤ b) : offL ls a ≤ offL ls b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a = b + 1
    · subst hab; exact Nat.le_refl _
    · have := ih (by omega); rw [offL_succ]; omega

theorem offL_eq_sum (ls : List Nat) (j : Nat) :
    offL ls (j + 1) = ((List.range j).map fun i => ls.count (i + 1)).sum := by
  induction j with
  | zero => exact offL_one ls
  | succ j ih =>
    rw [offL_succ_pos ls (by omega), ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem nz_eq (ls : List Nat) : nz ls = offL ls 16 := by
  unfold nz ord
  rw [List.length_flatMap, offL_eq_sum]
  simp [symsOf_length]

theorem ord_getElem? (ls : List Nat) (l r : Nat) (hl1 : 1 ≤ l) (hl : l ≤ 15)
    (hr : r < ls.count l) : (ord ls)[offL ls l + r]? = (symsOf ls l)[r]? := by
  unfold ord
  have hj : l - 1 < 15 := by omega
  have hlen : r < (symsOf ls (l - 1 + 1)).length := by
    rw [symsOf_length]; rw [show l - 1 + 1 = l by omega]; exact hr
  have := flatMap_range_getElem? (fun i => symsOf ls (i + 1)) 15 (l - 1) r hj hlen
  simp only [symsOf_length] at this
  rw [← offL_eq_sum, show l - 1 + 1 = l by omega] at this
  exact this

theorem exists_len (ls : List Nat) (j : Nat) (m : Nat) (hj : j < offL ls (m + 1)) :
    ∃ l, 1 ≤ l ∧ l ≤ m ∧ offL ls l ≤ j ∧ j < offL ls (l + 1) := by
  induction m with
  | zero => rw [offL_one] at hj; omega
  | succ m ih =>
    by_cases h : j < offL ls (m + 1)
    · obtain ⟨l, h1, h2, h3, h4⟩ := ih h
      exact ⟨l, h1, by omega, h3, h4⟩
    · exact ⟨m + 1, by omega, by omega, by omega, hj⟩

theorem sy_of_interval (ls : List Nat) {j l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ 15)
    (h1 : offL ls l ≤ j) (h2 : j < offL ls (l + 1)) :
    sy ls j < ls.length ∧ ls.getD (sy ls j) 0 = l := by
  rw [offL_succ_pos ls hl1] at h2
  have hr : j - offL ls l < ls.count l := by omega
  have hg := ord_getElem? ls l (j - offL ls l) hl1 hl hr
  rw [show offL ls l + (j - offL ls l) = j by omega] at hg
  have hlen : j - offL ls l < (symsOf ls l).length := by rw [symsOf_length]; exact hr
  have hm : (symsOf ls l)[j - offL ls l] ∈ symsOf ls l := List.getElem_mem hlen
  rw [List.getElem?_eq_getElem hlen] at hg
  have hsy : sy ls j = (symsOf ls l)[j - offL ls l] := by
    unfold sy; rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hsy]
  exact (mem_symsOf ls l _).mp hm

/-- Lengths are bounded by 15 (the C precondition). -/
def Bounded (ls : List Nat) : Prop := ∀ l ∈ ls, l ≤ 15

theorem count_eq_zero_of_gt (ls : List Nat) (hb : Bounded ls) (l : Nat) (hl : 15 < l) :
    ls.count l = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro hm; have := hb l hm; omega

theorem L_interval (ls : List Nat) {j : Nat} (hj : j < nz ls) :
    1 ≤ L ls j ∧ L ls j ≤ 15 ∧ offL ls (L ls j) ≤ j ∧ j < offL ls (L ls j + 1) ∧
      sy ls j < ls.length := by
  rw [nz_eq] at hj
  obtain ⟨l, h1, h2, h3, h4⟩ := exists_len ls j 15 hj
  obtain ⟨hs, hg⟩ := sy_of_interval ls h1 (by omega) h3 h4
  have : L ls j = l := hg
  rw [this]
  exact ⟨h1, h2, h3, h4, hs⟩

theorem L_eq_of_interval (ls : List Nat) {j l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ 15)
    (h1 : offL ls l ≤ j) (h2 : j < offL ls (l + 1)) : L ls j = l :=
  (sy_of_interval ls hl1 hl h1 h2).2

theorem L_mono (ls : List Nat) {j j' : Nat} (hjj : j ≤ j') (hj' : j' < nz ls) :
    L ls j ≤ L ls j' := by
  obtain ⟨_, _, a3, _, _⟩ := L_interval ls (show j < nz ls by omega)
  obtain ⟨_, _, _, b4, _⟩ := L_interval ls hj'
  refine Classical.byContradiction fun hc => ?_
  have := offL_mono ls (show L ls j' + 1 ≤ L ls j by omega)
  omega

/-- Indices of codes with length at most `l` are exactly `[0, offL (l+1))`. -/
theorem lt_offL_iff (ls : List Nat) {j l : Nat} (hj : j < nz ls) :
    j < offL ls (l + 1) ↔ L ls j ≤ l := by
  obtain ⟨_, _, a3, a4, _⟩ := L_interval ls hj
  constructor
  · intro h
    refine Classical.byContradiction fun hc => ?_
    have := offL_mono ls (show l + 1 ≤ L ls j by omega)
    omega
  · intro h
    have := offL_mono ls (show L ls j + 1 ≤ l + 1 by omega)
    omega

theorem count_take_lt (ls : List Nat) {s l : Nat} (hs : s < ls.length) (hls : ls.getD s 0 = l) :
    (ls.take s).count l < ls.count l := by
  have hsplit := congrArg (fun xs : List Nat => xs.count l) (List.take_append_drop s ls)
  simp only [List.count_append] at hsplit
  rw [List.drop_eq_getElem_cons hs] at hsplit
  have : ls[s] = l := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs] at hls; exact hls
  simp [this, List.count_cons] at hsplit
  omega

/-- Counting sort position: symbol `s` of length `l` sits at
`offL l + #{s' < s : ls[s'] = l}`. -/
theorem sy_sorted (ls : List Nat) {s l : Nat} (hs : s < ls.length) (hl1 : 1 ≤ l) (hl : l ≤ 15)
    (hls : ls.getD s 0 = l) : sy ls (offL ls l + (ls.take s).count l) = s := by
  have hr := count_take_lt ls hs hls
  unfold sy
  rw [List.getD_eq_getElem?_getD, ord_getElem? ls l _ hl1 hl hr, symsOf_getElem? ls l s hs hls]
  rfl

end Zlib.Inftrees.Canon


/-!
# Kraft prefix sums and canonical code values along the allocation order

Pure mathematics. `K ls j` is the left-aligned (15-bit) start of the `j`-th
canonical code; `cv ls j` its numeric code value; `H ls j` the bit-reversed
value inflate_table keeps in `huff`. `krAt` is the C's left recurrence.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Canon

def K (ls : List Nat) (j : Nat) : Nat := ((List.range j).map fun i => 2 ^ (15 - L ls i)).sum

def cv (ls : List Nat) (j : Nat) : Nat := K ls j / 2 ^ (15 - L ls j)

def H (ls : List Nat) (j : Nat) : Nat := rev (L ls j) (cv ls j)

/-- `krAt l = Σ_{1 ≤ l' ≤ l} count l' * 2^(l - l')`, the C's
`left <<= 1; left -= count[len]` recurrence with `left = 2^l - krAt l`. -/
def krAt (ls : List Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => 2 * krAt ls l + ls.count (l + 1)

/-- Remaining codes of length `l` at or after allocation index `a`. -/
def cntGE (ls : List Nat) (a l : Nat) : Nat := offL ls (l + 1) - max a (offL ls l)

theorem K_succ (ls : List Nat) (j : Nat) : K ls (j + 1) = K ls j + 2 ^ (15 - L ls j) := by
  unfold K; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem K_zero (ls : List Nat) : K ls 0 = 0 := rfl

theorem K_mono (ls : List Nat) {j j' : Nat} (h : j ≤ j') : K ls j ≤ K ls j' := by
  induction j' with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j' ih =>
    by_cases hj : j = j' + 1
    · subst hj; exact Nat.le_refl _
    · have := ih (by omega); rw [K_succ]; have := Nat.two_pow_pos (15 - L ls j'); omega

theorem K_strict (ls : List Nat) {j j' : Nat} (h : j < j') : K ls j < K ls j' := by
  have h1 := K_mono ls (show j + 1 ≤ j' by omega)
  have h2 := K_succ ls j
  have := Nat.two_pow_pos (15 - L ls j)
  omega

/-- Prefix sums are multiples of `2^(15-l)` when all earlier lengths are `≤ l`. -/
theorem dvd_K (ls : List Nat) (j l : Nat) (h : ∀ i < j, L ls i ≤ l) :
    2 ^ (15 - l) ∣ K ls j := by
  induction j with
  | zero => exact Nat.dvd_zero _
  | succ j ih =>
    rw [K_succ]
    refine Nat.dvd_add (ih fun i hi => h i (by omega)) ?_
    exact Nat.pow_dvd_pow 2 (by have := h j (by omega); omega)

theorem dvd_K_self (ls : List Nat) {j : Nat} (hj : j < nz ls) :
    2 ^ (15 - L ls j) ∣ K ls j :=
  dvd_K ls j _ fun i hi => L_mono ls (by omega) hj

/-- Codes of one length are consecutive multiples. -/
theorem K_offL_add (ls : List Nat) {l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ 15) (r : Nat)
    (hr : r ≤ ls.count l) : K ls (offL ls l + r) = K ls (offL ls l) + r * 2 ^ (15 - l) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← Nat.add_assoc, K_succ, ih (by omega)]
    have h2 : offL ls l + r < offL ls (l + 1) := by rw [offL_succ_pos ls hl1]; omega
    rw [L_eq_of_interval ls hl1 hl (by omega) h2, Nat.succ_mul]
    omega

theorem krAt_K (ls : List Nat) (l : Nat) (hl : l ≤ 15) :
    krAt ls l * 2 ^ (15 - l) = K ls (offL ls (l + 1)) := by
  induction l with
  | zero => simp [krAt, offL_one, K_zero]
  | succ l ih =>
    rw [krAt, offL_succ_pos ls (show 1 ≤ l + 1 by omega),
      K_offL_add ls (by omega) hl _ (Nat.le_refl _), ← ih (by omega)]
    have hp : 2 ^ (15 - l) = 2 * 2 ^ (15 - (l + 1)) := by
      rw [show 15 - l = (15 - (l + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    rw [hp, Nat.add_mul, Nat.mul_comm 2 (krAt ls l), Nat.mul_assoc]

/-- Total Kraft sum (in units of 2^-15) of the coded symbols. -/
theorem krAt15 (ls : List Nat) : krAt ls 15 = K ls (nz ls) := by
  have := krAt_K ls 15 (by omega)
  simp at this
  rw [nz_eq]; exact this

theorem krAt_mono (ls : List Nat) (a b : Nat) (h : a ≤ b) :
    krAt ls a * 2 ^ (b - a) ≤ krAt ls b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; simp
  | succ b ih =>
    by_cases hab : a = b + 1
    · subst hab; simp
    · have := ih (by omega)
      rw [krAt, show b + 1 - a = (b - a) + 1 by omega, Nat.pow_succ]
      rw [← Nat.mul_assoc]
      omega

/-! ## Canonical values -/

theorem cv_mul (ls : List Nat) {j : Nat} (hj : j < nz ls) :
    cv ls j * 2 ^ (15 - L ls j) = K ls j := Nat.div_mul_cancel (dvd_K_self ls hj)

theorem cv_succ (ls : List Nat) {j : Nat} (hj : j + 1 < nz ls) :
    cv ls (j + 1) = (cv ls j + 1) * 2 ^ (L ls (j + 1) - L ls j) := by
  have hm := L_mono ls (show j ≤ j + 1 by omega) hj
  have h15 := (L_interval ls hj).2.1
  show K ls (j + 1) / 2 ^ (15 - L ls (j + 1)) = _
  rw [K_succ, ← cv_mul ls (show j < nz ls by omega)]
  have hp : 2 ^ (15 - L ls j) = 2 ^ (L ls (j + 1) - L ls j) * 2 ^ (15 - L ls (j + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [show cv ls j * 2 ^ (15 - L ls j) + 2 ^ (15 - L ls j) = (cv ls j + 1) * 2 ^ (15 - L ls j)
    by rw [Nat.succ_mul], hp, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem H_succ (ls : List Nat) {j : Nat} (hj : j + 1 < nz ls) :
    H ls (j + 1) = rev (L ls j) (cv ls j + 1) := by
  have hm := L_mono ls (show j ≤ j + 1 by omega) hj
  show rev (L ls (j + 1)) (cv ls (j + 1)) = _
  rw [cv_succ ls hj]
  have := rev_shift (L ls j) (L ls (j + 1) - L ls j) (cv ls j + 1)
  rw [show L ls j + (L ls (j + 1) - L ls j) = L ls (j + 1) by omega] at this
  exact this

theorem H_zero (ls : List Nat) : H ls 0 = 0 := by
  unfold H cv; rw [K_zero, Nat.zero_div, rev_of_zero]

/-- A valid (not over-subscribed) code has room for every code value. -/
theorem cv_succ_le (ls : List Nat) {j : Nat} (hj : j < nz ls)
    (hk : K ls (j + 1) ≤ 2 ^ 15) : cv ls j + 1 ≤ 2 ^ L ls j := by
  have h15 := (L_interval ls hj).2.1
  rw [K_succ, ← cv_mul ls hj] at hk
  have hp : 2 ^ 15 = 2 ^ L ls j * 2 ^ (15 - L ls j) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hp, show cv ls j * 2 ^ (15 - L ls j) + 2 ^ (15 - L ls j) =
    (cv ls j + 1) * 2 ^ (15 - L ls j) by rw [Nat.succ_mul]] at hk
  exact Nat.le_of_mul_le_mul_right hk (Nat.two_pow_pos _)

theorem H_lt (ls : List Nat) (j : Nat) : H ls j < 2 ^ L ls j := rev_lt _ _

/-! ## Remaining counts -/

theorem cntGE_zero (ls : List Nat) {l : Nat} (hl : 1 ≤ l) : cntGE ls 0 l = ls.count l := by
  unfold cntGE; rw [offL_succ_pos ls hl]; simp

/-- Decrement of `count[len]` after processing allocation index `j`. -/
theorem cntGE_succ (ls : List Nat) {j l : Nat} (hj : j < nz ls) (hl : 1 ≤ l) :
    cntGE ls (j + 1) l = if l = L ls j then cntGE ls j l - 1 else cntGE ls j l := by
  obtain ⟨a1, a2, a3, a4, _⟩ := L_interval ls hj
  unfold cntGE
  split
  · rename_i he; subst he; omega
  · rename_i hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := offL_mono ls (show l + 1 ≤ L ls j by omega); omega
    · have := offL_mono ls (show L ls j + 1 ≤ l by omega); omega

theorem cntGE_self (ls : List Nat) {j : Nat} (hj : j < nz ls) :
    cntGE ls j (L ls j) = offL ls (L ls j + 1) - j := by
  obtain ⟨_, _, a3, _, _⟩ := L_interval ls hj
  unfold cntGE; congr 1; omega

end Zlib.Inftrees.Canon


/-!
# Root groups, the sub-table lookahead and the table descriptor sequence

Pure mathematics. With root width `root`, the codes longer than `root` fall
into groups by their first `root` bits, `grp j = K j / 2^(15-root)`. When the
main loop of inflate_table reaches the first code of a group it computes the
sub-table width with the `count[]` lookahead (`look`), advances `next` past the
previous table, and grows `used`. `desc ls root mx i` is the
(drop, curr, base, used, low) state in force while code `i` is written.

For a complete code (`K (nz) = 2^15`) every code of a group fits its
sub-table: `L i ≤ root + curr` (`look_covers`).
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Canon

def grp (ls : List Nat) (root j : Nat) : Nat := K ls j / 2 ^ (15 - root)

/-- The C lookahead
```c
while (curr + drop < max) { left -= count[curr + drop]; if (left <= 0) break;
                            curr++; left <<= 1; }
```
with `count[l] = cntGE a l` and a fuel bound. -/
def look (ls : List Nat) (a root mx : Nat) : Nat → Int → Nat → Nat
  | c, _, 0 => c
  | c, left, f + 1 =>
    if c + root < mx then
      if left - (cntGE ls a (c + root) : Int) ≤ 0 then c
      else look ls a root mx (c + 1) (2 * (left - (cntGE ls a (c + root) : Int))) f
    else c

/-- The sub-table width chosen for a group starting at allocation index `a`. -/
def width (ls : List Nat) (a root mx : Nat) : Nat :=
  look ls a root mx (L ls a - root) (2 ^ (L ls a - root) : Nat) 16

structure Desc where
  drop : Nat
  curr : Nat
  base : Nat
  used : Nat
  low : Nat
  deriving Repr

/-- A new sub-table starts at code `i+1`. -/
def startsAt (ls : List Nat) (root i : Nat) : Prop :=
  root < L ls (i + 1) ∧ (L ls i ≤ root ∨ grp ls root (i + 1) ≠ grp ls root i)

instance (ls : List Nat) (root i : Nat) : Decidable (startsAt ls root i) := by
  unfold startsAt; infer_instance

/-- Table descriptor in force while code `i` is written. -/
def desc (ls : List Nat) (root mx : Nat) : Nat → Desc
  | 0 => ⟨0, root, 0, 2 ^ root, 2 ^ 32 - 1⟩
  | i + 1 =>
    let d := desc ls root mx i
    if startsAt ls root i then
      ⟨root, width ls (i + 1) root mx, d.base + 2 ^ d.curr,
        d.used + 2 ^ width ls (i + 1) root mx, rev root (grp ls root (i + 1))⟩
    else d

/-! ## Hypotheses shared by the lemmas below -/

/-- Accepted complete code with root in `[min, max]`. -/
structure CompleteCode (ls : List Nat) (root mx : Nat) : Prop where
  pos : 0 < nz ls
  complete : K ls (nz ls) = 2 ^ 15
  root_pos : 1 ≤ root
  root_le : root ≤ mx
  mx_eq : mx = L ls (nz ls - 1)
  min_le : L ls 0 ≤ root

theorem CompleteCode.L_le_mx {ls : List Nat} {root mx : Nat} (hc : CompleteCode ls root mx)
    {i : Nat} (hi : i < nz ls) : L ls i ≤ mx := by
  rw [hc.mx_eq]; exact L_mono ls (by omega) (by have := hc.pos; omega)

theorem CompleteCode.mx_le {ls : List Nat} {root mx : Nat} (hc : CompleteCode ls root mx) :
    mx ≤ 15 := by
  rw [hc.mx_eq]; exact (L_interval ls (by have := hc.pos; omega)).2.1

theorem CompleteCode.K_lt {ls : List Nat} {root mx : Nat} (hc : CompleteCode ls root mx)
    {i : Nat} (hi : i < nz ls) : K ls (i + 1) ≤ 2 ^ 15 := by
  rw [← hc.complete]; exact K_mono ls (by omega)

theorem grp_lt {ls : List Nat} {root mx : Nat} (hc : CompleteCode ls root mx)
    {i : Nat} (hi : i < nz ls) : grp ls root i < 2 ^ root := by
  have hk : K ls i < 2 ^ 15 := by
    have := hc.K_lt hi; have := K_strict ls (show i < i + 1 by omega); omega
  have hr15 : root ≤ 15 := Nat.le_trans hc.root_le hc.mx_le
  have hp : 2 ^ 15 = 2 ^ root * 2 ^ (15 - root) := by rw [← Nat.pow_add]; congr 1; omega
  unfold grp
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← hp]
  exact hk

theorem grp_mono (ls : List Nat) (root : Nat) {i j : Nat} (h : i ≤ j) :
    grp ls root i ≤ grp ls root j :=
  Nat.div_le_div_right (K_mono ls h)

/-! ## Alignment of group starts -/

/-- A long code that starts a group begins on a root-slot boundary. -/
theorem start_aligned {ls : List Nat} {root mx : Nat} (hc : CompleteCode ls root mx)
    {i : Nat} (hi : i + 1 < nz ls) (hs : startsAt ls root i) :
    K ls (i + 1) = grp ls root (i + 1) * 2 ^ (15 - root) := by
  have hr15 : root ≤ 15 := Nat.le_trans hc.root_le hc.mx_le
  obtain ⟨hlong, hcase⟩ := hs
  by_cases hshort : L ls i ≤ root
  · have hd : 2 ^ (15 - root) ∣ K ls (i + 1) := by
      apply dvd_K
      intro j hj
      exact Nat.le_trans (L_mono ls (show j ≤ i by omega) (by omega)) hshort
    unfold grp; exact (Nat.div_mul_cancel hd).symm
  · have hne : grp ls root (i + 1) ≠ grp ls root i := by
      rcases hcase with h | h
      · exact absurd h hshort
      · exact h
    have hi' : i < nz ls := by omega
    have hL15 := (L_interval ls hi').2.1
    -- u = 2^(15 - L i), U = 2^(15 - root) = t * u
    have hU : 2 ^ (15 - root) = 2 ^ (L ls i - root) * 2 ^ (15 - L ls i) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hKi := cv_mul ls hi'
    have hKs := K_succ ls i
    have hq_le : grp ls root (i + 1) * 2 ^ (15 - root) ≤ K ls (i + 1) := Nat.div_mul_le_self _ _
    have hgi : grp ls root i < grp ls root (i + 1) := by
      have := grp_mono ls root (show i ≤ i + 1 by omega); omega
    have hlt : K ls i < grp ls root (i + 1) * 2 ^ (15 - root) := by
      unfold grp at hgi
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mp hgi
    -- divide everything by u
    generalize hu : 2 ^ (15 - L ls i) = u at hU hKi hKs
    generalize ht : 2 ^ (L ls i - root) = t at hU
    generalize hq : grp ls root (i + 1) = q at hq_le hlt ⊢
    have hupos : 0 < u := by rw [← hu]; exact Nat.two_pow_pos _
    rw [hU] at hq_le hlt
    rw [hKs, ← hKi] at hq_le
    rw [← hKi] at hlt
    rw [hKs, ← hKi, hU]
    -- q * (t * u) ≤ cv * u + u and cv * u < q * (t * u)
    have h1 : q * t ≤ cv ls i + 1 := by
      have : q * t * u ≤ (cv ls i + 1) * u := by
        rw [Nat.mul_assoc, Nat.succ_mul]; exact hq_le
      exact Nat.le_of_mul_le_mul_right this hupos
    have h2 : cv ls i < q * t := by
      have : cv ls i * u < q * t * u := by rw [Nat.mul_assoc]; exact hlt
      exact Nat.lt_of_mul_lt_mul_right this
    have h3 : q * t = cv ls i + 1 := by omega
    rw [← Nat.mul_assoc, h3, Nat.succ_mul]

end Zlib.Inftrees.Canon


/-!
# The sub-table lookahead covers its group

Pure mathematics. For a complete code, the width `look` chooses for a group
starting at allocation index `a` accommodates every code of the group, and
(for the canonical-table bridge) is attained by some code of the group.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Canon

theorem K_range (ls : List Nat) {l x : Nat} (hl1 : 1 ≤ l) (hl : l ≤ 15)
    (h1 : offL ls l ≤ x) (h2 : x ≤ offL ls (l + 1)) :
    K ls x = K ls (offL ls l) + (x - offL ls l) * 2 ^ (15 - l) := by
  have := K_offL_add ls hl1 hl (x - offL ls l) (by rw [offL_succ_pos ls hl1] at h2; omega)
  rwa [show offL ls l + (x - offL ls l) = x by omega] at this

/-- Coverage by codes from `a` of length `< root + c`. -/
def cov (ls : List Nat) (a root c : Nat) : Nat := K ls (max a (offL ls (root + c))) - K ls a

theorem cov_step (ls : List Nat) {a root c : Nat} (ha : a < nz ls)
    (hc : L ls a ≤ root + c) (h15 : root + c ≤ 15) :
    cov ls a root (c + 1) = cov ls a root c + cntGE ls a (root + c) * 2 ^ (15 - (root + c)) := by
  obtain ⟨a1, _, _, a4, _⟩ := L_interval ls ha
  have hl1 : 1 ≤ root + c := by omega
  have hmono := offL_mono ls (show L ls a + 1 ≤ root + c + 1 by omega)
  have hmono2 := offL_mono ls (show root + c ≤ root + c + 1 by omega)
  have hmax1 : max a (offL ls (root + (c + 1))) = offL ls (root + c + 1) := by
    rw [show root + (c + 1) = root + c + 1 by omega]; omega
  have hK1 := K_range ls hl1 h15 (x := offL ls (root + c + 1)) hmono2 (Nat.le_refl _)
  have hK2 := K_range ls hl1 h15 (x := max a (offL ls (root + c))) (by omega) (by omega)
  have hKa := K_mono ls (show a ≤ max a (offL ls (root + c)) by omega)
  unfold cov cntGE
  rw [hmax1, hK1, hK2]
  have hsub : offL ls (root + c + 1) - offL ls (root + c) =
      (offL ls (root + c + 1) - max a (offL ls (root + c))) +
        (max a (offL ls (root + c)) - offL ls (root + c)) := by omega
  rw [hsub, Nat.add_mul]
  rw [hK2] at hKa
  omega

theorem cov_init (ls : List Nat) {a root : Nat} (ha : a < nz ls) (hr : root ≤ L ls a) :
    cov ls a root (L ls a - root) = 0 := by
  obtain ⟨_, _, a3, _, _⟩ := L_interval ls ha
  unfold cov
  rw [show root + (L ls a - root) = L ls a by omega, show max a (offL ls (L ls a)) = a by omega]
  simp

theorem look_spec (ls : List Nat) {a root mx : Nat} (ha : a < nz ls) (hmx : mx ≤ 15) :
    ∀ (f c : Nat) (left : Int), L ls a ≤ root + c → c + root ≤ mx → mx - root - c ≤ f →
      left * (2 ^ (15 - root - c) : Nat) = ((2 ^ (15 - root) : Nat) : Int) - (cov ls a root c : Int) →
      0 < left →
      c ≤ look ls a root mx c left f ∧ look ls a root mx c left f + root ≤ mx ∧
      (look ls a root mx c left f + root = mx ∨
        2 ^ (15 - root) ≤ cov ls a root (look ls a root mx c left f + 1)) ∧
      (c < look ls a root mx c left f →
        cov ls a root (look ls a root mx c left f) < 2 ^ (15 - root)) := by
  intro f
  induction f with
  | zero =>
    intro c left h1 h2 h3 _ _
    simp only [look]
    exact ⟨Nat.le_refl _, h2, Or.inl (by omega), fun h => absurd h (Nat.lt_irrefl _)⟩
  | succ f ih =>
    intro c left h1 h2 h3 hinv hpos
    simp only [look]
    by_cases hlt : c + root < mx
    · rw [ite_eq_left hlt]
      have hstep := cov_step ls ha h1 (by omega)
      have hp : (2 ^ (15 - root - c) : Nat) = 2 ^ (15 - (root + c)) := by congr 1; omega
      -- new left times 2^(15-root-c)
      have hinv' : (left - (cntGE ls a (c + root) : Int)) * (2 ^ (15 - root - c) : Nat) =
          ((2 ^ (15 - root) : Nat) : Int) - (cov ls a root (c + 1) : Int) := by
        have e1 : ((cov ls a root (c + 1) : Nat) : Int) = (cov ls a root c : Int) +
            (cntGE ls a (root + c) : Int) * ((2 ^ (15 - (root + c)) : Nat) : Int) := by
          rw [hstep]; push_cast; rfl
        rw [Int.sub_mul, hinv, e1, show c + root = root + c by omega, hp]
        generalize (cntGE ls a (root + c) : Int) * ((2 ^ (15 - (root + c)) : Nat) : Int) = M
        omega
      by_cases hle : left - (cntGE ls a (c + root) : Int) ≤ 0
      · rw [ite_eq_left hle]
        refine ⟨Nat.le_refl _, by omega, Or.inr ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
        have hnn : (0 : Int) ≤ (2 ^ (15 - root - c) : Nat) := Int.natCast_nonneg _
        have := Int.mul_le_mul_of_nonneg_right hle hnn
        rw [hinv'] at this
        omega
      · rw [ite_eq_right hle]
        have hp2 : (2 ^ (15 - root - c) : Nat) = 2 * 2 ^ (15 - root - (c + 1)) := by
          rw [show 15 - root - c = (15 - root - (c + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hinv2 : 2 * (left - (cntGE ls a (c + root) : Int)) * (2 ^ (15 - root - (c + 1)) : Nat) =
            ((2 ^ (15 - root) : Nat) : Int) - (cov ls a root (c + 1) : Int) := by
          rw [← hinv', hp2]; push_cast; rw [Int.mul_comm 2, Int.mul_assoc]
        obtain ⟨r1, r2, r3, r4⟩ := ih (c + 1) _ (by omega) (by omega) (by omega) hinv2 (by omega)
        refine ⟨by omega, r2, r3, ?_⟩
        intro _
        by_cases hcr : c + 1 < look ls a root mx (c + 1) (2 * (left - (cntGE ls a (c + root) : Int))) f
        · exact r4 hcr
        · have heq : look ls a root mx (c + 1) (2 * (left - (cntGE ls a (c + root) : Int))) f = c + 1 := by omega
          rw [heq]
          have hpos2 : (0 : Int) < (2 ^ (15 - root - c) : Nat) := by
            exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
          have := Int.mul_pos (show (0 : Int) < left - (cntGE ls a (c + root) : Int) by omega) hpos2
          rw [hinv'] at this
          omega
    · rw [ite_eq_right hlt]
      refine ⟨Nat.le_refl _, h2, Or.inl (by omega), fun h => absurd h (Nat.lt_irrefl _)⟩

/-- Result facts for the width of a group starting at `a` (a long code). -/
theorem width_spec (ls : List Nat) {a root mx : Nat} (ha : a < nz ls) (hmx : mx ≤ 15)
    (hlong : root < L ls a) (hLmx : L ls a ≤ mx) :
    L ls a - root ≤ width ls a root mx ∧ width ls a root mx + root ≤ mx ∧
      (width ls a root mx + root = mx ∨ 2 ^ (15 - root) ≤ cov ls a root (width ls a root mx + 1)) ∧
      (L ls a - root < width ls a root mx →
        cov ls a root (width ls a root mx) < 2 ^ (15 - root)) := by
  unfold width
  apply look_spec ls ha hmx 16 _ _ (by omega) (by omega) (by omega) _ (by
    have := Nat.two_pow_pos (L ls a - root); omega)
  rw [cov_init ls ha (by omega)]
  have hp : 2 ^ (L ls a - root) * 2 ^ (15 - root - (L ls a - root)) = 2 ^ (15 - root) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [show ((0 : Nat) : Int) = 0 from rfl, Int.sub_zero]
  exact_mod_cast hp

/-- Every code of the group fits the chosen sub-table width. -/
theorem look_covers {ls : List Nat} {root mx : Nat} (hc : CompleteCode ls root mx)
    {a : Nat} (ha : a + 1 < nz ls) (hs : startsAt ls root a) {i : Nat}
    (hi1 : a + 1 ≤ i) (hi : i < nz ls) (hg : grp ls root i = grp ls root (a + 1)) :
    L ls i ≤ root + width ls (a + 1) root mx := by
  have hmx := hc.mx_le
  obtain ⟨w1, w2, w3, _⟩ := width_spec ls ha hmx hs.1 (hc.L_le_mx ha)
  rcases w3 with heq | hcov
  · have := hc.L_le_mx hi; omega
  · refine Classical.byContradiction fun hcon => ?_
    have hal := start_aligned hc ha hs
    have hge : max (a + 1) (offL ls (root + (width ls (a + 1) root mx + 1))) ≤ i := by
      have : ¬ i < offL ls (root + width ls (a + 1) root mx + 1) := by
        rw [lt_offL_iff ls hi]; omega
      rw [show root + (width ls (a + 1) root mx + 1) = root + width ls (a + 1) root mx + 1 by omega]
      omega
    have hKi := K_mono ls hge
    unfold cov at hcov
    have hka := K_mono ls (show a + 1 ≤ max (a + 1) (offL ls (root + (width ls (a + 1) root mx + 1)))
      by omega)
    -- K i ≥ (grp (a+1) + 1) * 2^(15-root), contradicting grp i = grp (a+1)
    have hK : (grp ls root (a + 1) + 1) * 2 ^ (15 - root) ≤ K ls i := by
      rw [Nat.succ_mul, ← hal]; omega
    have : grp ls root (a + 1) + 1 ≤ grp ls root i := by
      unfold grp
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr hK
    omega

end Zlib.Inftrees.Canon


/-!
# Properties of the table descriptor sequence

Pure mathematics: shape of `desc` (root table while codes are short; one
sub-table per group afterwards), `used = base + 2^curr`, monotonicity, and
the facts the main loop needs for in-bounds writes. Also the reversed group
index read from `huff & mask`, and `rev` injectivity.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Canon

theorem rev_one (b : Nat) : rev 1 b = b % 2 := by simp [rev]

theorem rev_rev (k x : Nat) : rev k (rev k x) = x % 2 ^ k := by
  induction k generalizing x with
  | zero => simp [rev, Nat.mod_one]
  | succ k ih =>
    have hs := rev_split 1 k (rev (k + 1) x)
    rw [show 1 + k = k + 1 by omega] at hs
    have hlt := rev_lt k (x / 2)
    have hb : x % 2 < 2 := Nat.mod_lt _ (by decide)
    have h1 : (rev k (x / 2) + x % 2 * 2 ^ k) / 2 ^ k = x % 2 := by
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt]; simp
    have h2 : (rev k (x / 2) + x % 2 * 2 ^ k) % 2 ^ k = rev k (x / 2) := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    rw [hs, rev_one, show rev (k + 1) x = rev k (x / 2) + x % 2 * 2 ^ k from rev_succ k x,
      h1, h2, ih, Nat.mod_mod, Nat.pow_one]
    -- x % 2 + (x / 2 % 2^k) * 2 = x % 2^(k+1)
    have := Nat.mod_add_div (x % 2 ^ (k + 1)) 2
    have e1 : x % 2 ^ (k + 1) % 2 = x % 2 := by rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    have e2 : x % 2 ^ (k + 1) / 2 = x / 2 % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    rw [e1, e2] at this
    omega

theorem rev_inj {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) (h : rev k x = rev k y) :
    x = y := by
  have := congrArg (rev k) h
  rw [rev_rev, rev_rev, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  exact this

/-- `huff & mask` of a long code is the reversed root prefix (its group). -/
theorem H_mod_root (ls : List Nat) {root j : Nat} (hj : j < nz ls) (hr : root ≤ L ls j) :
    H ls j % 2 ^ root = rev root (grp ls root j) := by
  have h15 := (L_interval ls hj).2.1
  unfold H
  have hs := rev_split root (L ls j - root) (cv ls j)
  rw [show root + (L ls j - root) = L ls j by omega] at hs
  rw [hs, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (rev_lt _ _)]
  congr 1
  unfold grp cv
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 2; omega

/-- `huff >> root` of a long code. -/
theorem H_div_root (ls : List Nat) {root j : Nat} (hj : j < nz ls) (hr : root ≤ L ls j) :
    H ls j / 2 ^ root = rev (L ls j - root) (cv ls j % 2 ^ (L ls j - root)) := by
  unfold H
  have hs := rev_split root (L ls j - root) (cv ls j)
  rw [show root + (L ls j - root) = L ls j by omega] at hs
  rw [hs, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (rev_lt _ _)]
  simp

theorem desc_used (ls : List Nat) (root mx : Nat) (i : Nat) :
    (desc ls root mx i).used = (desc ls root mx i).base + 2 ^ (desc ls root mx i).curr := by
  induction i with
  | zero => simp [desc]
  | succ i ih =>
    simp only [desc]
    split
    · simp only; rw [ih]
    · exact ih

theorem desc_used_mono (ls : List Nat) (root mx : Nat) {i j : Nat} (h : i ≤ j) :
    (desc ls root mx i).used ≤ (desc ls root mx j).used := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    by_cases hij : i = j + 1
    · subst hij; exact Nat.le_refl _
    · have := ih (by omega)
      simp only [desc]
      split
      · simp only; have := Nat.two_pow_pos (width ls (j + 1) root mx); omega
      · exact this

theorem desc_short (ls : List Nat) {root mx i : Nat} (hi : i < nz ls) (hs : L ls i ≤ root) :
    desc ls root mx i = desc ls root mx 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hm := L_mono ls (show i ≤ i + 1 by omega) hi
    simp only [desc]
    rw [ite_eq_right (by intro h; exact absurd h.1 (by omega))]
    exact ih (by omega) (by omega)

/-- A long code's descriptor is the one set up at the start of its group. -/
theorem desc_long {ls : List Nat} {root mx : Nat} (hmin : L ls 0 ≤ root) {i : Nat}
    (hi : i < nz ls) (hl : root < L ls i) :
    ∃ a, a + 1 ≤ i ∧ startsAt ls root a ∧ grp ls root (a + 1) = grp ls root i ∧
      (desc ls root mx i).drop = root ∧ (desc ls root mx i).curr = width ls (a + 1) root mx ∧
      (desc ls root mx i).low = rev root (grp ls root i) := by
  induction i with
  | zero => omega
  | succ i ih =>
    simp only [desc]
    by_cases hs : startsAt ls root i
    · rw [ite_eq_left hs]
      exact ⟨i, Nat.le_refl _, hs, rfl, rfl, rfl, rfl⟩
    · rw [ite_eq_right hs]
      have hli : root < L ls i ∧ grp ls root (i + 1) = grp ls root i := by
        unfold startsAt at hs
        refine Classical.byContradiction fun hc => hs ⟨hl, ?_⟩
        by_cases h1 : L ls i ≤ root
        · exact Or.inl h1
        · exact Or.inr fun he => hc ⟨by omega, he⟩
      obtain ⟨a, ha, hsa, hga, hd, hc, hlow⟩ := ih (by omega) hli.1
      exact ⟨a, by omega, hsa, by rw [hga, hli.2], hd, hc, by rw [hlow, hli.2]⟩

/-- Safety core: every code fits the table it is written into. -/
theorem desc_fits {ls : List Nat} {root mx : Nat} (hc : CompleteCode ls root mx) {i : Nat}
    (hi : i < nz ls) :
    (desc ls root mx i).drop ≤ L ls i ∧
      L ls i - (desc ls root mx i).drop ≤ (desc ls root mx i).curr ∧
      (desc ls root mx i).curr ≤ 15 ∧ (desc ls root mx i).drop ≤ root := by
  have hmx := hc.mx_le
  have hr15 : root ≤ 15 := Nat.le_trans hc.root_le hmx
  by_cases hs : L ls i ≤ root
  · rw [desc_short ls hi hs]; simp [desc]; omega
  · obtain ⟨a, ha, hsa, hga, hd, hcur, _⟩ := desc_long (mx := mx) hc.min_le hi (by omega)
    have hcov := look_covers hc (show a + 1 < nz ls by omega) hsa (show a + 1 ≤ i from ha) hi hga.symm
    have hw := width_spec ls (show a + 1 < nz ls by omega) hmx hsa.1 (hc.L_le_mx (by omega))
    rw [hd, hcur]
    omega

end Zlib.Inftrees.Canon
