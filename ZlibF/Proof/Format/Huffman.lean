import ZlibF.Spec.Format.Huffman

/-!
# Format meta-theory: canonical Huffman codes are prefix-free

An `Acceptable` code (in fact any code with all lengths at most 15 that `Fits`) is prefix-free.
Consequence: `decodeSym` does not look beyond the code it finds, so it gives the same symbol on
any extension of the input (`Ext`).
-/

namespace ZlibF.Spec

namespace Proofs

/-- `codeStart` grows at least by a factor 2 per length: the codes of length `l + j + 1` start
after the `(codeStart l + count l) * 2^(j+1)` leaves taken by the codes of length at most `l`. -/
theorem codeStart_ge (lens : List Nat) (l : Nat) (hl : 1 ≤ l) (j : Nat) :
    (codeStart lens l + count lens l) * 2 ^ (j + 1) ≤ codeStart lens (l + j + 1) := by
  induction j with
  | zero =>
    have : l ≠ 0 := by omega
    simp [codeStart, this]
  | succ j ih =>
    have e : codeStart lens (l + (j + 1) + 1) =
        (codeStart lens (l + j + 1) + count lens (l + j + 1)) * 2 := by
      show codeStart lens (l + j + 1 + 1) = _
      simp only [codeStart]
      have : l + j + 1 ≠ 0 := by omega
      simp
    rw [e, Nat.pow_succ 2 (j + 1), ← Nat.mul_assoc]
    omega

theorem natToBitsMSB_length (len v : Nat) : (natToBitsMSB len v).length = len := by
  simp [natToBitsMSB]

theorem natToBitsMSB_getElem (len v i : Nat) (h : i < (natToBitsMSB len v).length) :
    (natToBitsMSB len v)[i] = v.testBit (len - 1 - i) := by
  simp [natToBitsMSB]

/-- If the `l`-bit code of `v` is a prefix of the `l'`-bit code of `v'` (both numbers fit),
then `v` is the top `l` bits of `v'`. -/
theorem natToBitsMSB_prefix {l l' v v' : Nat} (hv : v < 2 ^ l) (hv' : v' < 2 ^ l')
    (h : (natToBitsMSB l v).isPrefixOf (natToBitsMSB l' v') = true) :
    l ≤ l' ∧ v = v' / 2 ^ (l' - l) := by
  have hp : natToBitsMSB l v <+: natToBitsMSB l' v' := List.isPrefixOf_iff_prefix.mp h
  have hlen := hp.length_le
  rw [natToBitsMSB_length, natToBitsMSB_length] at hlen
  refine ⟨hlen, ?_⟩
  rw [← Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight]
  by_cases hj : j < l
  · have hi : l - 1 - j < (natToBitsMSB l v).length := by rw [natToBitsMSB_length]; omega
    have := hp.getElem hi
    rw [natToBitsMSB_getElem, natToBitsMSB_getElem] at this
    have e1 : l - 1 - (l - 1 - j) = j := by omega
    have e2 : l' - 1 - (l - 1 - j) = l' - l + j := by omega
    rw [e1, e2] at this
    rw [this, Nat.add_comm]
  · have h1 : v.testBit j = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : v'.testBit (l' - l + j) = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hv' (Nat.pow_le_pow_right (by omega) (by omega))
    rw [h1, h2]

/-- Position of a symbol of length `l` among the symbols of length `l`. -/
abbrev rk (lens : List Nat) (l s : Nat) : Nat :=
  ((lens.take s).filter (· == l)).length

theorem getD_ne_zero_lt (lens : List Nat) (s : Nat) (hs : lens.getD s 0 ≠ 0) : s < lens.length := by
  rcases Nat.lt_or_ge s lens.length with h | h
  · exact h
  · exfalso; apply hs
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_eq_getElem' (lens : List Nat) (s l : Nat) (h : s < lens.length)
    (hs : lens.getD s 0 = l) : lens[s] = l := by
  rw [← hs]; simp [List.getD_eq_getElem?_getD, h]

theorem rk_lt_count (lens : List Nat) (s l : Nat) (hs : lens.getD s 0 = l) (hl : l ≠ 0) :
    rk lens l s < count lens l := by
  have hlt : s < lens.length := getD_ne_zero_lt lens s (by omega)
  have hg := getD_eq_getElem' lens s l hlt hs
  have e : lens = lens.take s ++ lens.drop s := (List.take_append_drop s lens).symm
  have hd : lens.drop s = lens[s] :: lens.drop (s + 1) := List.drop_eq_getElem_cons hlt
  unfold rk count
  conv => rhs; rw [e, hd]
  rw [List.filter_append, List.length_append, List.filter_cons]
  simp [hg]

theorem rk_strict (lens : List Nat) (s s' l : Nat) (hss : s < s') (hs : lens.getD s 0 = l)
    (hl : l ≠ 0) : rk lens l s < rk lens l s' := by
  have hlt : s < lens.length := getD_ne_zero_lt lens s (by omega)
  have hg := getD_eq_getElem' lens s l hlt hs
  unfold rk
  obtain ⟨m, rfl⟩ : ∃ m, s' = (s + 1) + m := ⟨s' - (s + 1), by omega⟩
  rw [List.take_add, List.filter_append, List.length_append, List.take_add_one]
  simp [List.getElem?_eq_getElem hlt, hg]
  omega

/-- A code that `Fits` and has lengths at most 15 is prefix-free. -/
theorem prefixFree {lens : List Nat} (h15 : ∀ x ∈ lens, x ≤ maxCodeLen) (hf : Fits lens)
    {s s' : Nat} (hs : lens.getD s 0 ≠ 0) (hs' : lens.getD s' 0 ≠ 0)
    (hp : (codeOf lens s).isPrefixOf (codeOf lens s') = true) : s = s' := by
  have hlen : ∀ t, lens.getD t 0 ≠ 0 → 1 ≤ lens.getD t 0 ∧ lens.getD t 0 ≤ 15 := by
    intro t ht
    refine ⟨by omega, ?_⟩
    have hl := getD_ne_zero_lt lens t ht
    have : lens.getD t 0 = lens[t] := by simp [List.getD_eq_getElem?_getD, hl]
    rw [this]; exact h15 _ (List.getElem_mem hl)
  have hv : ∀ t l, lens.getD t 0 = l → l ≠ 0 → codeStart lens l + rk lens l t < 2 ^ l := by
    intro t l hl hl0
    obtain ⟨h1, h2⟩ := hlen t (by omega)
    rw [hl] at h1 h2
    have := hf l (by simp [List.mem_range'_1, maxCodeLen]; omega)
    have := rk_lt_count lens t l hl hl0
    omega
  obtain ⟨l, hl⟩ : ∃ l, lens.getD s 0 = l := ⟨_, rfl⟩
  obtain ⟨l', hl'⟩ : ∃ l', lens.getD s' 0 = l' := ⟨_, rfl⟩
  have hl0 : l ≠ 0 := by omega
  have hl0' : l' ≠ 0 := by omega
  have hp' : (natToBitsMSB l (codeStart lens l + rk lens l s)).isPrefixOf
      (natToBitsMSB l' (codeStart lens l' + rk lens l' s')) = true := by
    simp only [codeOf, hl, hl'] at hp
    exact hp
  obtain ⟨hll, hveq⟩ := natToBitsMSB_prefix (hv s l hl hl0) (hv s' l' hl' hl0') hp'
  have hlen1 : 1 ≤ l := by have := hlen s hs; omega
  rcases Nat.lt_or_ge l l' with hlt | hge
  · exfalso
    obtain ⟨j, hj⟩ : ∃ j, l' = l + j + 1 := ⟨l' - l - 1, by omega⟩
    have h1 := codeStart_ge lens l hlen1 j
    have h2 : l' - l = j + 1 := by omega
    rw [h2] at hveq
    rw [← hj] at h1
    have h3 : (codeStart lens l + count lens l) ≤ (codeStart lens l' + rk lens l' s') / 2 ^ (j + 1) := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
      omega
    have := rk_lt_count lens s l hl hl0
    omega
  · have hll' : l = l' := by omega
    subst hll'
    rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hveq
    have hr : rk lens l s = rk lens l s' := by omega
    refine Classical.byContradiction fun hne => ?_
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := rk_strict lens s s' l h hl hl0
      omega
    · have := rk_strict lens s' s l h hl' hl0
      omega

/-- The decoder does not read past the code it finds: it gives the same symbol on any
extension of the input. -/
def Ext (lens : List Nat) : Prop :=
  ∀ (inp : List Bool) (s : Nat) (r X : List Bool),
    decodeSym lens inp = some (s, r) → decodeSym lens (inp ++ X) = some (s, r ++ X)

theorem ext_of_prefixFree {lens : List Nat}
    (hpf : ∀ {s s' : Nat}, lens.getD s 0 ≠ 0 → lens.getD s' 0 ≠ 0 →
      (codeOf lens s).isPrefixOf (codeOf lens s') = true → s = s') : Ext lens := by
  intro inp s r X h
  unfold decodeSym at h ⊢
  split at h
  · rename_i b hb
    obtain ⟨hb1, as, bs, hsplit, hall⟩ := List.find?_eq_some_iff_append.mp hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb1' := hb1
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb1
    obtain ⟨hne, hpre⟩ := hb1
    have hpre' : (codeOf lens b).isPrefixOf (inp ++ X) = true := by
      have := List.isPrefixOf_iff_prefix.mp hpre
      exact List.isPrefixOf_iff_prefix.mpr (this.trans (List.prefix_append _ _))
    have hnd : (as ++ b :: bs).Nodup := by rw [← hsplit]; exact List.nodup_range
    have hfind : (List.range lens.length).find?
        (fun s => lens.getD s 0 != 0 && (codeOf lens s).isPrefixOf (inp ++ X)) = some b := by
      rw [hsplit, List.find?_append]
      have hnone : as.find? (fun s => lens.getD s 0 != 0 && (codeOf lens s).isPrefixOf (inp ++ X))
          = none := by
        rw [List.find?_eq_none]
        intro a ha
        simp only [Bool.not_eq_true, Bool.and_eq_false_iff, bne_eq_false_iff_eq]
        refine Classical.byContradiction fun hc => ?_
        simp only [not_or, Bool.not_eq_false] at hc
        have hc1 : lens.getD a 0 ≠ 0 := by simpa using hc.1
        have hc2 := hc.2
        have hab : a ≠ b := by
          intro hab
          subst hab
          have := List.nodup_append.mp hnd
          exact this.2.2 a ha a (List.mem_cons_self) rfl
        have h1 := List.isPrefixOf_iff_prefix.mp hc2
        have h2 := List.isPrefixOf_iff_prefix.mp hpre'
        rcases Nat.le_total (codeOf lens a).length (codeOf lens b).length with hle | hle
        · exact hab (hpf hc1 hne (List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le h1 h2 hle)))
        · exact hab (hpf hne hc1 (List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le h2 h1 hle))).symm
      rw [hnone]
      have hpb : (lens.getD b 0 != 0 && (codeOf lens b).isPrefixOf (inp ++ X)) = true := by
        rw [hpre', Bool.and_true]; exact bne_iff_ne.mpr hne
      rw [Option.none_or]
      simp only [List.find?_cons, hpb]
    rw [hfind]
    have hlenb : lens.getD b 0 ≤ inp.length := by
      have := (List.isPrefixOf_iff_prefix.mp hpre).length_le
      simpa [codeOf, natToBitsMSB_length] using this
    simp only [List.drop_append_of_le_length hlenb]
  · simp at h

theorem ext_acceptable {k : CodeKind} {lens : List Nat} (h : Acceptable k lens) : Ext lens :=
  ext_of_prefixFree fun hs hs' hp => prefixFree h.1 h.2.1 hs hs' hp

theorem ext_fixedLit : Ext fixedLitLens :=
  ext_of_prefixFree fun hs hs' hp =>
    prefixFree (by decide +kernel) (by decide +kernel) hs hs' hp

theorem ext_fixedDist : Ext fixedDistLens :=
  ext_of_prefixFree fun hs hs' hp =>
    prefixFree (by decide +kernel) (by decide +kernel) hs hs' hp

end Proofs

end ZlibF.Spec
