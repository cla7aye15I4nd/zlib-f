import ZlibF.Proof.«inffixed.h.fixed-stability»

namespace Zlib.InffixedH.Proofs
open C ZlibF.Spec Zlib.Inftrees Zlib.Inftrees.Spec
open DecodeSemantics DecodeSoundness
set_option autoImplicit false
set_option maxRecDepth 100000

theorem lenfix_root_safe : RootTable.Safe Zlib.InffixedH.lenfix 0 9 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i inside
  have bound : i < 512 := by simpa using inside
  have width := lenfix_widths ⟨i, bound⟩
  exact ⟨_, by simpa only [Nat.zero_add] using
    (show Zlib.InffixedH.lenfix[i]? = some (Zlib.InffixedH.lenfix[i]!) by simp [lenfix_size, bound]),
    by omega, width.2⟩

theorem distfix_root_safe : RootTable.Safe Zlib.InffixedH.distfix 0 5 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i inside
  have bound : i < 32 := by simpa using inside
  have width := distfix_widths ⟨i, bound⟩
  change (Zlib.InffixedH.distfix[i]!).bits.toNat = 5 at width
  exact ⟨_, by simpa only [Nat.zero_add] using
    (show Zlib.InffixedH.distfix[i]? = some (Zlib.InffixedH.distfix[i]!) by simp [distfix_size, bound]),
    by rw [width]; decide, by rw [width]; decide⟩

theorem lenfix_no_fast_links : ∀ i : Fin 512,
    ¬ Zlib.Inffast.Spec.LenLink (Zlib.InffixedH.lenfix[i.val]!) := by
  decide +kernel

theorem distfix_no_fast_links : ∀ i : Fin 32,
    ¬ Zlib.Inffast.Spec.DistLink (Zlib.InffixedH.distfix[i.val]!) := by
  decide +kernel

theorem lenfix_read_extent : TableReadExtent LENS Zlib.InffixedH.lenfix 0 9 512 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i inside
  dsimp only
  intro link
  have bound : i < 512 := by simpa using inside
  rcases link with ⟨_, linked⟩ | ⟨wrong, _⟩
  · apply False.elim
    apply lenfix_no_fast_links ⟨i, bound⟩
    simpa only [Nat.zero_add, Array.getElem!_eq_getD] using linked
  · cases wrong

theorem distfix_read_extent : TableReadExtent DISTS Zlib.InffixedH.distfix 0 5 32 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i inside
  dsimp only
  intro link
  have bound : i < 32 := by simpa using inside
  rcases link with ⟨wrong, _⟩ | ⟨_, linked⟩
  · cases wrong
  · apply False.elim
    apply distfix_no_fast_links ⟨i, bound⟩
    simpa only [Nat.zero_add, Array.getElem!_eq_getD] using linked

theorem fixed_lit_acceptable : Acceptable .litLen fixedLitLens := by
  decide +kernel

theorem fixed_dist_acceptable : Acceptable .dist fixedDistLens := by
  decide +kernel

/-- The real fixed static array has the same semantic interface as a
constructed dynamic table. No incoming static-table invariant is assumed. -/
theorem lenfix_decode_invariant : DecodeTableInvariant.Inv LENS Zlib.InffixedH.lenfix 0 9 512 fixedLitLens := by
  refine ⟨Or.inl rfl, lenfix_root_safe, ?_, lenfix_read_extent, fixed_lit_acceptable, ?_, ?_⟩
  · intro i entry inside get linked
    have bound : i < 512 := by simpa using inside
    have cell : Zlib.InffixedH.lenfix[i]? = some (Zlib.InffixedH.lenfix[i]!) := by simp [lenfix_size, bound]
    have get' : Zlib.InffixedH.lenfix[i]? = some entry := by simpa only [Nat.zero_add] using get
    have same : entry = Zlib.InffixedH.lenfix[i]! := Option.some.inj (get'.symm.trans cell)
    subst entry
    have noLink := lenfix_no_links ⟨i, bound⟩
    exact False.elim (noLink (by simpa only [Subtable.IsLink, ite_true] using linked))
  · intro inp entry used query fits accepted
    have enough : 9 ≤ (DecodeShort.padded inp).length := by
      have total := Zlib.Inftrees.Proofs.padded_length inp
      omega
    obtain ⟨symbol, rest, actual, decoded, selected, length, _rest, meaning, classification⟩ :=
      lenfix_full_input (DecodeShort.padded inp) enough
    obtain ⟨sameEntry, sameUsed⟩ := Prod.mk.inj (Option.some.inj (query.symm.trans selected))
    subst actual used
    have original := Zlib.Inftrees.Proofs.decode_unpad fixed_lit_acceptable decoded length fits
    exact ⟨symbol, classification.mp accepted, meaning, length, original,
      fun more => ZlibF.Spec.Proofs.ext_fixedLit inp symbol (inp.drop entry.bits.toNat) more original⟩
  · intro inp enough
    obtain ⟨symbol, rest, entry, decoded, query, _length, _rest, _meaning, classification⟩ :=
      lenfix_full_input inp (by omega)
    refine ⟨entry, entry.bits.toNat, query, ?_⟩
    constructor
    · intro accepted
      exact ⟨symbol, rest, decoded, classification.mp accepted⟩
    · rintro ⟨other, suffix, observed, valid⟩
      have same : other = symbol := congrArg Prod.fst (Option.some.inj (observed.symm.trans decoded))
      exact classification.mpr (by simpa only [same] using valid)

theorem distfix_decode_invariant : DecodeTableInvariant.Inv DISTS Zlib.InffixedH.distfix 0 5 32 fixedDistLens := by
  refine ⟨Or.inr rfl, distfix_root_safe, ?_, distfix_read_extent, fixed_dist_acceptable, ?_, ?_⟩
  · intro i entry inside get linked
    have bound : i < 32 := by simpa using inside
    have cell : Zlib.InffixedH.distfix[i]? = some (Zlib.InffixedH.distfix[i]!) := by simp [distfix_size, bound]
    have get' : Zlib.InffixedH.distfix[i]? = some entry := by simpa only [Nat.zero_add] using get
    have same : entry = Zlib.InffixedH.distfix[i]! := Option.some.inj (get'.symm.trans cell)
    subst entry
    have noLink := distfix_no_links ⟨i, bound⟩
    have zero : (Zlib.InffixedH.distfix[i]!).op &&& 0xf0 = 0 := by
      simpa only [Subtable.IsLink, show ¬ (DISTS = LENS) from by decide, ite_false, beq_iff_eq] using linked
    exact False.elim (by simp only [zero, bne_self_eq_false, Bool.false_eq_true] at noLink)
  · intro inp entry used query fits accepted
    have enough : 5 ≤ (DecodeShort.padded inp).length := by
      have total := Zlib.Inftrees.Proofs.padded_length inp
      omega
    obtain ⟨symbol, rest, actual, decoded, selected, length, _rest, meaning, classification⟩ :=
      distfix_full_input (DecodeShort.padded inp) enough
    obtain ⟨sameEntry, sameUsed⟩ := Prod.mk.inj (Option.some.inj (query.symm.trans selected))
    subst actual used
    have original := Zlib.Inftrees.Proofs.decode_unpad fixed_dist_acceptable decoded length fits
    exact ⟨symbol, classification.mp accepted, meaning, length, original,
      fun more => ZlibF.Spec.Proofs.ext_fixedDist inp symbol (inp.drop entry.bits.toNat) more original⟩
  · intro inp enough
    obtain ⟨symbol, rest, entry, decoded, query, _length, _rest, _meaning, classification⟩ :=
      distfix_full_input inp (by omega)
    refine ⟨entry, entry.bits.toNat, query, ?_⟩
    constructor
    · intro accepted
      exact ⟨symbol, rest, decoded, classification.mp accepted⟩
    · rintro ⟨other, suffix, observed, valid⟩
      have same : other = symbol := congrArg Prod.fst (Option.some.inj (observed.symm.trans decoded))
      exact classification.mpr (by simpa only [same] using valid)

#print axioms lenfix_decode_invariant
#print axioms distfix_decode_invariant
end Zlib.InffixedH.Proofs
