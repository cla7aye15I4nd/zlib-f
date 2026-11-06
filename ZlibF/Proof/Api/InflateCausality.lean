import ZlibF.Spec.Api.Inflate
import ZlibF.Proof.Format.Api
import ZlibF.Math.InflatePrefixes

/-!
# Causal output evidence

These proofs concern the heap-free API model. They establish the relationship between
bit-prefix evidence and byte-prefix determinacy, and a concrete delayed-error regression.
They do not assert refinement of the translated implementation.
-/

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

set_option maxRecDepth 100000

/-- The universal part of causal evidence entails the original byte-based determinacy. -/
theorem output_evidence_determined {w : Wrap} {b : Nat} {allowed : List UInt8 → Prop}
    {input output : List UInt8} (h : Layer.OutputEvidence w b allowed input output) :
    ∀ d, allowed d → Layer.Determined w b d input output := by
  obtain ⟨pfx, hp, _, hu⟩ := h
  intro d ha stream decoded hc hd
  exact hu d stream decoded ha (bit_compatible_of_byte_compatible hp hc) hd

/-- An empty output has causal evidence when an allowed valid stream exists. -/
theorem output_evidence_nil {w : Wrap} {b : Nat} {allowed : List UInt8 → Prop}
    {dictionary stream decoded : List UInt8} (ha : allowed dictionary)
    (hd : Layer.Decodes w b dictionary stream decoded) (input : List UInt8) :
    Layer.OutputEvidence w b allowed input [] := by
  refine ⟨[], List.nil_prefix, ⟨dictionary, stream, decoded, ha, Or.inl List.nil_prefix, hd⟩, ?_⟩
  intro _ _ _ _ _ _
  exact List.nil_prefix

/-- A complete stream provides causal evidence when the dictionary is fixed. -/
theorem output_evidence_of_decodes {w : Wrap} {b : Nat} {allowed : List UInt8 → Prop}
    {dictionary input output : List UInt8} (ha : allowed dictionary)
    (hfixed : ∀ d, allowed d → d = dictionary)
    (hd : Layer.Decodes w b dictionary input output) :
    Layer.OutputEvidence w b allowed input output := by
  refine ⟨bytesToBits input, List.prefix_refl _,
    ⟨dictionary, input, output, ha, Or.inl (List.prefix_refl _), hd⟩, ?_⟩
  intro d stream decoded had hc hs
  obtain rfl := hfixed d had
  rcases hc with hc | hc
  · obtain ⟨tail, heq⟩ := bytesToBits_prefix_reflect hc
    have hx := Layer.ext hd (by simpa only [← heq] using hs)
    simpa only [← hx.2] using List.prefix_refl output
  · obtain ⟨tail, heq⟩ := bytesToBits_prefix_reflect hc
    have hx := Layer.ext hs (by simpa only [← heq] using hd)
    simpa only [hx.2] using List.prefix_refl output

private theorem copyBack_prefix (dict : List UInt8) (dist n : Nat) (h : List UInt8) :
    h <+: copyBack dict dist n h := by
  induction n generalizing h with
  | zero => exact List.prefix_refl _
  | succ n ih => exact (List.prefix_append _ _).trans (ih _)

private theorem symbols_output_prefix {L D : List Nat} {dict h : List UInt8}
    {inp rest : List Bool} {out : List UInt8} (hs : Symbols L D dict h inp rest out) :
    h <+: out := by
  induction hs with
  | eob => exact List.prefix_refl _
  | lit _ _ _ ih => exact (List.prefix_append _ _).trans ih
  | copy _ _ _ _ _ _ _ _ _ ih => exact (copyBack_prefix _ _ _ _).trans ih

private theorem literal65 (tail : List Bool) :
    decodeSym fixedLitLens
      ([false, true, true, true, false, false, false, true] ++ tail) = some (65, tail) := by
  simpa only [List.nil_append] using
    ZlibF.Spec.Proofs.ext_fixedLit _ _ _ tail
      (by decide +kernel : decodeSym fixedLitLens
        [false, true, true, true, false, false, false, true] = some (65, []))

private theorem deferred_valid_completion :
    Layer.Decodes .raw 15 [] [115, 4, 0] [65] :=
  ⟨_, .last rfl rfl (.fixed (.lit (s := 65) rfl (by decide) (.eob rfl))), by decide⟩

private theorem deferred_bits_force_output {stream decoded : List UInt8}
    (hp : [true, true, false, false, true, true, true, false, false, false, true] <+:
      bytesToBits stream) (hd : Deflate.Decodes [] stream decoded) : [65] <+: decoded := by
  obtain ⟨tail, heq⟩ := hp
  obtain ⟨rest, hb, _⟩ := hd
  rw [← heq] at hb
  cases hb with
  | more h1 =>
    change some (1, _) = some (0, _) at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    omega
  | last h1 h2 hbody =>
    change some (1, _) = some (1, _) at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨_, rfl⟩ := h1
    change some (1, _) = some (_, _) at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | fixed hs =>
      change Symbols fixedLitLens fixedDistLens [] []
        ([false, true, true, true, false, false, false, true] ++ tail) rest decoded at hs
      cases hs with
      | eob h => rw [literal65] at h; simp at h
      | copy h hlow =>
        rw [literal65] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        omega
      | lit h _ hs =>
        rw [literal65] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact symbols_output_prefix hs

/-- The eleven checked bits end after literal 65; the invalid distance is still lookahead. -/
theorem deferred_distance_output_evidence :
    (InflState.fresh .raw 15).Consistent [115, 4, 66] [65] := by
  refine ⟨[true, true, false, false, true, true, true, false, false, false, true],
    by decide +kernel, ⟨[], [115, 4, 0], [65], Or.inr rfl, Or.inl (by decide +kernel),
      deferred_valid_completion⟩, ?_⟩
  intro dictionary stream decoded hdictionary hcompatible hdecode
  have hdict : dictionary = [] := by simpa [InflState.PermitsDictionary, InflState.fresh] using hdictionary
  subst dictionary
  change Layer.Decodes .raw 15 [] stream decoded at hdecode
  rcases hcompatible with hcompatible | hcompatible
  · exact deferred_bits_force_output hcompatible hdecode
  · have hp : bytesToBits stream <+: bytesToBits [115, 4, 0] :=
      hcompatible.trans (by decide +kernel)
    obtain ⟨tail, heq⟩ := bytesToBits_prefix_reflect hp
    have hx := Layer.ext hdecode (by simpa only [← heq] using deferred_valid_completion)
    simpa only [hx.2] using List.prefix_refl [65]

private theorem length257 (tail : List Bool) :
    decodeSym fixedLitLens
      ([false, false, false, false, false, false, true] ++ tail) = some (257, tail) := by
  simpa only [List.nil_append] using
    ZlibF.Spec.Proofs.ext_fixedLit _ _ _ tail
      (by decide +kernel : decodeSym fixedLitLens
        [false, false, false, false, false, false, true] = some (257, []))

private theorem distance1 (tail : List Bool) :
    decodeSym fixedDistLens ([false, false, false, false, true] ++ tail) = some (1, tail) := by
  simpa only [List.nil_append] using
    ZlibF.Spec.Proofs.ext_fixedDist _ _ _ tail
      (by decide +kernel : decodeSym fixedDistLens [false, false, false, false, true] = some (1, []))

private theorem deferred_invalid_prefix (tail out : List UInt8) :
    ¬ Deflate.Decodes [] ([115, 4, 66] ++ tail) out := by
  rintro ⟨rest, hb, _⟩
  cases hb with
  | more h1 =>
    change some (1, _) = some (0, _) at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    omega
  | last h1 h2 hbody =>
    change some (1, _) = some (1, _) at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨_, rfl⟩ := h1
    change some (1, _) = some (_, _) at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | fixed hs =>
      change Symbols fixedLitLens fixedDistLens [] []
        ([false, true, true, true, false, false, false, true] ++
          [false, false, false, false, false, false, true,
           false, false, false, false, true, false] ++ bytesToBits tail) rest out at hs
      cases hs with
      | eob h => rw [List.append_assoc, literal65] at h; simp at h
      | copy h hlow =>
        rw [List.append_assoc, literal65] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        omega
      | lit h _ hs =>
        rw [List.append_assoc, literal65] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        change Symbols fixedLitLens fixedDistLens [] [65]
          ([false, false, false, false, false, false, true] ++
            [false, false, false, false, true, false] ++ bytesToBits tail) rest out at hs
        cases hs with
        | eob h => rw [List.append_assoc, length257] at h; simp at h
        | lit h hlt =>
          rw [List.append_assoc, length257] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          omega
        | copy h _ _ hl hd _ hx hbound =>
          rw [List.append_assoc, length257] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          change some (0, _) = some (_, _) at hl
          simp only [Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          change decodeSym fixedDistLens
            ([false, false, false, false, true] ++ (false :: bytesToBits tail)) = some (_, _) at hd
          rw [distance1] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          change some (0, _) = some (_, _) at hx
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, _⟩ := hx
          exact absurd hbound (by decide)


private theorem deferred_no_complete_prefix (n : Nat) (output : List UInt8) :
    ¬ Layer.Decodes .raw 15 [] ([115, 4, 66, 0].take n) output := by
  intro hd
  by_cases hn : 3 ≤ n
  · have heq : ([115, 4, 66, 0] : List UInt8).take n = [115, 4, 66] ++ [0].take (n - 3) := by
      change (([115, 4, 66] : List UInt8) ++ [0]).take n = _
      rw [List.take_append, List.take_of_length_le hn]
      rfl
    rw [heq] at hd
    exact deferred_invalid_prefix _ _ hd
  · have hp : ([115, 4, 66, 0] : List UInt8).take n <+: [115, 4, 0] := by
      have hc : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hc with rfl | rfl | rfl <;> decide
    obtain ⟨tail, heq⟩ := hp
    have hx := Layer.ext hd (by simpa only [← heq] using deferred_valid_completion)
    have hlen := congrArg List.length heq
    rw [hx.1] at hlen
    simp only [List.length_append, List.length_nil, Nat.add_zero, List.length_take,
      List.length_cons] at hlen
    omega

/-- The former whole-lookahead condition rejects the actual first call. This proof uses
the old predicate, which remains available separately from the corrected causal relation. -/
theorem inflate_deferred_distance_rejects_legacy_consistency :
    ¬ Layer.Consistent .raw 15 [] [115, 4, 66] [65] := by
  intro h
  rcases h with h | ⟨tail, output, n, hn, hd, _⟩
  · have bad := h.1
    simp [hdrLag] at bad
  · have heq : (([115, 4, 66] : List UInt8) ++ tail).take n =
        [115, 4, 66] ++ tail.take (n - 3) := by
      rw [List.take_append, List.take_of_length_le hn]
      rfl
    change Deflate.Decodes [] ((([115, 4, 66] : List UInt8) ++ tail).take n) output at hd
    rw [heq] at hd
    exact deferred_invalid_prefix _ _ hd

/-- The model admits the real first call before the invalid distance is checked. -/
theorem inflate_deferred_distance : Goal.inflate_deferred_distance := by
  refine ⟨{ (InflState.fresh .raw 15) with
    seen := [115, 4, 66]
    out := [65]
    totalIn := 3
    totalOut := 1 }, ?_⟩
  unfold InflRunOk
  and_intros
  all_goals first
    | rfl
    | decide
    | (intro h; exact absurd h (by decide))
    | (intro _ h; exact absurd h (by decide))
    | (intro _; exact ⟨Or.inl (by decide), by decide, rfl⟩)
    | (intro _ _; exact deferred_distance_output_evidence)
    | (intro _; exact Or.inl rfl)
    | (intro _ _ _ _ ⟨n, output, _, _, hd, _, _⟩;
       exact False.elim (deferred_no_complete_prefix n output hd))
    | (intro _ _ _ _ h; exact absurd h (by decide))
    | (intro _ _ h; exact absurd h (by decide))
    | (intro _ h; exact absurd h (by decide))
    | (intro _ _; exact output_evidence_determined deferred_distance_output_evidence)
    | (intro req h; cases h)

end ZlibF.Spec.Api.Proofs
