import ZlibF.Spec.Api.Examples

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

private theorem compressParams_wrap {level : Int} {p : DeflParams}
    (h : compressParams level = some p) : p.wrap = .zlib := by
  simp [compressParams, deflInit?] at h
  split at h <;> rcases h with ⟨_, he⟩ <;> cases he <;> rfl

private theorem compress_decodes {level : Int} {src dst : List UInt8} {cap : Nat}
    (h : Compress2 true level src cap Z.ok dst) :
    Zlib.Decodes [] dst src ∧ ¬ HdrNeedsDict .zlib 15 dst := by
  cases hp : compressParams level with
  | none => simp [Compress2, hp, Z.ok, Z.streamError] at h
  | some p =>
    simp only [Compress2, Bool.true_eq_false, ↓reduceIte, hp] at h
    rcases h with ⟨he, _⟩ | ⟨_, hv, _, _⟩ | ⟨he, _, _, _⟩
    · cases he
    · have hw := compressParams_wrap hp
      simp only [DeflState.Valid, DeflState.fresh, hw, DeflState.dictEff, Option.getD_none] at hv
      refine ⟨hv.1, ?_⟩
      rintro ⟨_, cmf, flg, rest, he, _, hflag, _⟩
      obtain ⟨cmf', flg', rest', he', hnot⟩ := hv.2.2
      rw [he] at he'
      simp only [List.cons.injEq] at he'
      obtain ⟨rfl, rfl, _⟩ := he'
      exact (hnot.mp hflag) rfl
    · cases he

/-- The abstract compression and decompression relations round-trip without allocation failure. -/
theorem compress_roundtrip : Goal.compress_roundtrip := by
  intro level src cap cap2 dst src2 used rc2 hc hcap hu
  obtain ⟨hdecode, hnodict⟩ := compress_decodes hc
  simp only [Uncompress2, Bool.true_eq_false, ↓reduceIte] at hu
  obtain ⟨hused, _, _, hok, _, _, _, hlive⟩ := hu
  have hl := hlive dst.length src (Nat.le_refl _) (by simpa using hdecode)
  have hrc : rc2 = Z.ok ∨ rc2 = Z.memError := (hl.2 (by simpa using hnodict)).1 hcap
  constructor
  · intro hr
    have hdec2 := hok hr
    have he : dst.take used ++ dst.drop used = dst := List.take_append_drop used dst
    have hdecode' : Zlib.Decodes [] (dst.take used ++ dst.drop used) src := by simpa [he] using hdecode
    obtain ⟨hdrop, hout⟩ := Zlib.ext hdec2 hdecode'
    constructor
    · exact hout
    · have hd := congrArg List.length hdrop
      simp only [List.length_drop, List.length_nil] at hd
      omega
  · intro hne
    exact hrc.resolve_left hne

#print axioms compress_roundtrip
end ZlibF.Spec.Api.Proofs
