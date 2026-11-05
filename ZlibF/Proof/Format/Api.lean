import ZlibF.Spec.Api.Goals
import ZlibF.Proof.Format.Wrapper

/-!
# Proofs: the format is deterministic and self-delimiting

`Goal.format_deterministic` and `Goal.format_prefix_free`. Both follow from `Layer.ext`: if `z` and
`z ++ t` are complete streams of the layer (same configuration and dictionary), then `t = []` and
the outputs are equal. The proof does not use any window-size hypothesis: neither goal mentions
`FullWindow`, and the dictionary and the window only select which back-references are allowed,
never how the stream is cut into fields.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

namespace Proofs

/-- A complete stream of any layer has no complete extension, and its output is determined
(the dictionary and the configuration are fixed). -/
theorem Layer.ext {w : Wrap} {b : Nat} {d z t o1 o2 : List UInt8}
    (h1 : Layer.Decodes w b d z o1) (h2 : Layer.Decodes w b d (z ++ t) o2) :
    t = [] ∧ o1 = o2 := by
  cases w with
  | raw =>
    obtain ⟨hl, ho⟩ := Prefix.ext h1 h2
    exact ⟨List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at hl; omega), ho⟩
  | zlib => exact Zlib.ext h1.1 h2.1
  | gzip => exact Gzip.ext h1 h2
  | auto =>
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Zlib.ext h1.1 h2.1
    · exfalso
      obtain ⟨cmf, r, hz, hc⟩ := zlib_head h1.1
      obtain ⟨r2, hg⟩ := gzip_head h2
      rw [hz] at hg
      simp only [List.cons_append, List.cons.injEq] at hg
      rw [hg.1] at hc
      exact absurd hc (by decide)
    · exfalso
      obtain ⟨cmf, r, hz, hc⟩ := zlib_head h2.1
      obtain ⟨r2, hg⟩ := gzip_head h1
      rw [hg] at hz
      simp only [List.cons_append, List.cons.injEq] at hz
      rw [← hz.1] at hc
      exact absurd hc (by decide)
    · exact Gzip.ext h1 h2

/-- Decoding is a function: one stream has one decoding. -/
theorem format_deterministic : Goal.format_deterministic := by
  intro w b d z o1 o2 h1 h2
  exact (Layer.ext h1 (by simpa using h2) : [] = [] ∧ o1 = o2).2

/-- A complete stream has no complete extension: where a stream ends is determined by its bytes. -/
theorem format_prefix_free : Goal.format_prefix_free := by
  intro w b d z t o1 o2 h1 h2
  exact (Layer.ext h1 h2).1

end Proofs

end ZlibF.Spec.Api
