import ZlibF.Spec.Api.Inflate

/-!
# Dictionary independence for wrapped streams

This format-level bridge replaces the supplied dictionary when a non-raw
stream does not request one. It does not assert a property of the translated
decoder or change the API model's causal conditions.
-/

namespace ZlibF.Spec.Api.Proofs

open ZlibF.Spec

private theorem zlib_decodes_dictionary_irrelevant
    {w : Wrap} {b : Nat} {d1 d2 stream output : List UInt8}
    (hw : w = .zlib ∨ w = .auto) (hn : ¬ HdrNeedsDict w b stream)
    (hf : ZlibFits b stream) (hd : Zlib.Decodes d1 stream output) :
    Zlib.Decodes d2 stream output := by
  rcases hd with ⟨cmf, flg, pre, s, hs, hh, hclear, _⟩
  refine ⟨cmf, flg, pre, s, hs, hh, hclear, ?_⟩
  intro hset
  exact False.elim (hn ⟨hw, cmf, flg, pre ++ s, hs, hh, hset, hf⟩)

/-- A wrapped stream that does not request a preset dictionary decodes to the
same output for every supplied dictionary. Raw streams are excluded because
their back-references can use the dictionary without an announcing header. -/
theorem layer_decodes_dictionary_irrelevant
    {w : Wrap} {b : Nat} {d1 d2 stream output : List UInt8}
    (hw : w ≠ .raw) (hn : ¬ HdrNeedsDict w b stream)
    (hd : Layer.Decodes w b d1 stream output) :
    Layer.Decodes w b d2 stream output := by
  cases w with
  | raw => exact False.elim (hw rfl)
  | zlib =>
    rcases hd with ⟨hz, hf⟩
    exact ⟨zlib_decodes_dictionary_irrelevant (Or.inl rfl) hn hf hz, hf⟩
  | gzip => exact hd
  | auto =>
    rcases hd with ⟨hz, hf⟩ | hg
    · exact Or.inl ⟨zlib_decodes_dictionary_irrelevant (Or.inr rfl) hn hf hz, hf⟩
    · exact Or.inr hg

end ZlibF.Spec.Api.Proofs
