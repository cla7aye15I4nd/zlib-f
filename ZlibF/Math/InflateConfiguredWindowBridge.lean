import ZlibF.Spec.Api.InflateAccepted
import ZlibF.Proof.Format.Dictionary

namespace ZlibF.Math.InflateConfiguredWindowBridge
open ZlibF.Spec
set_option autoImplicit false

/-- The RFC-format dictionary retained for the announced window is a
suffix of the dictionary retained for a fitting configured window. Its
existing matches therefore keep exactly the same bytes and output. -/
theorem zlib_decodes_with_fitting_window
    {bits : Nat} {dict input output : List UInt8}
    (parsed : Zlib.Decodes dict input output) (fits : Api.ZlibFits bits input) :
    Zlib.DecodesWithWindow bits dict input output := by
  by_cases zero : bits = 0
  · subst bits
    exact (Zlib.decodesWithWindow_zero dict input output).mpr parsed
  obtain ⟨cmf, flg, pre, data, inputEq, header, plain, dictionary⟩ := parsed
  obtain ⟨c, first, capacity⟩ := fits.resolve_left zero
  have same : c = cmf := by
    rw [inputEq] at first
    exact Option.some.inj first.symm
  subst c
  have size : Zlib.windowSize cmf ≤ 2 ^ bits :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) capacity
  have offsets : dict.length - 2 ^ bits ≤ dict.length - Zlib.windowSize cmf := by omega
  have suffix : dict.drop (dict.length - Zlib.windowSize cmf) <:+
      dict.drop (dict.length - 2 ^ bits) := List.drop_suffix_drop_left dict offsets
  refine ⟨cmf, flg, pre, data, inputEq, header, plain, ?_⟩
  intro present
  obtain ⟨id, rest, blocks, padding⟩ := dictionary present
  refine ⟨id, rest, ?_, padding⟩
  simp only [zero, ite_false]
  exact ZlibF.Spec.Proofs.blocks_dictionary_suffix suffix blocks

/-- Every RFC zlib stream fits the default 15-bit configuration. The
larger retained preset dictionary preserves every already-valid match;
no restriction on dictionary size, content, input or output is introduced. -/
theorem zlib_decodes_with_default_window
    {dict input output : List UInt8} (parsed : Zlib.Decodes dict input output) :
    Zlib.DecodesWithWindow 15 dict input output := by
  apply zlib_decodes_with_fitting_window parsed
  obtain ⟨cmf, flg, pre, data, inputEq, header, _plain, _dictionary⟩ := parsed
  refine Or.inr ⟨cmf, ?_, ?_⟩
  · rw [inputEq]
    rfl
  · have limit := header.2.1
    omega

/-- The original configured zlib-format premise implies successful
acceptance's independent byte meaning, preserving its exact output. -/
theorem zlib_layer_decodes_accepted
    {bits : Nat} {dict input output : List UInt8}
    (parsed : Api.Layer.Decodes .zlib bits dict input output) :
    Api.Layer.InflateAccepted .zlib bits dict input output :=
  ⟨zlib_decodes_with_fitting_window parsed.1 parsed.2, parsed.2⟩

/-- Automatic wrapper selection preserves the same valid-format-to-
acceptance implication. The gzip branch is unchanged. -/
theorem auto_layer_decodes_accepted
    {bits : Nat} {dict input output : List UInt8}
    (parsed : Api.Layer.Decodes .auto bits dict input output) :
    Api.Layer.InflateAccepted .auto bits dict input output := by
  rcases parsed with zlib | gzip
  · exact Or.inl (zlib_layer_decodes_accepted zlib)
  · exact Or.inr gzip

/-- For every wrapper and configured window, the unchanged valid-source
format implies the accepted-output relation. This is a pure format bridge,
not a claim that every valid stream succeeds for every caller buffer split. -/
theorem layer_decodes_accepted
    {wrap : Api.Wrap} {bits : Nat} {dict input output : List UInt8}
    (parsed : Api.Layer.Decodes wrap bits dict input output) :
    Api.Layer.InflateAccepted wrap bits dict input output := by
  cases wrap with
  | raw => exact parsed
  | zlib => exact zlib_layer_decodes_accepted parsed
  | gzip => exact parsed
  | auto => exact auto_layer_decodes_accepted parsed

#print axioms zlib_decodes_with_fitting_window
#print axioms zlib_decodes_with_default_window
#print axioms zlib_layer_decodes_accepted
#print axioms auto_layer_decodes_accepted
#print axioms layer_decodes_accepted
end ZlibF.Math.InflateConfiguredWindowBridge
