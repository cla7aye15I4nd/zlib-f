import ZlibF.Spec.Api.InflateAccepted

/-! # Successful acceptance without a preset dictionary

The configured-window acceptance relation changes only the retained dictionary.
With no dictionary it is exactly the original format relation. This bridge
does not assert any translated decoder or utility execution theorem.
-/
namespace ZlibF.Spec
set_option autoImplicit false

theorem Zlib.decodesWithWindow_nil (windowBits : Nat) (stream out : List UInt8) :
    Zlib.DecodesWithWindow windowBits [] stream out ↔ Zlib.Decodes [] stream out := by
  simp only [Zlib.DecodesWithWindow, Zlib.Decodes, List.length_nil,
    Nat.zero_sub, List.drop_nil]

theorem Api.Layer.inflateAccepted_nil (wrap : Api.Wrap) (windowBits : Nat)
    (stream out : List UInt8) :
    Api.Layer.InflateAccepted wrap windowBits [] stream out ↔
      Api.Layer.Decodes wrap windowBits [] stream out := by
  cases wrap <;>
    simp only [Api.Layer.InflateAccepted, Api.Layer.Decodes, Zlib.decodesWithWindow_nil]

#print axioms Zlib.decodesWithWindow_nil
#print axioms Api.Layer.inflateAccepted_nil
end ZlibF.Spec
