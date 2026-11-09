import ZlibF.Spec.Api.Basic

namespace ZlibF.Spec

/-- Independent zlib-wrapper parsing with the dictionary capacity selected
by inflate initialization. With windowBits zero, the header selects that
capacity. With a nonzero value, the configured capacity is retained even
when the header announces a smaller one. This describes default inflate
acceptance with INFLATE_STRICT undefined; the stricter RFC-format
Zlib.Decodes remains unchanged. -/
def Zlib.DecodesWithWindow (windowBits : Nat) (dict stream out : List UInt8) : Prop :=
  ∃ (cmf flg : UInt8) (pre s : List UInt8),
    stream = cmf :: flg :: (pre ++ s) ∧ Zlib.HeaderOK cmf flg ∧
    (flg.toNat / 32 % 2 = 0 → pre = [] ∧
      Deflate.Prefix [] s (be32 (adler32 out).toNat) out) ∧
    (flg.toNat / 32 % 2 = 1 → pre = be32 (adler32 dict).toNat ∧
      Deflate.Prefix
        (dict.drop (dict.length -
          (if windowBits = 0 then Zlib.windowSize cmf else 2 ^ windowBits)))
        s (be32 (adler32 out).toNat) out)

/-- Successful inflate acceptance, separate from the RFC-format premise
used by valid-input prefix and completion claims. Only the zlib dictionary
capacity differs from Layer.Decodes; header, checksum and exact ending
remain mandatory. The selected window must still fit the configuration. -/
def Api.Layer.InflateAccepted (wrap : Api.Wrap) (windowBits : Nat)
    (dict stream out : List UInt8) : Prop :=
  match wrap with
  | .raw => Api.Layer.Decodes .raw windowBits dict stream out
  | .zlib => Zlib.DecodesWithWindow windowBits dict stream out ∧ Api.ZlibFits windowBits stream
  | .gzip => Gzip.Decodes stream out
  | .auto =>
      (Zlib.DecodesWithWindow windowBits dict stream out ∧ Api.ZlibFits windowBits stream) ∨
      Gzip.Decodes stream out

/-- Selecting the window from the header recovers the original relation. -/
theorem Zlib.decodesWithWindow_zero (dict stream out : List UInt8) :
    Zlib.DecodesWithWindow 0 dict stream out ↔ Zlib.Decodes dict stream out := by
  simp only [Zlib.DecodesWithWindow, Zlib.Decodes, ite_true]

end ZlibF.Spec
