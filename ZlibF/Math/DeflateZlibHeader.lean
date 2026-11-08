import ZlibF.Math.DeflateZlibEncoding

/-! # Independent zlib validity permits every valid dictionary-free header -/

namespace ZlibF.Math.DeflateEncoding
open ZlibF.Spec
set_option autoImplicit false

/-- A valid dictionary-free header wraps any independently valid raw stream. -/
theorem raw_valid_zlib_header {input raw : List UInt8} {cmf flg : UInt8}
    (valid : Deflate.Valid input raw) (header : Zlib.HeaderOK cmf flg)
    (plain : flg.toNat / 32 % 2 = 0) :
    Zlib.Valid input ([cmf, flg] ++ raw ++ be32 (adler32 input).toNat) := by
  refine ⟨cmf, flg, [], raw ++ be32 (adler32 input).toNat, rfl, header, ?_, ?_⟩
  · intro _
    exact ⟨rfl, raw_valid_trailer_prefix valid _⟩
  · intro impossible
    rw [plain] at impossible
    contradiction

/-- Replace only the two dictionary-free header bytes. The exact body,
checksum trailer and independent decode remain unchanged. This lets an
existing raw-data execution proof serve all compression-level flags. -/
theorem zlib_valid_replace_default_header {input payload : List UInt8} {cmf flg : UInt8}
    (valid : Zlib.Valid input ([120, 156] ++ payload))
    (header : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0) :
    Zlib.Valid input ([cmf, flg] ++ payload) := by
  obtain ⟨oldCmf, oldFlg, pre, stream, shape, _oldHeader, parse, _dictionary⟩ := valid
  have split : (120 : UInt8) = oldCmf ∧ (156 : UInt8) = oldFlg ∧ payload = pre ++ stream := by
    simpa only [List.cons_append, List.nil_append, List.cons.injEq] using shape
  obtain ⟨rfl, rfl, suffix⟩ := split
  obtain ⟨rfl, decoded⟩ := parse (by decide)
  simp only [List.nil_append] at suffix
  subst stream
  refine ⟨cmf, flg, [], payload, rfl, header, ?_, ?_⟩
  · intro _
    exact ⟨rfl, decoded⟩
  · intro impossible
    rw [plain] at impossible
    contradiction

end ZlibF.Math.DeflateEncoding
