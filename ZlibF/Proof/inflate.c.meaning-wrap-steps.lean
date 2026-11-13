import ZlibF.Proof.«inflate.c.meaning-stream»
import ZlibF.Proof.«inflate.c.meaning»

/-!
# inflate.c: the stage steps of the wrapper grammar

Heap-free steps of `WrapParsed` (`inflate.c.meaning`) that the stream-side
mode proofs use: raw data enters the body; a zlib header enters the body or
asks for a dictionary; a dictionary with the requested identifier enters the
body; the gzip magic and every completable gzip beginning stay in the header;
the end of the last block enters the trailer (or the end for raw data); each
trailer byte that matches stays in the trailer or ends the stream.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem bytesToBits_append' (a b : List UInt8) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  simp [bytesToBits]

theorem bytesToBits_length' (a : List UInt8) : (bytesToBits a).length = 8 * a.length := by
  induction a with
  | nil => rfl
  | cons x rest ih =>
    simp only [bytesToBits, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [byteBits]
    omega

/-- `GzipHeader` of the meaning is the complete header of the grammar. -/
theorem gzipHeader_iff {header : List UInt8} : GzipHeader header ↔ GzipFull header := by
  constructor
  · rintro ⟨flg, mt, xfl, os, ex, nm, cm, a, b, c, d, e, eq⟩
    exact ⟨flg, mt, xfl, os, ex, nm, cm, ⟨a, b, c, d, e⟩, by simpa [gzipHcrc] using eq⟩
  · rintro ⟨flg, mt, xfl, os, ex, nm, cm, ⟨a, b, c, d, e⟩, eq⟩
    exact ⟨flg, mt, xfl, os, ex, nm, cm, a, b, c, d, e, by simpa [gzipHcrc] using eq⟩

/-- A gzip beginning that is not yet a complete header is a header stage for
gzip and automatic detection. -/
theorem wrapParsed_gzip_header {wrap : Api.Wrap} {configured : Nat} {dict bytes : List UInt8}
    (gzipLike : wrap = .gzip ∨ wrap = .auto) (viable : GzipViable bytes) (short : GzipShort bytes) :
    WrapParsed wrap configured dict (bytesToBits bytes) (.header bytes) := by
  obtain ⟨header, full, ⟨more, eq⟩⟩ := viable
  refine ⟨rfl, more, [], ?_, Or.inl (short header more full eq)⟩
  rw [eq]
  rcases gzipLike with rfl | rfl
  · exact ⟨gzipHeader_iff.mpr full, rfl⟩
  · exact Or.inr ⟨gzipHeader_iff.mpr full, rfl⟩

/-- The gzip magic. -/
theorem wrapParsed_gzip_magic {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8}
    (gzipLike : wrap = .gzip ∨ wrap = .auto) :
    WrapParsed wrap configured dict (bytesToBits [31, 139]) (.header [31, 139]) :=
  wrapParsed_gzip_header gzipLike gzipViable_magic (gzipShort_of_length (by simp))

/-- Raw data: the empty header is followed by the body. -/
theorem wrapParsed_raw_start {configured : Nat} {dict : List UInt8} :
    WrapParsed .raw configured dict [] (.body [] ⟨[], false, .boundary⟩) :=
  ⟨_, [], ⟨rfl, rfl⟩, by simp [bytesToBits], .start⟩

/-- A zlib header without `FDICT` is followed by the body. -/
theorem wrapParsed_zlib_body {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8}
    {cmf flg : UInt8} (zlibLike : wrap = .zlib ∨ wrap = .auto) (ok : Zlib.HeaderOK cmf flg)
    (fits : Api.ZlibFits configured [cmf, flg]) (plain : flg.toNat / 32 % 2 = 0) :
    WrapParsed wrap configured dict (bytesToBits [cmf, flg])
      (.body [cmf, flg] ⟨[], false, .boundary⟩) := by
  have header : ∃ window, ZlibHeader configured dict [cmf, flg] window ∧
      ([] : List UInt8) = (if [cmf, flg].length = 2 then [] else bodyDictionary window dict) :=
    ⟨_, ⟨cmf, flg, ok, fits, rfl, Or.inl ⟨plain, rfl⟩⟩, by simp⟩
  refine ⟨[], [], ?_, by simp, .start⟩
  rcases zlibLike with rfl | rfl
  · exact header
  · exact Or.inl header

/-- A zlib header with `FDICT`: its identifier is still to be read. -/
theorem wrapParsed_zlib_fdict {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8}
    {cmf flg : UInt8} (zlibLike : wrap = .zlib ∨ wrap = .auto) (ok : Zlib.HeaderOK cmf flg)
    (fits : Api.ZlibFits configured [cmf, flg]) (fdict : flg.toNat / 32 % 2 = 1) :
    WrapParsed wrap configured dict (bytesToBits [cmf, flg]) (.header [cmf, flg]) := by
  have header : ∃ window, ZlibHeader configured dict ([cmf, flg] ++ be32 (adler32 dict).toNat)
      window ∧ bodyDictionary (if configured = 0 then Zlib.windowSize cmf else 2 ^ configured) dict =
        (if ([cmf, flg] ++ be32 (adler32 dict).toNat).length = 2 then []
          else bodyDictionary window dict) :=
    ⟨_, ⟨cmf, flg, ok, fits, rfl, Or.inr ⟨fdict, rfl⟩⟩, by simp [be32]⟩
  refine ⟨rfl, be32 (adler32 dict).toNat,
    bodyDictionary (if configured = 0 then Zlib.windowSize cmf else 2 ^ configured) dict, ?_,
    Or.inl (by simp [be32])⟩
  rcases zlibLike with rfl | rfl
  · exact header
  · exact Or.inl header

/-- After `DICTID`: any identifier asks for the dictionary. -/
theorem wrapParsed_needDict {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8}
    {cmf flg : UInt8} {dictid : List UInt8} (zlibLike : wrap = .zlib ∨ wrap = .auto)
    (ok : Zlib.HeaderOK cmf flg) (fits : Api.ZlibFits configured [cmf, flg])
    (fdict : flg.toNat / 32 % 2 = 1) (length : dictid.length = 4) :
    WrapParsed wrap configured dict (bytesToBits ([cmf, flg] ++ dictid))
      (.needDict ([cmf, flg] ++ dictid)) :=
  ⟨rfl, zlibLike, cmf, flg, dictid, rfl, length, ok, fits, fdict⟩

/-- A dictionary whose Adler-32 is the requested identifier: the body starts,
with the last window of the dictionary. -/
theorem wrapParsed_dictionary_body {wrap : Api.Wrap} {configured : Nat}
    {dict dict' : List UInt8} {consumed : List Bool} {header : List UInt8}
    (needed : WrapParsed wrap configured dict' consumed (.needDict header))
    (identifier : be32 (adler32 dict).toNat = header.drop 2) :
    WrapParsed wrap configured dict consumed (.body header ⟨[], false, .boundary⟩) := by
  obtain ⟨consumedEq, zlibLike, cmf, flg, dictid, rfl, length, ok, fits, fdict⟩ := needed
  have idEq : dictid = be32 (adler32 dict).toNat := by simpa using identifier.symm
  subst idEq
  have header : ∃ window, ZlibHeader configured dict ([cmf, flg] ++ be32 (adler32 dict).toNat)
      window ∧ bodyDictionary (if configured = 0 then Zlib.windowSize cmf else 2 ^ configured) dict =
        (if ([cmf, flg] ++ be32 (adler32 dict).toNat).length = 2 then []
          else bodyDictionary window dict) :=
    ⟨_, ⟨cmf, flg, ok, fits, rfl, Or.inr ⟨fdict, rfl⟩⟩, by simp [be32]⟩
  refine ⟨bodyDictionary (if configured = 0 then Zlib.windowSize cmf else 2 ^ configured) dict,
    [], ?_, by simp [consumedEq], .start⟩
  rcases zlibLike with rfl | rfl
  · exact header
  · exact Or.inl header

/-- The end of the last block: the padding to the byte boundary enters the
trailer, or ends raw data. -/
theorem wrapParsed_body_end {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8}
    {consumed pad : List Bool} {header out : List UInt8}
    (body : WrapParsed wrap configured dict consumed (.body header ⟨out, true, .finished⟩))
    (padLength : pad.length = (8 - consumed.length % 8) % 8) :
    (wrap ≠ .raw → WrapParsed wrap configured dict (consumed ++ pad) (.trailer header out [])) ∧
    (wrap = .raw → WrapParsed wrap configured dict (consumed ++ pad) (.done out)) := by
  obtain ⟨bodyDict, bits, wrapHeader, rfl, parsed⟩ := body
  have aligned : (bytesToBits header ++ bits).length % 8 = bits.length % 8 := by
    rw [List.length_append, bytesToBits_length']
    omega
  rw [aligned] at padLength
  refine ⟨fun wrapped => ⟨bodyDict, bits, pad, wrapHeader, parsed, wrapped, padLength,
    List.nil_prefix, ?_, by simp [bytesToBits]⟩, fun raw => ?_⟩
  · intro empty
    cases wrap with
    | raw => exact wrapped rfl
    | zlib => simp [WrapTrailer, be32] at empty
    | gzip => simp [WrapTrailer, le32] at empty
    | auto =>
      simp only [WrapTrailer] at empty
      split at empty <;> simp [be32, le32] at empty
  · subst raw
    refine ⟨header, bodyDict, bits, pad, wrapHeader, parsed, padLength, ?_⟩
    simp [WrapTrailer, bytesToBits]

/-- Trailer bytes that continue the expected trailer stay in the trailer or
end the stream. -/
theorem wrapParsed_trailer_step {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8}
    {consumed : List Bool} {header out bytes more : List UInt8}
    (trailer : WrapParsed wrap configured dict consumed (.trailer header out bytes))
    (expected : bytes ++ more <+: WrapTrailer wrap header out) :
    (bytes ++ more ≠ WrapTrailer wrap header out →
      WrapParsed wrap configured dict (consumed ++ bytesToBits more)
        (.trailer header out (bytes ++ more))) ∧
    (bytes ++ more = WrapTrailer wrap header out →
      WrapParsed wrap configured dict (consumed ++ bytesToBits more) (.done out)) := by
  obtain ⟨bodyDict, bits, pad, wrapHeader, parsed, wrapped, padLength, _, _, rfl⟩ := trailer
  refine ⟨fun unfinished => ⟨bodyDict, bits, pad, wrapHeader, parsed, wrapped, padLength, expected,
    unfinished, by simp [bytesToBits_append']⟩, fun complete => ⟨header, bodyDict, bits, pad,
    wrapHeader, parsed, padLength, ?_⟩⟩
  rw [← complete]
  simp [bytesToBits_append']

#print axioms wrapParsed_gzip_header
#print axioms wrapParsed_gzip_magic
#print axioms wrapParsed_raw_start
#print axioms wrapParsed_zlib_body
#print axioms wrapParsed_zlib_fdict
#print axioms wrapParsed_needDict
#print axioms wrapParsed_dictionary_body
#print axioms wrapParsed_body_end
#print axioms wrapParsed_trailer_step

end Zlib.Inflate.Proofs
