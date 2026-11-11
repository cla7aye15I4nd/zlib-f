import ZlibF.Spec.Api.Inflate

open ZlibF.Spec

/-! `TraceEvidence` asked for evidence in `Api.Layer.Decodes` after every
single-dictionary history. The zlib stream below announces a 256-byte window
(`CMF = 08`) and asks for a dictionary (`FDICT`). It was made by deflate from
20 bytes that repeat a 1000-byte preset dictionary at distance 500, with the
header patched (`tests/goals/inflate-meaning/dictionary-beyond-header-window.c`).
inflate configured with windowBits 15 keeps the whole dictionary in its
window, accepts the stream and writes the 20 bytes. `Zlib.Decodes` (RFC 1950)
keeps only the last `Zlib.windowSize 0x08 = 256` bytes of the dictionary, so
distance 500 reaches outside it: inflate with windowBits 8 answers "invalid
distance too far back". No stream that `Api.Layer.Decodes .zlib 15` accepts
begins with the match, so the written bytes have no `OutputEvidence`.
`TraceEvidence` now excludes a zlib dictionary with a configured window: it
asks for no dictionary, raw data, or windowBits 0. -/
namespace DictionaryHeaderWindowRegression

/-- The stream printed by the reproduction. -/
def stream : List UInt8 :=
  [0x08, 0xf6, 0x3e, 0x7b, 0xfc, 0xa8, 0xc3, 0x16, 0xe7, 0x00, 0x69, 0x4d, 0x09, 0xee]

/-- A valid zlib header that sets `FDICT`. -/
theorem header_ok : Zlib.HeaderOK 0x08 0xf6 ∧ (0xf6 : UInt8).toNat / 32 % 2 = 1 := by decide

/-- The header announces a window of 256 bytes. -/
theorem header_window : Zlib.windowSize 0x08 = 256 := by decide

/-- The header fits the configured windowBits 15, so `Api.Layer.Decodes .zlib 15` uses the
RFC window of the header. -/
theorem fits_15 : Api.ZlibFits 15 stream := Or.inr ⟨0x08, rfl, by decide⟩

end DictionaryHeaderWindowRegression
