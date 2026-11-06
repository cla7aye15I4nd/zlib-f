import ZlibF.Spec.Format.Wrapper

/-!
# Format: sanity examples

These `example`s are the tests of the specification (there is no other check that the
definitions say what the RFCs say). Every rule of `docs/spec/format.md` has a positive
and a negative example. Facts about a definition are proved by `decide` (kernel
evaluation, no extra axiom); a derivation of a relation is built from its constructors, with
`rfl` filling in the symbols and the bits that are left. All evaluation is kernel checked.

Byte lists were produced by zlib itself (raw deflate, `Z_FIXED`), except the dynamic block
and the invalid streams, which were written by hand and checked against zlib.
-/

namespace ZlibF.Spec

set_option maxRecDepth 100000

/-- Kernel evaluation of a decidable proposition. -/
local macro "dk" : term => `(by decide +kernel)

/-- Evaluate a reader hypothesis `readBits .. = some (..)` or `decodeSym .. = some (..)` of a
concrete input, and split the equation. Used to invert derivations in the negative examples. -/
local macro "ev " h:ident : tactic =>
  `(tactic| (change some (_, _) = some (_, _) at $h:ident
             simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident))

/-! ## Checksums (`F-adler-incremental`, `F-crc-incremental`) -/

/-- "Wikipedia" (RFC 1950 example, Wikipedia article). -/
example : adler32 [0x57, 0x69, 0x6B, 0x69, 0x70, 0x65, 0x64, 0x69, 0x61] = 0x11E60398 := by decide
example : adler32 [] = 1 := by decide
/-- "123456789", the standard CRC-32 check value. -/
example : crc32 [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xCBF43926 := by decide
example : crc32 [] = 0 := by decide
/-- Incremental: "1234" then "56789". -/
example : crc32Update (crc32 [0x31, 0x32, 0x33, 0x34]) [0x35, 0x36, 0x37, 0x38, 0x39] = 0xCBF43926 := by
  decide
example : adler32Update (adler32 [0x57, 0x69, 0x6B, 0x69]) [0x70, 0x65, 0x64, 0x69, 0x61] = 0x11E60398 := by
  decide
/-- Negative: a different input gives a different value. -/
example : adler32 [0x57, 0x69, 0x6B, 0x69, 0x70, 0x65, 0x64, 0x69, 0x62] ≠ 0x11E60398 := by decide
example : crc32 [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x38] ≠ 0xCBF43926 := by decide

/-! ## Bit order (`F-bit-order`) -/

/-- Data in least significant bit first: 0x05 = 1,0,1,0,0,0,0,0. -/
example : byteBits 0x05 = [true, false, true, false, false, false, false, false] := by decide
/-- A number is read least significant bit first: bits 1,0,1 are 5. -/
example : readBits 3 [true, false, true, false] = some (5, [false]) := by decide
/-- A Huffman code is written most significant bit first: 5 in 4 bits is 0,1,0,1. -/
example : natToBitsMSB 4 5 = [false, true, false, true] := by decide
/-- Negative: too few bits. -/
example : readBits 3 [true, false] = none := by decide

/-! ## Canonical codes (`F-code-fits`, `F-code-complete`, `F-fixed-lengths`) -/

/-- The example of RFC 1951, 3.2.2: lengths (3,3,3,3,3,2,4,4) for A..H give
F=00, A=010, B=011, C=100, D=101, E=110, G=1110, H=1111. -/
example : (List.range 8).map (codeOf [3, 3, 3, 3, 3, 2, 4, 4]) =
    [[false, true, false], [false, true, true], [true, false, false], [true, false, true],
     [true, true, false], [false, false], [true, true, true, false], [true, true, true, true]] := by
  decide
example : Fits [3, 3, 3, 3, 3, 2, 4, 4] ∧ Complete [3, 3, 3, 3, 3, 2, 4, 4] := by decide
/-- The fixed codes (RFC 1951, 3.2.6): symbol 0 is 00110000, 143 is 10111111, 144 is
110010000, 256 is 0000000 (7 bits), 280 is 11000000; distance 3 is 00011. -/
example : codeOf fixedLitLens 0 = natToBitsMSB 8 0x30 := by decide
example : codeOf fixedLitLens 143 = natToBitsMSB 8 0xBF := by decide
example : codeOf fixedLitLens 144 = natToBitsMSB 9 0x190 := by decide
example : codeOf fixedLitLens 256 = natToBitsMSB 7 0 := by decide
example : codeOf fixedLitLens 280 = natToBitsMSB 8 0xC0 := by decide
example : codeOf fixedDistLens 3 = natToBitsMSB 5 3 := by decide
example : Acceptable .litLen fixedLitLens ∧ Complete fixedLitLens := by decide
example : Acceptable .dist fixedDistLens ∧ Complete fixedDistLens := by decide
example : fixedLitLens.length = 288 ∧ fixedDistLens.length = 32 := by decide
/-- Negative (`F-fixed-lengths`): the fixed literal code is not the all-8 code. -/
example : codeOf fixedLitLens 256 ≠ natToBitsMSB 8 0 := by decide
/-- Negative (`F-code-fits`): an over-subscribed set (three codes of length 1). -/
example : ¬ Fits [1, 1, 1] := by decide
example : ¬ Acceptable .litLen [1, 1, 1] := by decide
/-- Negative (`F-code-fits`): over-subscribed at a longer length (1/2 + 1/4 + 1/4 + 1/8 > 1). -/
example : ¬ Acceptable .dist [1, 2, 2, 3] := by decide
/-- Negative (`F-code-complete`): an incomplete set with two symbols is rejected. -/
example : ¬ Acceptable .litLen [2, 2] := by decide
example : ¬ Acceptable .dist [2, 2, 0, 0] := by decide
/-- Negative: a length above 15 is rejected. -/
example : ¬ Acceptable .litLen [16, 16] := by decide
/-- The single-symbol exception (format.md 2.4): one symbol of length 1 is accepted for the
literal/length and distance codes, but not for the code-length code. -/
example : Acceptable .dist [0, 1] ∧ Acceptable .litLen [1] := by decide
example : ¬ Acceptable .codeLength [0, 1] := by decide
/-- Negative: a single symbol of length 2 is not the exception. -/
example : ¬ Acceptable .dist [0, 2] := by decide
/-- No symbol at all is accepted (format.md 2.4); every decode attempt then fails. -/
example : Acceptable .dist [0, 0, 0] := by decide
example : decodeSym [0, 0, 0] [true, false] = none := by decide
/-- Decoding by prefix: with lengths (1,2,2), "1" then "0 1" then "0 0". -/
example : decodeSym [1, 2, 2] [true, false, true] = some (1, [true]) := by decide
example : decodeSym [1, 2, 2] [false, false] = some (0, [false]) := by decide
/-- Negative: with one symbol of length 1 (code "0"), the bit "1" is not a code. -/
example : decodeSym [0, 1] [true] = none := by decide
/-- `F-dynamic-eob`: symbol 256 must have a length. -/
example : HasEndOfBlock (List.replicate 256 0 ++ [1]) := by decide
example : ¬ HasEndOfBlock (List.replicate 256 0) := by decide
example : ¬ HasEndOfBlock (List.replicate 256 0 ++ [0, 1]) := by decide
/-- `F-dynamic-limits`: at most 286 literal/length and 30 distance codes. -/
example : DynamicCountsOK 29 29 := by decide
example : ¬ DynamicCountsOK 30 0 := by decide
example : ¬ DynamicCountsOK 0 30 := by decide

/-! ## Tables (`F-length-table`, `F-distance-table`) -/

example : lengthBases.length = 29 ∧ lengthExtras.length = 29 := by decide
example : distBases.length = 30 ∧ distExtras.length = 30 := by decide
/-- Each distance row starts where the previous one ends, and the last one ends at 32768. -/
example : (List.range 29).all (fun i => distBases.getD i 0 + 2 ^ distExtras.getD i 0 == distBases.getD (i + 1) 0)
    = true := by decide
example : distBases.getD 29 0 + 2 ^ distExtras.getD 29 0 - 1 = 32768 := by decide
/-- The same for lengths 3..257 (symbols 257..284). Symbol 285 is the single length 258. -/
example : (List.range 27).all (fun i => lengthBases.getD i 0 + 2 ^ lengthExtras.getD i 0 == lengthBases.getD (i + 1) 0)
    = true := by decide
example : lengthBases.getD 28 0 = 258 ∧ lengthExtras.getD 28 0 = 0 := by decide
/-- Negative: distance 5 is not in the first row, it is symbol 4 with 0 extra bits. -/
example : distBases.getD 4 0 = 5 ∧ distExtras.getD 4 0 = 1 := by decide

/-! ## Copying (`F-match-copy`) -/

/-- Distance 1 repeats one byte. -/
example : copyBack [] 1 4 [0x61] = [0x61, 0x61, 0x61, 0x61, 0x61] := by decide
/-- Overlap: distance 2, length 5 over "ab" gives "abababa". -/
example : copyBack [] 2 5 [0x61, 0x62] = [0x61, 0x62, 0x61, 0x62, 0x61, 0x62, 0x61] := by decide
/-- The dictionary is before the output. -/
example : copyBack [0x61, 0x62] 2 3 [] = [0x61, 0x62, 0x61] := by decide

/-! ## Deflate: stored blocks (`F-stored-complement`, `F-block-type-3`) -/

/-- A final stored block "abc": header byte 0x01, LEN = 3, NLEN = 0xFFFC. -/
example : Deflate.Decodes [] [0x01, 0x03, 0x00, 0xFC, 0xFF, 0x61, 0x62, 0x63] [0x61, 0x62, 0x63] :=
  ⟨_, .last rfl rfl (.stored rfl rfl rfl rfl), dk⟩
/-- An empty stored block. -/
example : Deflate.Decodes [] [0x01, 0x00, 0x00, 0xFF, 0xFF] [] :=
  ⟨_, .last rfl rfl (.stored rfl rfl rfl rfl), dk⟩
/-- The padding bits after the 3 header bits are skipped, whatever they are (here 1s). -/
example : Deflate.Decodes [] [0xF9, 0x01, 0x00, 0xFE, 0xFF, 0x61] [0x61] :=
  ⟨_, .last rfl rfl (.stored rfl rfl rfl rfl), dk⟩
/-- Negative (`F-stored-complement`): `NLEN` is not the complement of `LEN`. -/
example : ∀ out, ¬ Deflate.Decodes [] [0x01, 0x03, 0x00, 0xFC, 0xFE, 0x61, 0x62, 0x63] out := by
  rintro out ⟨rest, hb, -⟩
  cases hb with
  | more h1 => ev h1; exact absurd h1.1 (by decide)
  | last h1 h2 hbody =>
    ev h1; obtain ⟨-, rfl⟩ := h1
    ev h2; obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | stored a b c d =>
      ev a; obtain ⟨rfl, rfl⟩ := a
      ev b; obtain ⟨rfl, rfl⟩ := b
      exact absurd c (by decide)
/-- Negative (`F-block-type-3`): `BTYPE = 3` has no meaning. -/
example : ∀ out, ¬ Deflate.Decodes [] [0x07, 0x00, 0x00] out := by
  rintro out ⟨rest, hb, -⟩
  cases hb with
  | more h1 => ev h1; exact absurd h1.1 (by decide)
  | last h1 h2 hbody =>
    ev h1; obtain ⟨-, rfl⟩ := h1
    ev h2; obtain ⟨rfl, rfl⟩ := h2
    cases hbody

/-! ## Deflate: fixed Huffman blocks (`F-fixed-lengths`, `F-match-copy`, `F-distance-bound`) -/

/-- The stream of "a" (zlib raw deflate, fixed block): header 1,1,0; literal 0x61; end of block. -/
example : Deflate.Decodes [] [0x4b, 0x04, 0x00] [0x61] :=
  ⟨_, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩
/-- "aaaaaaaaaa": literals "aa", then a match of length 8 at distance 1 (it overlaps itself). -/
example : Deflate.Decodes [] [0x4b, 0x4c, 0x84, 0x01, 0x00] (List.replicate 10 0x61) :=
  ⟨_, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.lit (s := 97) rfl dk
    (.copy (s := 262) (d := 0) (xl := 0) (xd := 0) rfl dk dk rfl rfl dk rfl dk (.eob rfl))))), dk⟩
/-- "abcabcabcabc": literals "abca", then length 8 at distance 3. -/
example : Deflate.Decodes [] [0x4b, 0x4c, 0x4a, 0x4e, 0x84, 0x21, 0x00]
    [0x61, 0x62, 0x63, 0x61, 0x62, 0x63, 0x61, 0x62, 0x63, 0x61, 0x62, 0x63] :=
  ⟨_, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.lit (s := 98) rfl dk (.lit (s := 99) rfl dk
    (.lit (s := 97) rfl dk
    (.copy (s := 262) (d := 2) (xl := 0) (xd := 0) rfl dk dk rfl rfl dk rfl dk (.eob rfl))))))), dk⟩
/-- Two blocks: a stored block that is not final ("ab"), then a final fixed block that copies
from the first (length 3, distance 2). Back-references reach across blocks. -/
example : Deflate.Decodes [] [0x00, 0x02, 0x00, 0xFD, 0xFF, 0x61, 0x62, 0x03, 0x42, 0x00]
    [0x61, 0x62, 0x61, 0x62, 0x61] :=
  ⟨_, .more rfl rfl (.stored rfl rfl rfl rfl) (.last rfl rfl (.fixed
    (.copy (s := 257) (d := 1) (xl := 0) (xd := 0) rfl dk dk rfl rfl dk rfl dk (.eob rfl)))), dk⟩
/-- With a preset dictionary "ab", a block that begins with a match is valid. -/
example : Deflate.Decodes [0x61, 0x62] [0x03, 0x42, 0x00] [0x61, 0x62, 0x61] :=
  ⟨_, .last rfl rfl (.fixed
    (.copy (s := 257) (d := 1) (xl := 0) (xd := 0) rfl dk dk rfl rfl dk rfl dk (.eob rfl))), dk⟩
/-- Bytes after the deflate data are the tail: `Prefix` splits them off. -/
example : Deflate.Prefix [] [0x4b, 0x04, 0x00, 0xAA, 0xBB] [0xAA, 0xBB] [0x61] :=
  ⟨_, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩

/-- Negative (`F-distance-bound`): the match has distance 2 but only 1 byte was produced. -/
example : ∀ out, ¬ Deflate.Decodes [] [0x4b, 0x04, 0x42, 0x00] out := by
  rintro out ⟨rest, hb, -⟩
  cases hb with
  | more h1 => ev h1; exact absurd h1.1 (by decide)
  | last h1 h2 hbody =>
    ev h1; obtain ⟨-, rfl⟩ := h1
    ev h2; obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | fixed hs =>
      cases hs with
      | eob h => ev h; exact absurd h.1 (by decide)
      | copy h h2 => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd h2 (by decide)
      | lit h _ hs =>
        ev h; obtain ⟨rfl, rfl⟩ := h
        cases hs with
        | eob h => ev h; exact absurd h.1 (by decide)
        | lit h hlt => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd hlt (by decide)
        | copy h _ _ hl hd _ hx hdist =>
          ev h; obtain ⟨rfl, rfl⟩ := h
          ev hl; obtain ⟨rfl, rfl⟩ := hl
          ev hd; obtain ⟨rfl, rfl⟩ := hd
          ev hx; obtain ⟨rfl, rfl⟩ := hx
          exact absurd hdist (by decide)
/-- The same stream is valid with a preset dictionary of one byte (distance 2 then reaches it):
the distance bound counts the dictionary. -/
example : Deflate.Decodes [0x62] [0x4b, 0x04, 0x42, 0x00] [0x61, 0x62, 0x61, 0x62] :=
  ⟨_, .last rfl rfl (.fixed (.lit (s := 97) rfl dk
    (.copy (s := 257) (d := 1) (xl := 0) (xd := 0) rfl dk dk rfl rfl dk rfl dk (.eob rfl)))), dk⟩


/-- Negative (`F-fixed-lengths`): in a fixed block, distance symbol 30 is invalid. -/
example : ∀ out, ¬ Deflate.Decodes [] [0x4b, 0x04, 0x3e, 0x00] out := by
  rintro out ⟨rest, hb, -⟩
  cases hb with
  | more h1 => ev h1; exact absurd h1.1 (by decide)
  | last h1 h2 hbody =>
    ev h1; obtain ⟨-, rfl⟩ := h1
    ev h2; obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | fixed hs =>
      cases hs with
      | eob h => ev h; exact absurd h.1 (by decide)
      | copy h h2 => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd h2 (by decide)
      | lit h _ hs =>
        ev h; obtain ⟨rfl, rfl⟩ := h
        cases hs with
        | eob h => ev h; exact absurd h.1 (by decide)
        | lit h hlt => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd hlt (by decide)
        | copy h _ _ hl hd hd29 =>
          ev h; obtain ⟨rfl, rfl⟩ := h
          ev hl; obtain ⟨rfl, rfl⟩ := hl
          ev hd; obtain ⟨rfl, rfl⟩ := hd
          exact absurd hd29 (by decide)
/-- Negative (`F-fixed-lengths`): in a fixed block, literal/length symbol 286 is invalid. -/
example : ∀ out, ¬ Deflate.Decodes [] [0x4b, 0x1c, 0x03, 0x00] out := by
  rintro out ⟨rest, hb, -⟩
  cases hb with
  | more h1 => ev h1; exact absurd h1.1 (by decide)
  | last h1 h2 hbody =>
    ev h1; obtain ⟨-, rfl⟩ := h1
    ev h2; obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | fixed hs =>
      cases hs with
      | eob h => ev h; exact absurd h.1 (by decide)
      | copy h h2 => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd h2 (by decide)
      | lit h _ hs =>
        ev h; obtain ⟨rfl, rfl⟩ := h
        cases hs with
        | eob h => ev h; exact absurd h.1 (by decide)
        | lit h hlt => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd hlt (by decide)
        | copy h _ h285 => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd h285 (by decide)

/-! ## Deflate: dynamic blocks (`F-dynamic-limits`, `F-dynamic-repeat`, `F-dynamic-eob`, `F-dynamic-valid`) -/

/-- A dynamic block written by hand (and accepted by zlib): `HLIT = 2`, `HDIST = 1`, `HCLEN = 14`;
a code-length code with the four symbols 0, 1, 2, 18 (all of length 2); literal/length lengths
`a`:2, `b`:2, 256:2, 258:2; distance lengths `[0, 1]`, so the distance code has one symbol of
length 1 (the single-symbol exception). The data is "a", "b", a match of length 4 at distance 2,
and the end of block: "ababab". -/
example : Deflate.Decodes []
    [21, 193, 1, 9, 0, 0, 0, 128, 160, 173, 245, 127, 68, 132, 184, 0]
    [0x61, 0x62, 0x61, 0x62, 0x61, 0x62] :=
  ⟨_, .last rfl rfl (.dynamic rfl rfl rfl dk rfl dk
    (.rep18 dk rfl rfl dk (.len dk rfl dk (.len dk rfl dk (.rep18 dk rfl rfl dk (.rep18 dk rfl rfl dk
      (.len dk rfl dk (.len dk rfl dk (.len dk rfl dk (.len dk rfl dk (.len dk rfl dk
        (.done dk))))))))))) dk dk dk
    (.lit (s := 97) rfl dk (.lit (s := 98) rfl dk
      (.copy (s := 258) (d := 1) (xl := 0) (xd := 0) rfl dk dk rfl rfl dk rfl dk (.eob rfl))))), dk⟩
/-- Negative (`F-dynamic-limits`): `HLIT = 30`, that is 287 literal/length codes. -/
example : ∀ out, ¬ Deflate.Decodes [] [0xF5, 0x00, 0x00, 0x00] out := by
  rintro out ⟨rest, hb, -⟩
  cases hb with
  | more h1 => ev h1; exact absurd h1.1 (by decide)
  | last h1 h2 hbody =>
    ev h1; obtain ⟨-, rfl⟩ := h1
    ev h2; obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | dynamic a b _ hcnt =>
      ev a; obtain ⟨rfl, rfl⟩ := a
      ev b; obtain ⟨rfl, rfl⟩ := b
      exact absurd hcnt (by decide)
/-- Negative (`F-dynamic-repeat`): the first code length is symbol 16 (repeat the previous
length), but there is no previous length. The code-length code is 16 and 1 with length 1. -/
example : ∀ out, ¬ Deflate.Decodes [] [5, 192, 3, 0, 0, 0, 0, 0, 144, 0, 0] out := by
  rintro out ⟨rest, hb, -⟩
  cases hb with
  | more h1 => ev h1; exact absurd h1.1 (by decide)
  | last h1 h2 hbody =>
    ev h1; obtain ⟨-, rfl⟩ := h1
    ev h2; obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | dynamic a b c hcnt e _ g =>
      ev a; obtain ⟨rfl, rfl⟩ := a
      ev b; obtain ⟨rfl, rfl⟩ := b
      ev c; obtain ⟨rfl, rfl⟩ := c
      ev e; obtain ⟨rfl, rfl⟩ := e
      cases g with
      | done h => exact absurd h (by decide)
      | len _ h hs => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd hs (by decide)
      | rep16 _ _ hne => exact absurd rfl hne
      | rep17 _ h => ev h; exact absurd h.1 (by decide)
      | rep18 _ h => ev h; exact absurd h.1 (by decide)

/-! ## Helper lemmas for the negative examples of the wrappers -/

theorem bytesToBits_length (t : List UInt8) : (bytesToBits t).length = 8 * t.length := by
  induction t with
  | nil => rfl
  | cons b t ih => simp [bytesToBits, byteBits] at *; omega

theorem drop_pad (X B : List Bool) (n k : Nat) (hX : X.length = n + k) (hk : k < 8)
    (hB : B.length % 8 = 0) :
    List.drop (n + (List.drop n (X ++ B)).length % 8) (X ++ B) = B := by
  have h : (List.drop n (X ++ B)).length % 8 = k := by simp [List.length_drop, hX]; omega
  rw [h, ← hX]
  exact List.drop_left

set_option maxHeartbeats 2000000 in
/-- Inversion of the stream of "a" (`4B 04 00`) followed by any bytes `t`: the output is "a" and
the bytes left after the data are `t`. -/
theorem a_stream_inv {t : List UInt8} {rest : List Bool} {out : List UInt8}
    (hb : Blocks [] [] (bytesToBits (0x4b :: 0x04 :: 0x00 :: t)) rest out) :
    out = [0x61] ∧ rest.drop (rest.length % 8) = bytesToBits t := by
  have e : bytesToBits (0x4b :: 0x04 :: 0x00 :: t) =
      [true,true,false,true,false,false,true,false, false,false,true,false,false,false,false,false,
       false,false,false,false,false,false,false,false] ++ bytesToBits t := by
    show byteBits 0x4b ++ (byteBits 0x04 ++ (byteBits 0x00 ++ bytesToBits t)) = _
    rw [show byteBits 0x4b = [true,true,false,true,false,false,true,false] from by decide,
        show byteBits 0x04 = [false,false,true,false,false,false,false,false] from by decide,
        show byteBits 0x00 = [false,false,false,false,false,false,false,false] from by decide]
    rfl
  rw [e] at hb
  cases hb with
  | more h1 => ev h1; exact absurd h1.1 (by decide)
  | last h1 h2 hbody =>
    ev h1; obtain ⟨-, rfl⟩ := h1
    ev h2; obtain ⟨rfl, rfl⟩ := h2
    cases hbody with
    | fixed hs =>
      cases hs with
      | eob h => ev h; exact absurd h.1 (by decide)
      | copy h h2 => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd h2 (by decide)
      | lit h _ hs =>
        ev h; obtain ⟨rfl, rfl⟩ := h
        cases hs with
        | eob h =>
          ev h; obtain ⟨-, rfl⟩ := h
          refine ⟨rfl, ?_⟩
          have h97 : fixedLitLens.getD 97 0 = 8 := by decide
          have h256 : fixedLitLens.getD 256 0 = 7 := by decide
          rw [h97, h256]
          simp only [List.drop_drop, List.append_eq]
          exact drop_pad _ _ 15 6 (by simp) (by decide) (by rw [bytesToBits_length]; omega)
        | lit h hlt => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd hlt (by decide)
        | copy h h2 => ev h; obtain ⟨rfl, rfl⟩ := h; exact absurd h2 (by decide)

/-! ## The zlib wrapper (`F-zlib-header`, `F-zlib-check`) -/

/-- zlib's own stream for "a": header 78 9C, the fixed block, Adler-32 `00 62 00 62`. -/
example : Zlib.Decodes [] [0x78, 0x9C, 0x4b, 0x04, 0x00, 0x00, 0x62, 0x00, 0x62] [0x61] :=
  ⟨0x78, 0x9C, [], _, rfl, dk, fun _ => ⟨rfl, _, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩,
    fun h => absurd h dk⟩
example : Zlib.Valid [0x61] [0x78, 0x9C, 0x4b, 0x04, 0x00, 0x00, 0x62, 0x00, 0x62] :=
  ⟨0x78, 0x9C, [], _, rfl, dk, fun _ => ⟨rfl, _, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩,
    fun h => absurd h dk⟩
/-- With `FDICT`: header 78 20, `DICTID` = Adler-32 of "ab" = 01 26 00 C4, a block that is only a
match of length 3 at distance 2 (it needs the dictionary), Adler-32 of "aba" = 02 4B 01 25. -/
example : Zlib.Decodes [0x61, 0x62]
    [0x78, 0x20, 0x01, 0x26, 0x00, 0xC4, 0x03, 0x42, 0x00, 0x02, 0x4B, 0x01, 0x25] [0x61, 0x62, 0x61] :=
  ⟨0x78, 0x20, [0x01, 0x26, 0x00, 0xC4], _, rfl, dk, fun h => absurd h dk,
    fun _ => ⟨dk, _, .last rfl rfl (.fixed
      (.copy (s := 257) (d := 1) (xl := 0) (xd := 0) rfl dk dk rfl rfl dk rfl dk (.eob rfl))), dk⟩⟩
/-- Negative: the same stream with no dictionary (zlib returns `Z_NEED_DICT`; here the dictionary id
does not match the Adler-32 of the empty dictionary). -/
example : ∀ out, ¬ Zlib.Decodes []
    [0x78, 0x20, 0x01, 0x26, 0x00, 0xC4, 0x03, 0x42, 0x00, 0x02, 0x4B, 0x01, 0x25] out := by
  rintro out ⟨cmf, flg, pre, s, hs, hh, h0, h1⟩
  simp only [List.cons.injEq] at hs
  obtain ⟨rfl, rfl, hs⟩ := hs
  obtain ⟨rfl, -⟩ := h1 (by decide)
  rw [show be32 (adler32 []).toNat = [0, 0, 0, 1] from by decide] at hs
  simp at hs
/-- Negative: the same stream with the wrong dictionary "ac". -/
example : ∀ out, ¬ Zlib.Decodes [0x61, 0x63]
    [0x78, 0x20, 0x01, 0x26, 0x00, 0xC4, 0x03, 0x42, 0x00, 0x02, 0x4B, 0x01, 0x25] out := by
  rintro out ⟨cmf, flg, pre, s, hs, hh, h0, h1⟩
  simp only [List.cons.injEq] at hs
  obtain ⟨rfl, rfl, hs⟩ := hs
  obtain ⟨rfl, -⟩ := h1 (by decide)
  rw [show be32 (adler32 [0x61, 0x63]).toNat = [1, 0x27, 0, 0xC5] from by decide] at hs
  simp at hs
/-- Negative (`F-zlib-header`): the header check fails, 0x789D is not a multiple of 31. -/
example : ∀ out, ¬ Zlib.Decodes [] [0x78, 0x9D, 0x4b, 0x04, 0x00, 0x00, 0x62, 0x00, 0x62] out := by
  rintro out ⟨cmf, flg, pre, s, hs, hh, -⟩
  simp only [List.cons.injEq] at hs
  obtain ⟨rfl, rfl, -⟩ := hs
  exact absurd hh (by decide)
/-- Negative (`F-zlib-header`): compression method 9 (the check bits are right). -/
example : ∀ out, ¬ Zlib.Decodes [] [0x79, 0x18, 0x4b, 0x04, 0x00, 0x00, 0x62, 0x00, 0x62] out := by
  rintro out ⟨cmf, flg, pre, s, hs, hh, -⟩
  simp only [List.cons.injEq] at hs
  obtain ⟨rfl, rfl, -⟩ := hs
  exact absurd hh (by decide)
/-- Negative (`F-zlib-header`): window size field `CINFO = 8` (the check bits are right). -/
example : ∀ out, ¬ Zlib.Decodes [] [0x88, 0x1C, 0x4b, 0x04, 0x00, 0x00, 0x62, 0x00, 0x62] out := by
  rintro out ⟨cmf, flg, pre, s, hs, hh, -⟩
  simp only [List.cons.injEq] at hs
  obtain ⟨rfl, rfl, -⟩ := hs
  exact absurd hh (by decide)
/-- Negative (`F-zlib-check`): the Adler-32 is wrong (last byte 0x63 instead of 0x62). -/
example : ∀ out, ¬ Zlib.Decodes [] [0x78, 0x9C, 0x4b, 0x04, 0x00, 0x00, 0x62, 0x00, 0x63] out := by
  rintro out ⟨cmf, flg, pre, s, hs, hh, h0, h1⟩
  simp only [List.cons.injEq] at hs
  obtain ⟨rfl, rfl, hs⟩ := hs
  obtain ⟨rfl, ⟨rest, hb, ht⟩⟩ := h0 (by decide)
  simp only [List.nil_append] at hs
  subst hs
  obtain ⟨rfl, hr⟩ := a_stream_inv (t := [0x00, 0x62, 0x00, 0x63]) hb
  rw [hr] at ht
  exact absurd ht (by decide)
/-- Negative: a stream that is too short (no trailer). -/
example : ∀ out, ¬ Zlib.Decodes [] [0x78, 0x9C, 0x4b, 0x04, 0x00] out := by
  rintro out ⟨cmf, flg, pre, s, hs, hh, h0, h1⟩
  simp only [List.cons.injEq] at hs
  obtain ⟨rfl, rfl, hs⟩ := hs
  obtain ⟨rfl, ⟨rest, hb, ht⟩⟩ := h0 (by decide)
  simp only [List.nil_append] at hs
  subst hs
  obtain ⟨rfl, hr⟩ := a_stream_inv (t := []) hb
  rw [hr] at ht
  exact absurd ht (by decide)

/-! ## The gzip wrapper (format.md section 4, `F-gzip-check`) -/

/-- zlib's own gzip stream for "a" (no optional fields): header 1F 8B 08 00 + MTIME 0 + XFL 2 + OS 19,
the fixed block, CRC-32 `E8B7BE43` and length 1, both little endian. -/
example : Gzip.Decodes
    [31, 139, 8, 0, 0, 0, 0, 0, 2, 19, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0] [0x61] :=
  ⟨0, [0, 0, 0, 0], 2, 19, [], [], [], [75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0], dk, dk, dk, dk, dk, dk,
    _, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩
/-- A header with `FHCRC` and `FNAME` (flags 10): name "a.txt", MTIME 01 02 03 04, then the
16-bit header CRC D3 C6 (the low 16 bits of the CRC-32 of the 16 header bytes before it). -/
example : Gzip.Decodes
    [31, 139, 8, 10, 1, 2, 3, 4, 0, 3, 97, 46, 116, 120, 116, 0, 211, 198,
     75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0] [0x61] :=
  ⟨10, [1, 2, 3, 4], 0, 3, [], [97, 46, 116, 120, 116], [], [75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0], dk, dk, dk, dk, dk, dk,
    _, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩
/-- `FEXTRA` (flags 4): `XLEN = 2` and two extra bytes. -/
example : Gzip.Decodes
    [31, 139, 8, 4, 0, 0, 0, 0, 0, 3, 2, 0, 7, 7, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0] [0x61] :=
  ⟨4, [0, 0, 0, 0], 0, 3, [7, 7], [], [], [75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0], dk, dk, dk, dk, dk, dk,
    _, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩
/-- Negative: the wrong magic number (ID2 = 138). -/
example : ∀ out, ¬ Gzip.Decodes
    [31, 138, 8, 0, 0, 0, 0, 0, 2, 19, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0] out := by
  rintro out ⟨flg, mtime, xfl, os, extra, name, comment, s, -, -, -, -, -, hs, -⟩
  simp only [Gzip.header, List.cons_append, List.cons.injEq] at hs
  exact absurd hs.2.1 (by decide)
/-- Negative: the reserved flag bit 5 is set (zlib: `unknown header flags set`). -/
example : ∀ out, ¬ Gzip.Decodes
    [31, 139, 8, 32, 0, 0, 0, 0, 2, 19, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0] out := by
  rintro out ⟨flg, mtime, xfl, os, extra, name, comment, s, hf, -, -, -, -, hs, -⟩
  simp only [Gzip.header, List.cons_append, List.cons.injEq] at hs
  obtain ⟨-, -, -, rfl, -⟩ := hs
  exact absurd hf (by decide)
/-- Negative (`F-gzip-check`): the CRC-32 is wrong (first CRC byte 67 changed to 68). -/
example : ∀ out, ¬ Gzip.Decodes
    [31, 139, 8, 0, 0, 0, 0, 0, 2, 19, 75, 4, 0, 68, 190, 183, 232, 1, 0, 0, 0] out := by
  rintro out ⟨flg, mtime, xfl, os, extra, name, comment, s, hf, hm, he, hn, hc, hs, rest, hb, ht⟩
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, mtime = [a, b, c, d] := by
    match mtime, hm with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  simp [Gzip.header] at hs
  obtain ⟨rfl, -, -, -, -, rfl, rfl, hs⟩ := hs
  simp at hs
  subst hs
  obtain ⟨rfl, hr⟩ := a_stream_inv (t := [68, 190, 183, 232, 1, 0, 0, 0]) hb
  rw [hr] at ht
  exact absurd ht (by decide)

/-- Negative (`F-gzip-check`): the length is wrong (`ISIZE` = 2 for one byte of data). -/
example : ∀ out, ¬ Gzip.Decodes
    [31, 139, 8, 0, 0, 0, 0, 0, 2, 19, 75, 4, 0, 67, 190, 183, 232, 2, 0, 0, 0] out := by
  rintro out ⟨flg, mtime, xfl, os, extra, name, comment, s, hf, hm, he, hn, hc, hs, rest, hb, ht⟩
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, mtime = [a, b, c, d] := by
    match mtime, hm with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  simp [Gzip.header] at hs
  obtain ⟨rfl, -, -, -, -, rfl, rfl, hs⟩ := hs
  simp at hs
  subst hs
  obtain ⟨rfl, hr⟩ := a_stream_inv (t := [67, 190, 183, 232, 2, 0, 0, 0]) hb
  rw [hr] at ht
  exact absurd ht (by decide)

end ZlibF.Spec
