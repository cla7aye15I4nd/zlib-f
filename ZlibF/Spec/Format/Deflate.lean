import ZlibF.Spec.Format.Huffman

/-!
# Format: DEFLATE (RFC 1951) as a declarative relation

`docs/spec/format.md` section 2. The relations say exactly what zlib's `inflate` accepts
(zlib is stricter than the RFC in the places listed in format.md; each is a premise below).

Convention: the history `h` is the output produced so far (without the preset dictionary);
a back-reference may reach into `dict ++ h` (`F-distance-bound`).
Stored blocks need to know the position in the current byte. A relation here is always
applied to the bits of a whole number of bytes (`bytesToBits`), so the number of bits left
in the current byte is `inp.length % 8`; `Deflate.Prefix` is the entry point that guarantees this.
-/

namespace ZlibF.Spec

/-- `F-match-copy`: copy `n` bytes one at a time from `dist` bytes back in `dict ++ h`.
The copy may overlap itself (`n > dist`): bytes copied earlier are read again. -/
def copyBack (dict : List UInt8) (dist : Nat) : Nat → List UInt8 → List UInt8
  | 0, h => h
  | n + 1, h => copyBack dict dist n (h ++ [(dict ++ h).getD ((dict ++ h).length - dist) 0])

/-- The symbols of one Huffman block with the literal/length code `L` and distance code `D`
(RFC 1951, 3.2.3 and 3.2.5; format.md 2.7). `Symbols L D dict h inp rest out`: starting with output
`h` and bits `inp`, the block ends with the end-of-block symbol, leaves the bits `rest`, and
the output is `out`. -/
inductive Symbols (L D : List Nat) (dict : List UInt8) :
    List UInt8 → List Bool → List Bool → List UInt8 → Prop
  /-- Symbol 256: end of block. -/
  | eob {h : List UInt8} {inp r : List Bool} :
      decodeSym L inp = some (256, r) → Symbols L D dict h inp r h
  /-- Symbols 0..255: output that byte. -/
  | lit {h : List UInt8} {inp r rest : List Bool} {s : Nat} {out : List UInt8} :
      decodeSym L inp = some (s, r) → s < 256 →
      Symbols L D dict (h ++ [s.toUInt8]) r rest out → Symbols L D dict h inp rest out
  /-- Symbols 257..285: length code, its extra bits, distance code, its extra bits (in this
  order, `F-length-table`, `F-distance-table`), then a copy of `len` bytes from `dist` back.
  Distance symbols 30 and 31 (possible in the fixed code) are invalid; `dist` may not exceed
  the output so far plus the dictionary (`F-distance-bound`). -/
  | copy {h : List UInt8} {inp r1 r2 r3 r4 rest : List Bool} {s d xl xd : Nat} {out : List UInt8} :
      decodeSym L inp = some (s, r1) → 257 ≤ s → s ≤ 285 →
      readBits (lengthExtras.getD (s - 257) 0) r1 = some (xl, r2) →
      decodeSym D r2 = some (d, r3) → d ≤ 29 →
      readBits (distExtras.getD d 0) r3 = some (xd, r4) →
      xd + distBases.getD d 0 ≤ (dict ++ h).length →
      Symbols L D dict
        (copyBack dict (distBases.getD d 0 + xd) (lengthBases.getD (s - 257) 0 + xl) h) r4 rest out →
      Symbols L D dict h inp rest out

/-- The code lengths of a dynamic block, read with the code-length code `cl`
(RFC 1951, 3.2.7; `F-dynamic-repeat`). `CodeLens cl total acc inp rest lens`: `acc` lengths are
already read, reading continues until there are exactly `total`, and `lens` is the result.
A repeat may not run past `total` and symbol 16 needs a previous length. -/
inductive CodeLens (cl : List Nat) (total : Nat) :
    List Nat → List Bool → List Bool → List Nat → Prop
  /-- All `total` lengths are read. -/
  | done {acc : List Nat} {inp : List Bool} : acc.length = total → CodeLens cl total acc inp inp acc
  /-- Symbols 0..15: that length. -/
  | len {acc : List Nat} {inp r rest : List Bool} {s : Nat} {out : List Nat} :
      acc.length < total → decodeSym cl inp = some (s, r) → s < 16 →
      CodeLens cl total (acc ++ [s]) r rest out → CodeLens cl total acc inp rest out
  /-- Symbol 16: repeat the previous length 3 to 6 times (2 extra bits). -/
  | rep16 {acc : List Nat} {inp r1 r2 rest : List Bool} {x : Nat} {out : List Nat} :
      acc.length < total → decodeSym cl inp = some (16, r1) → acc ≠ [] →
      readBits 2 r1 = some (x, r2) → acc.length + (3 + x) ≤ total →
      CodeLens cl total (acc ++ List.replicate (3 + x) (acc.getLastD 0)) r2 rest out →
      CodeLens cl total acc inp rest out
  /-- Symbol 17: repeat length 0, 3 to 10 times (3 extra bits). -/
  | rep17 {acc : List Nat} {inp r1 r2 rest : List Bool} {x : Nat} {out : List Nat} :
      acc.length < total → decodeSym cl inp = some (17, r1) →
      readBits 3 r1 = some (x, r2) → acc.length + (3 + x) ≤ total →
      CodeLens cl total (acc ++ List.replicate (3 + x) 0) r2 rest out →
      CodeLens cl total acc inp rest out
  /-- Symbol 18: repeat length 0, 11 to 138 times (7 extra bits). -/
  | rep18 {acc : List Nat} {inp r1 r2 rest : List Bool} {x : Nat} {out : List Nat} :
      acc.length < total → decodeSym cl inp = some (18, r1) →
      readBits 7 r1 = some (x, r2) → acc.length + (11 + x) ≤ total →
      CodeLens cl total (acc ++ List.replicate (11 + x) 0) r2 rest out →
      CodeLens cl total acc inp rest out

/-- The order in which the lengths of the code-length alphabet are stored (RFC 1951, 3.2.7). -/
def clOrder : List Nat := [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Read the `n` three-bit code-length-code lengths (`HCLEN + 4` of them, in `clOrder`) and
return the lengths of the 19 symbols in symbol order; those not stored are 0. -/
def readCodeLenLens (n : Nat) (inp : List Bool) : Option (List Nat × List Bool) :=
  match readNats 3 n inp with
  | none => none
  | some (vs, r) =>
    some ((List.range 19).map fun sym =>
      if clOrder.idxOf sym < n then vs.getD (clOrder.idxOf sym) 0 else 0, r)

/-- `F-dynamic-limits`: zlib rejects `HLIT + 257 > 286` and `HDIST + 1 > 30`
(`too many length or distance symbols`). Here `hlit` and `hdist` are the raw 5-bit fields. -/
abbrev DynamicCountsOK (hlit hdist : Nat) : Prop :=
  hlit + 257 ≤ 286 ∧ hdist + 1 ≤ 30

/-- `F-dynamic-eob`: the length of symbol 256 must not be 0
(`invalid code -- missing end-of-block`). -/
abbrev HasEndOfBlock (litLens : List Nat) : Prop :=
  litLens.getD 256 0 ≠ 0

/-- The body of a block of type `bt` (RFC 1951, 3.2.4 to 3.2.7), after the three header bits.
`Body dict bt h inp rest out`. There is no constructor for `bt = 3` (`F-block-type-3`). -/
inductive Body (dict : List UInt8) :
    Nat → List UInt8 → List Bool → List Bool → List UInt8 → Prop
  /-- `BTYPE = 0` (`F-stored-complement`): skip to the byte boundary, `LEN` and `NLEN` (16 bits
  each, least significant bit first), `NLEN` is the complement of `LEN`, then `LEN` bytes. -/
  | stored {h : List UInt8} {inp r1 r2 r3 : List Bool} {len nlen : Nat} {bs : List UInt8} :
      readBits 16 (inp.drop (inp.length % 8)) = some (len, r1) →
      readBits 16 r1 = some (nlen, r2) → nlen = 65535 - len →
      readBytes len r2 = some (bs, r3) →
      Body dict 0 h inp r3 (h ++ bs)
  /-- `BTYPE = 1` (`F-fixed-lengths`): the fixed codes. -/
  | fixed {h : List UInt8} {inp rest : List Bool} {out : List UInt8} :
      Symbols fixedLitLens fixedDistLens dict h inp rest out → Body dict 1 h inp rest out
  /-- `BTYPE = 2` (RFC 1951, 3.2.7; format.md 2.6): `HLIT`, `HDIST`, `HCLEN`, the code-length code,
  the literal/length and distance lengths, then the symbols. `F-dynamic-limits`,
  `F-dynamic-repeat` (in `CodeLens`), `F-dynamic-eob`, `F-dynamic-valid`. -/
  | dynamic {h : List UInt8} {inp r1 r2 r3 r4 r5 rest : List Bool} {hlit hdist hclen : Nat}
      {cl lens : List Nat} {out : List UInt8} :
      readBits 5 inp = some (hlit, r1) → readBits 5 r1 = some (hdist, r2) →
      readBits 4 r2 = some (hclen, r3) → DynamicCountsOK hlit hdist →
      readCodeLenLens (hclen + 4) r3 = some (cl, r4) → Acceptable .codeLength cl →
      CodeLens cl (hlit + 257 + (hdist + 1)) [] r4 r5 lens →
      HasEndOfBlock (lens.take (hlit + 257)) →
      Acceptable .litLen (lens.take (hlit + 257)) → Acceptable .dist (lens.drop (hlit + 257)) →
      Symbols (lens.take (hlit + 257)) (lens.drop (hlit + 257)) dict h r5 rest out →
      Body dict 2 h inp rest out

/-- A sequence of blocks (RFC 1951, 3.2.3; format.md 2.2): the three header bits
`BFINAL` and `BTYPE`, the body, and, unless `BFINAL` was 1, more blocks.
`Blocks dict h inp rest out`: starting with output `h`, the blocks use the bits up to `rest`. -/
inductive Blocks (dict : List UInt8) : List UInt8 → List Bool → List Bool → List UInt8 → Prop
  /-- A block with `BFINAL = 1`. -/
  | last {h : List UInt8} {inp r1 r2 rest : List Bool} {bt : Nat} {out : List UInt8} :
      readBits 1 inp = some (1, r1) → readBits 2 r1 = some (bt, r2) →
      Body dict bt h r2 rest out → Blocks dict h inp rest out
  /-- A block with `BFINAL = 0`, followed by more blocks. -/
  | more {h h' : List UInt8} {inp r1 r2 r3 rest : List Bool} {bt : Nat} {out : List UInt8} :
      readBits 1 inp = some (0, r1) → readBits 2 r1 = some (bt, r2) →
      Body dict bt h r2 r3 h' → Blocks dict h' r3 rest out → Blocks dict h inp rest out

/-- A deflate stream that begins `stream`, with the preset dictionary `dict` (empty if none),
is followed by the bytes `tail` and produces `out`: the blocks end at some bit; the rest of
that byte is skipped (padding is ignored, as in zlib); and the bytes after it are exactly `tail`.
This is how the wrappers find their trailer. -/
def Deflate.Prefix (dict stream tail out : List UInt8) : Prop :=
  ∃ rest, Blocks dict [] (bytesToBits stream) rest out ∧
    rest.drop (rest.length % 8) = bytesToBits tail

/-- Raw deflate data (RFC 1951): `stream` is exactly one deflate stream with no bytes
after it, and it decodes to `out`. `dict` is the preset dictionary (`[]` if none). -/
def Deflate.Decodes (dict stream out : List UInt8) : Prop :=
  Deflate.Prefix dict stream [] out

/-- `F-deflate-valid` for raw deflate: `compressed` is a valid compressed stream for
`input`. This is what `deflate` has to produce (without a dictionary). -/
def Deflate.Valid (input compressed : List UInt8) : Prop :=
  Deflate.Decodes [] compressed input

end ZlibF.Spec
