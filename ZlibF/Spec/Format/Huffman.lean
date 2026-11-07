import ZlibF.Spec.Format.Bits

/-!
# Format: canonical Huffman codes

RFC 1951, 3.2.2 and `docs/format/README.md` sections on canonical Huffman codes, dynamic tables and code alphabets.
A code is given by a list of code lengths: `lens[s]` is the length of symbol `s`,
and 0 means the symbol is unused. A symbol beyond the end of the list is unused.
-/

namespace ZlibF.Spec

/-- The longest code length of deflate (RFC 1951, 3.2.7). -/
def maxCodeLen : Nat := 15

/-- `count lens l` is `count[l]` of RFC 1951, 3.2.2: the number of symbols of length `l`. -/
def count (lens : List Nat) (l : Nat) : Nat :=
  (lens.filter (· == l)).length

/-- `codeStart lens l` is `code_start[l]` of `F-code-fits` / RFC 1951, 3.2.2:
`code_start[1] = 0` and `code_start[l] = (code_start[l-1] + count[l-1]) * 2`.
(Length 0 is not a code length, so its count is taken as 0.) -/
def codeStart (lens : List Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => (codeStart lens l + (if l = 0 then 0 else count lens l)) * 2

/-- The canonical code of symbol `s` (`F-code-fits`, RFC 1951, 3.2.2): the symbols of
length `l`, in increasing symbol order, get the consecutive values
`code_start[l]`, `code_start[l]+1`, ..., written in `l` bits, most significant bit first
(`F-bit-order`). Meaningful only if `lens[s] > 0`. -/
def codeOf (lens : List Nat) (s : Nat) : List Bool :=
  let l := lens.getD s 0
  natToBitsMSB l (codeStart lens l + ((lens.take s).filter (· == l)).length)

/-- `F-code-fits`: no code overflows its length, `code_start[l] + count[l] <= 2^l` for
`l = 1..15`. This is the Kraft inequality; a set that breaks it is over-subscribed. -/
abbrev Fits (lens : List Nat) : Prop :=
  ∀ l ∈ List.range' 1 maxCodeLen, codeStart lens l + count lens l ≤ 2 ^ l

/-- `F-code-complete`: the Kraft sum is exactly 1, that is, the codes of length 15 and
shorter fill all `2^15` leaves. (Meant together with `Fits`.) -/
abbrev Complete (lens : List Nat) : Prop :=
  codeStart lens maxCodeLen + count lens maxCodeLen = 2 ^ maxCodeLen

/-- The three kinds of code of a dynamic block. The code-length code never gets the
single-symbol exception (`F-code-complete`, table of format.md 2.4). -/
inductive CodeKind where
  | codeLength
  | litLen
  | dist
  deriving DecidableEq

/-- What zlib's `inflate_table` accepts as the lengths of one code (`F-code-fits`,
`F-code-complete`, `F-dynamic-valid`; format.md 2.4): every length is at most 15, the set
is not over-subscribed, and it is complete, or it has no symbol at all, or (not for the
code-length code) its only symbol has length 1. -/
abbrev Acceptable (k : CodeKind) (lens : List Nat) : Prop :=
  (∀ x ∈ lens, x ≤ maxCodeLen) ∧ Fits lens ∧
    (Complete lens ∨ (∀ x ∈ lens, x = 0) ∨ (k ≠ .codeLength ∧ lens.filter (· != 0) = [1]))

/-- `decodeSym lens inp`: the first symbol whose canonical code is a prefix of `inp`,
with the bits after that code. `none` if no code is a prefix (an invalid code).
For an `Acceptable` set at most one code is a prefix, because the code is prefix-free. -/
def decodeSym (lens : List Nat) (inp : List Bool) : Option (Nat × List Bool) :=
  match (List.range lens.length).find?
      (fun s => lens.getD s 0 != 0 && (codeOf lens s).isPrefixOf inp) with
  | some s => some (s, inp.drop (lens.getD s 0))
  | none => none

/-- `F-fixed-lengths` (RFC 1951, 3.2.6): the 288 literal/length code lengths of a fixed block:
8 for 0..143, 9 for 144..255, 7 for 256..279, 8 for 280..287. -/
def fixedLitLens : List Nat :=
  List.replicate 144 8 ++ List.replicate 112 9 ++ List.replicate 24 7 ++ List.replicate 8 8

/-- `F-fixed-lengths`: the 32 distance code lengths of a fixed block, all 5. -/
def fixedDistLens : List Nat := List.replicate 32 5

/-- `F-length-table` (RFC 1951, 3.2.5): first match length of symbols 257..285, indexed by `s - 257`. -/
def lengthBases : List Nat :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
   131, 163, 195, 227, 258]

/-- `F-length-table`: number of extra bits of symbols 257..285, indexed by `s - 257`. -/
def lengthExtras : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

/-- `F-distance-table` (RFC 1951, 3.2.5): first distance of distance symbols 0..29. -/
def distBases : List Nat :=
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
   2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

/-- `F-distance-table`: number of extra bits of distance symbols 0..29. -/
def distExtras : List Nat :=
  [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

end ZlibF.Spec
