import ZlibF.Proof.«inflate.c.invariant»
import ZlibF.Proof.«inflate.c.meaning-stream»
import ZlibF.Spec.Format.Token
import ZlibF.Spec.InflateDecodeTableInvariant
import ZlibF.Spec.InflateDecodeTableStability
import ZlibF.Proof.«inftrees.c.code-length-meaning-state»
import ZlibF.Math.«code-length-prefix»
import ZlibF.Spec.Format.Wrapper
import ZlibF.Spec.Api.Basic
import ZlibF.Spec.Public.Sequences

/-!
# inflate.c: the format meaning of a decoder state (interface)

`ParseMeaning` couples the actual decoder after a data epoch with the stream
format. It has two halves:

* a prefix grammar of the format (`DeflateParsed`, `WrapParsed`): which
  positions a reader of the format can reach after a given prefix of the
  input, independent of zlib;
* a matching relation (`StageMatches`): how the decoder state represents such
  a position (mode, bit buffer, tables, pending token, window, check value,
  counters).

The grammar is closed under exactly the steps of `ZlibF/Spec/Format`, so a
position reached on a prefix of a valid stream can be completed to that
stream's decoding, and a rejected position has no valid completion.

The proof obligations are listed in `docs/progress.md` (Core proof skeletons,
inflate). Each component is separate:

* `TableMeaning`: an installed table decodes the canonical code of its lengths
  (`DecodeTableInvariant.Inv`);
* `PendingMatches`: the partial token held in `length`, `offset`, `extra`;
* `WindowMeaning`: the window holds the last bytes of dictionary and output;
* `CheckMeaning`: `check` and `total` are the checksum and length of the output;
* `ConfigMatches`, `WrapMatches`: the configuration of a protocol trace and
  the stream-side fields of each stage (header position, dictionary
  identifier, flags word and width, trailer bit buffer), with their parts in
  `inflate.c.meaning-stream`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## The prefix grammar of deflate data -/

/-- A token that has started but is not complete, as zlib holds it between
modes. Lengths and distances are the decoded values. -/
inductive Pending where
  /-- Between symbols (`LEN`). -/
  | none
  /-- A length symbol read, its extra bits not yet (`LENEXT`). -/
  | lengthExtra (symbol : Nat)
  /-- A length read, its distance symbol not yet (`DIST`). -/
  | distance (length : Nat)
  /-- A distance symbol read, its extra bits not yet (`DISTEXT`). -/
  | distanceExtra (length distanceSymbol : Nat)
  /-- A copy with `remaining` bytes left at distance `dist` (`MATCH`). -/
  | copy (remaining dist : Nat)
  /-- A literal decoded but not yet written (`LIT`). -/
  | literal (byte : UInt8)
  deriving DecidableEq

/-- Where the parse of deflate data stands. -/
inductive BlockStage where
  /-- Before a block header (`TYPE`, `TYPEDO`). -/
  | boundary
  /-- After the header bits of a stored block, before its length (`STORED`). -/
  | storedHeader
  /-- Inside a stored block with `remaining` bytes left (`COPY_`, `COPY`). -/
  | stored (remaining : Nat)
  /-- Inside a dynamic block header; `header` are its bits so far
  (`TABLE`, `LENLENS`, `CODELENS`). -/
  | dynamicHeader (header : List Bool)
  /-- Inside a Huffman block with literal/length lengths `L` and distance
  lengths `D` (`LEN_`, `LEN`, `LENEXT`, `DIST`, `DISTEXT`, `MATCH`, `LIT`). -/
  | codes (L D : List Nat) (pending : Pending)
  /-- After the final block, before the byte alignment of the trailer
  (`TYPE`, `TYPEDO` with `last = 1`). -/
  | finished

/-- A position of the parse: output so far, whether the current block is
final, and the stage. -/
structure DeflatePos where
  out : List UInt8
  final : Bool
  stage : BlockStage

/-- A small helper: `n` bits of `v`, least significant first. -/
def natToBitsLSB (n v : Nat) : List Bool :=
  (List.range n).map fun i => v / 2 ^ i % 2 = 1

/-- The bits of a started length or distance and the decoded fields zlib
keeps for it (`LENEXT`, `DIST`, `DISTEXT`), and a match read completely but
not yet checked against the history (`MATCH` before its first byte): zlib
leaves `MATCH` for want of output room before it checks the distance, so a
too-far distance can wait there while the call returns `Z_OK`. -/
def PendingParsed (L D : List Nat) (bits : List Bool) : Pending → Prop
  | .none => bits = []
  | .lengthExtra symbol => 257 ≤ symbol ∧ symbol ≤ 285 ∧ decodeSym L bits = some (symbol, [])
  | .distance length => ∃ symbol extra r1,
      decodeSym L bits = some (symbol, r1) ∧ 257 ≤ symbol ∧ symbol ≤ 285 ∧
      readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (extra, []) ∧
      length = lengthBases.getD (symbol - 257) 0 + extra
  | .distanceExtra length distanceSymbol => ∃ symbol extra r1 r2,
      decodeSym L bits = some (symbol, r1) ∧ 257 ≤ symbol ∧ symbol ≤ 285 ∧
      readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (extra, r2) ∧
      length = lengthBases.getD (symbol - 257) 0 + extra ∧
      decodeSym D r2 = some (distanceSymbol, []) ∧ distanceSymbol ≤ 29
  | .copy remaining dist => ∃ symbol extra distanceSymbol distanceExtra r1 r2 r3,
      decodeSym L bits = some (symbol, r1) ∧ 257 ≤ symbol ∧ symbol ≤ 285 ∧
      readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (extra, r2) ∧
      decodeSym D r2 = some (distanceSymbol, r3) ∧ distanceSymbol ≤ 29 ∧
      readBits (distExtras.getD distanceSymbol 0) r3 = some (distanceExtra, []) ∧
      remaining = lengthBases.getD (symbol - 257) 0 + extra ∧
      dist = distBases.getD distanceSymbol 0 + distanceExtra
  | .literal _ => False

/-- A dynamic block header that is complete: the codes it defines, as in
`Body.dynamic`. -/
def DynamicHeader (header : List Bool) (L D : List Nat) : Prop :=
  ∃ (hlit hdist hclen : Nat) (r1 r2 r3 r4 : List Bool) (cl lens : List Nat),
    readBits 5 header = some (hlit, r1) ∧ readBits 5 r1 = some (hdist, r2) ∧
    readBits 4 r2 = some (hclen, r3) ∧ DynamicCountsOK hlit hdist ∧
    readCodeLenLens (hclen + 4) r3 = some (cl, r4) ∧ Acceptable .codeLength cl ∧
    CodeLens cl (hlit + 257 + (hdist + 1)) [] r4 [] lens ∧
    HasEndOfBlock (lens.take (hlit + 257)) ∧
    Acceptable .litLen (lens.take (hlit + 257)) ∧ Acceptable .dist (lens.drop (hlit + 257)) ∧
    L = lens.take (hlit + 257) ∧ D = lens.drop (hlit + 257)

/-- `DeflateParsed dict consumed pos`: reading the deflate bits `consumed`
from the start of the data reaches `pos`. Every complete step is a step of
`Blocks`/`Body`/`Symbols`. A partial token is admitted when its fields are
read. The bits of a dynamic block header are admitted before the header is
complete, also when no completion exists: zlib checks the code-length code,
the end-of-block length and the acceptability of the codes only after a whole
part of the header is read (`tests/goals/inflate-meaning/late-rejection.c`).
`DynamicMatches` pins those bits to the decoder state; `dynamicDone` still
needs a complete `DynamicHeader`. -/
inductive DeflateParsed (dict : List UInt8) : List Bool → DeflatePos → Prop
  | start : DeflateParsed dict [] ⟨[], false, .boundary⟩
  /-- The header bits `BFINAL`, `BTYPE = 0` of a stored block. -/
  | storedStart {consumed : List Bool} {out : List UInt8} {final : Bool} :
      DeflateParsed dict consumed ⟨out, false, .boundary⟩ →
      DeflateParsed dict (consumed ++ [final, false, false]) ⟨out, final, .storedHeader⟩
  /-- The padding to the byte boundary alone: `STORED` drops it (`BYTEBITS`)
  before it waits for `LEN` and `NLEN`. -/
  | storedPad {consumed : List Bool} {out : List UInt8} {final : Bool} {pad : List Bool} :
      DeflateParsed dict consumed ⟨out, final, .storedHeader⟩ →
      pad.length = (8 - consumed.length % 8) % 8 →
      DeflateParsed dict (consumed ++ pad) ⟨out, final, .storedHeader⟩
  /-- The padding to the byte boundary (empty after `storedPad`), `LEN` and `NLEN`. -/
  | storedLength {consumed : List Bool} {out : List UInt8} {final : Bool}
      {pad : List Bool} {len : Nat} :
      DeflateParsed dict consumed ⟨out, final, .storedHeader⟩ →
      pad.length = (8 - consumed.length % 8) % 8 →
      len < 65536 →
      DeflateParsed dict
        (consumed ++ pad ++ natToBitsLSB 16 len ++ natToBitsLSB 16 (65535 - len))
        ⟨out, final, .stored len⟩
  | storedByte {consumed : List Bool} {out : List UInt8} {final : Bool} {remaining : Nat}
      (byte : UInt8) :
      DeflateParsed dict consumed ⟨out, final, .stored (remaining + 1)⟩ →
      DeflateParsed dict (consumed ++ byteBits byte) ⟨out ++ [byte], final, .stored remaining⟩
  | storedEnd {consumed : List Bool} {out : List UInt8} :
      DeflateParsed dict consumed ⟨out, false, .stored 0⟩ →
      DeflateParsed dict consumed ⟨out, false, .boundary⟩
  | storedFinal {consumed : List Bool} {out : List UInt8} :
      DeflateParsed dict consumed ⟨out, true, .stored 0⟩ →
      DeflateParsed dict consumed ⟨out, true, .finished⟩
  | fixedHeader {consumed : List Bool} {out : List UInt8} {final : Bool} :
      DeflateParsed dict consumed ⟨out, false, .boundary⟩ →
      DeflateParsed dict (consumed ++ [final, true, false])
        ⟨out, final, .codes fixedLitLens fixedDistLens .none⟩
  | dynamicStart {consumed : List Bool} {out : List UInt8} {final : Bool} :
      DeflateParsed dict consumed ⟨out, false, .boundary⟩ →
      DeflateParsed dict (consumed ++ [final, false, true]) ⟨out, final, .dynamicHeader []⟩
  | dynamicBits {consumed header : List Bool} {out : List UInt8} {final : Bool}
      (more : List Bool) :
      DeflateParsed dict consumed ⟨out, final, .dynamicHeader header⟩ →
      DeflateParsed dict (consumed ++ more) ⟨out, final, .dynamicHeader (header ++ more)⟩
  | dynamicDone {consumed header : List Bool} {out : List UInt8} {final : Bool}
      {L D : List Nat} :
      DeflateParsed dict consumed ⟨out, final, .dynamicHeader header⟩ →
      DynamicHeader header L D →
      DeflateParsed dict consumed ⟨out, final, .codes L D .none⟩
  /-- One complete literal or match. -/
  | token {consumed tokenBits : List Bool} {out out' : List UInt8} {final : Bool}
      {L D : List Nat} :
      DeflateParsed dict consumed ⟨out, final, .codes L D .none⟩ →
      Token.Step L D dict out tokenBits [] out' false →
      DeflateParsed dict (consumed ++ tokenBits) ⟨out', final, .codes L D .none⟩
  /-- The end-of-block symbol. -/
  | endOfBlock {consumed tokenBits : List Bool} {out : List UInt8} {L D : List Nat} :
      DeflateParsed dict consumed ⟨out, false, .codes L D .none⟩ →
      Token.Step L D dict out tokenBits [] out true →
      DeflateParsed dict (consumed ++ tokenBits) ⟨out, false, .boundary⟩
  | endOfFinal {consumed tokenBits : List Bool} {out : List UInt8} {L D : List Nat} :
      DeflateParsed dict consumed ⟨out, true, .codes L D .none⟩ →
      Token.Step L D dict out tokenBits [] out true →
      DeflateParsed dict (consumed ++ tokenBits) ⟨out, true, .finished⟩
  /-- A started length or distance (`LENEXT`, `DIST`, `DISTEXT`). -/
  | partialToken {consumed : List Bool} {out : List UInt8} {final : Bool} {L D : List Nat}
      {pending : Pending} (bits : List Bool) :
      DeflateParsed dict consumed ⟨out, final, .codes L D .none⟩ →
      PendingParsed L D bits pending →
      DeflateParsed dict (consumed ++ bits) ⟨out, final, .codes L D pending⟩
  /-- A complete match of which `written` bytes are out (`MATCH`). `dist` is
  the match distance: positive, within the history, at most 32768. -/
  | partialCopy {consumed tokenBits : List Bool} {out out' : List UInt8} {final : Bool}
      {L D : List Nat} {dist written : Nat} :
      DeflateParsed dict consumed ⟨out, final, .codes L D .none⟩ →
      Token.Step L D dict out tokenBits [] out' false →
      out' = copyBack dict dist (out'.length - out.length) out →
      written < out'.length - out.length →
      0 < dist → dist ≤ (dict ++ out).length → dist ≤ 32768 →
      DeflateParsed dict (consumed ++ tokenBits)
        ⟨out'.take (out.length + written), final,
          .codes L D (.copy (out'.length - out.length - written) dist)⟩
  /-- A decoded literal not yet written (`LIT`). -/
  | partialLiteral {consumed tokenBits : List Bool} {out : List UInt8} {final : Bool}
      {L D : List Nat} {byte : UInt8} :
      DeflateParsed dict consumed ⟨out, final, .codes L D .none⟩ →
      Token.Step L D dict out tokenBits [] (out ++ [byte]) false →
      DeflateParsed dict (consumed ++ tokenBits) ⟨out, final, .codes L D (.literal byte)⟩

/-! ## The wrapper layer -/

/-- The dictionary a deflate body may refer to: the last window of the
installed dictionary for raw data and for a zlib header with `FDICT`. -/
def bodyDictionary (window : Nat) (dict : List UInt8) : List UInt8 :=
  dict.drop (dict.length - window)

/-- A complete zlib header (with `DICTID` when `FDICT` is set) and the window
its body uses. -/
def ZlibHeader (configured : Nat) (dict header : List UInt8) (window : Nat) : Prop :=
  ∃ cmf flg, Zlib.HeaderOK cmf flg ∧ Api.ZlibFits configured [cmf, flg] ∧
    window = (if configured = 0 then Zlib.windowSize cmf else 2 ^ configured) ∧
    ((flg.toNat / 32 % 2 = 0 ∧ header = [cmf, flg]) ∨
     (flg.toNat / 32 % 2 = 1 ∧ header = [cmf, flg] ++ be32 (adler32 dict).toNat))

/-- A complete gzip header, optional header CRC included. -/
def GzipHeader (header : List UInt8) : Prop :=
  ∃ (flg : UInt8) (mtime : List UInt8) (xfl os : UInt8) (extra name comment : List UInt8),
    flg.toNat < 32 ∧ mtime.length = 4 ∧ extra.length < 2 ^ 16 ∧ 0 ∉ name ∧ 0 ∉ comment ∧
    header = Gzip.header flg mtime xfl os extra name comment ++
      (if flg.toNat / 2 % 2 = 1 then
        le16 ((crc32 (Gzip.header flg mtime xfl os extra name comment)).toNat % 2 ^ 16) else [])

/-- The header the configuration accepts, and the window and dictionary its
body uses. Raw data has an empty header. -/
def WrapHeader (wrap : Api.Wrap) (configured : Nat) (dict header : List UInt8)
    (bodyDict : List UInt8) : Prop :=
  match wrap with
  | .raw => header = [] ∧ bodyDict = bodyDictionary (2 ^ configured) dict
  | .zlib => ∃ window, ZlibHeader configured dict header window ∧
      bodyDict = (if header.length = 2 then [] else bodyDictionary window dict)
  | .gzip => GzipHeader header ∧ bodyDict = []
  | .auto => (∃ window, ZlibHeader configured dict header window ∧
      bodyDict = (if header.length = 2 then [] else bodyDictionary window dict)) ∨
    (GzipHeader header ∧ bodyDict = [])

/-- The trailer of a finished body. -/
def WrapTrailer (wrap : Api.Wrap) (header out : List UInt8) : List UInt8 :=
  match wrap with
  | .raw => []
  | .zlib => be32 (adler32 out).toNat
  | .gzip => le32 (crc32 out).toNat ++ le32 (out.length % 2 ^ 32)
  | .auto => if header.take 2 = [31, 139] then le32 (crc32 out).toNat ++ le32 (out.length % 2 ^ 32)
      else be32 (adler32 out).toNat

/-- Where the parse of the whole stream stands. -/
inductive WrapStage where
  /-- Inside the wrapper header; `bytes` read so far. Raw data stands here,
  with no bytes, until its first call leaves `HEAD`. -/
  | header (bytes : List UInt8)
  /-- A zlib header with `FDICT` read; the dictionary is still missing. Any
  identifier is admitted: zlib asks for the dictionary before it can compare. -/
  | needDict (header : List UInt8)
  /-- Inside the deflate body. -/
  | body (header : List UInt8) (pos : DeflatePos)
  /-- After the final block; `bytes` of the trailer read so far. -/
  | trailer (header : List UInt8) (out : List UInt8) (bytes : List UInt8)
  /-- The stream is complete. -/
  | done (out : List UInt8)

/-- `WrapParsed wrap configured dict consumed stage`: reading the bits
`consumed` of a stream reaches `stage`. Header, trailer and token positions
are ones a valid stream can pass through; the bits of a dynamic block header
are the ones zlib can hold before it rejects the header (`DeflateParsed`).
The rejection facts are carried by the `BAD` clause of `ParseMeaning`. -/
def WrapParsed (wrap : Api.Wrap) (configured : Nat) (dict : List UInt8)
    (consumed : List Bool) : WrapStage → Prop
  | .header bytes => consumed = bytesToBits bytes ∧
      ∃ more bodyDict, WrapHeader wrap configured dict (bytes ++ more) bodyDict ∧
        (more ≠ [] ∨ wrap = .raw)
  | .needDict header => consumed = bytesToBits header ∧
      (wrap = .zlib ∨ wrap = .auto) ∧
      ∃ cmf flg dictid, header = [cmf, flg] ++ dictid ∧ dictid.length = 4 ∧
        Zlib.HeaderOK cmf flg ∧ Api.ZlibFits configured [cmf, flg] ∧ flg.toNat / 32 % 2 = 1
  | .body header pos => ∃ bodyDict bits,
      WrapHeader wrap configured dict header bodyDict ∧
      consumed = bytesToBits header ++ bits ∧ DeflateParsed bodyDict bits pos
  | .trailer header out bytes => ∃ bodyDict bits pad,
      WrapHeader wrap configured dict header bodyDict ∧
      DeflateParsed bodyDict bits ⟨out, true, .finished⟩ ∧ wrap ≠ .raw ∧
      pad.length = (8 - bits.length % 8) % 8 ∧
      bytes <+: WrapTrailer wrap header out ∧ bytes ≠ WrapTrailer wrap header out ∧
      consumed = bytesToBits header ++ bits ++ pad ++ bytesToBits bytes
  | .done out => ∃ header bodyDict bits pad,
      WrapHeader wrap configured dict header bodyDict ∧
      DeflateParsed bodyDict bits ⟨out, true, .finished⟩ ∧
      pad.length = (8 - bits.length % 8) % 8 ∧
      consumed = bytesToBits header ++ bits ++ pad ++
        bytesToBits (WrapTrailer wrap header out)

/-! ## The decoder state of a position -/

/-- The bit buffer holds exactly `held`, least significant bit first. -/
def HeldBits (s : InflateState) (held : List Bool) : Prop :=
  held.length = s.bits.toNat ∧
    s.hold.toNat = (held.zipIdx.map fun (b, i) => if b then 2 ^ i else 0).sum

/-- An installed table decodes the canonical code of `lens`, and a lookup that
fits the held bits selects the same entry on every continuation (needed to
reject an invalid code on fewer than 15 held bits). -/
def TableMeaning (h : Heap) (pointer : CodePtr) (root : UInt32) (type : UInt32)
    (lens : List Nat) : Prop :=
  ∃ ref offset codes used, pointer = .ref ref offset ∧ Space.get h ref = some codes ∧
    Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type codes offset root.toNat used lens ∧
    Zlib.Inftrees.Spec.DecodeTableStability.StableQuery type codes offset root.toNat

/-- The code lengths stored so far, `lens[0 .. have)`. -/
def lensPrefix (s : InflateState) : List Nat :=
  (List.range s.«have».toNat).map fun k => (s.lens.getD k 0).toNat

/-- The held bits without the last byte, when at least 8 bits are held. zlib
pulls a byte only while the held bits do not complete the field it waits
for, so these bits never complete it (the bounds in `DynamicMatches` and
`BodyMatches`). -/
def heldShort (s : InflateState) : List Bool :=
  (List.range (s.bits.toNat - 8)).map fun i => s.hold.toNat.testBit i

/-- The repeat bits after a code-length symbol. -/
def codeLenExtra (symbol : Nat) : Nat :=
  if symbol = 16 then 2 else if symbol = 17 then 3 else if symbol = 18 then 7 else 0

/-- `bits` start with a complete code-length item: a symbol and its repeat bits. -/
def CodeLenItem (cl : List Nat) (bits : List Bool) : Prop :=
  ∃ symbol r1 x r2, decodeSym cl bits = some (symbol, r1) ∧
    readBits (codeLenExtra symbol) r1 = some (x, r2)

/-- The decoder state inside a dynamic block header that holds the header bits
`header`. `TABLE`: none. `LENLENS`: the three counts and the first `have`
code-length-code lengths, stored in `clOrder`. `CODELENS`: the counts, the
code-length code `cl` and its table, and a causal partial parse of the
lengths read so far, in both directions: a completion from the stored lengths
is one of the header, and every parse of the header passes through them. An empty code-length code passes `inflate_table`; its
cells `{op 64, bits 1, val 0}` are read as length 0, so only zeros are
stored until the end-of-block check fails. -/
def DynamicMatches (h : Heap) (s : InflateState) (header : List Bool) : Prop :=
  (s.mode = TABLE ∧ header = [] ∧ s.bits.toNat < 22) ∨
  ∃ (hlit hdist hclen : Nat) (r1 r2 r3 : List Bool),
    readBits 5 header = some (hlit, r1) ∧ readBits 5 r1 = some (hdist, r2) ∧
    readBits 4 r2 = some (hclen, r3) ∧ DynamicCountsOK hlit hdist ∧
    s.nlen.toNat = hlit + 257 ∧ s.ndist.toNat = hdist + 1 ∧ s.ncode.toNat = hclen + 4 ∧
    ((s.mode = LENLENS ∧ s.«have».toNat < hclen + 4 ∧ s.bits.toNat < 11 ∧
      ∃ vs, readNats 3 s.«have».toNat r3 = some (vs, []) ∧
        ∀ j, j < s.«have».toNat → (s.lens.getD (clOrder.getD j 0) 0).toNat = vs.getD j 0) ∨
     (s.mode = CODELENS ∧ ∃ (cl : List Nat) (r4 : List Bool) (ref : CodeRef) (offset : Nat)
        (codes : Array Code),
      readCodeLenLens (hclen + 4) r3 = some (cl, r4) ∧
      s.lencode = .ref ref offset ∧ Space.get h ref = some codes ∧
      Zlib.Inftrees.Proofs.CodeLengthMeaning codes offset s.lenbits.toNat cl ∧
      s.«have».toNat < hlit + 257 + (hdist + 1) ∧
      ZlibF.Math.CodeLengthPrefix.Trace cl (hlit + 257 + (hdist + 1)) [] r4 (lensPrefix s) ∧
      (∀ future rest lens, CodeLens cl (hlit + 257 + (hdist + 1)) [] (r4 ++ future) rest lens →
        CodeLens cl (hlit + 257 + (hdist + 1)) (lensPrefix s) future rest lens) ∧
      ((∀ k, cl.getD k 0 = 0) →
        (∀ i, i < 2 ^ s.lenbits.toNat → codes[offset + i]? = some ⟨64, 1, 0⟩) ∧
        ∀ k, k < s.«have».toNat → s.lens.getD k 0 = 0) ∧
      (s.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧ ¬ CodeLenItem cl (heldShort s)))))

/-- The window holds the last bytes of dictionary and output. Before the
window is set up (`wsize = 0`) there is no history: the next match may only
reach back into this call's output. -/
def WindowMeaning (h : Heap) (s : InflateState) (dict out : List UInt8) : Prop :=
  (s.wsize ≠ 0 ∧
    InflateDictionary h s ((dict ++ out).drop ((dict ++ out).length - s.wsize.toNat))) ∨
  (s.wsize = 0 ∧ s.whave = 0 ∧ dict ++ out = [])

/-- `check` and `total` are the running checksum and length of the output,
when the wrapper keeps them. -/
def CheckMeaning (s : InflateState) (wrap : Api.Wrap) (header out : List UInt8) : Prop :=
  s.total = UInt64.ofNat out.length ∧
    (s.wrap &&& 4 ≠ 0 →
      s.check = (if wrap = .gzip ∨ (wrap = .auto ∧ header.take 2 = [31, 139]) then
        (crc32 out).toUInt64 else (adler32 out).toUInt64))

/-- The modes of each deflate stage, the pending token in its fields, and the
tables of a Huffman stage. While zlib waits for a field it holds no byte it
does not need: the held bits without the last byte do not complete the field
(`heldShort`); this makes `bits < 8` at a block boundary inductive. At a
symbol only valid symbols are excluded: the reserved codes of the fixed
tables are rejected when looked up, and the table meaning does not fix how
many bits their entries take. At a block boundary fewer than 8 bits are held, so
`BYTEBITS` at the end of the last block drops exactly the padding (to confirm
by the per-mode proofs: the slow path pulls a byte only while bits are short,
`inflate_fast` returns whole unused bytes, a stored block ends after
`INITBITS`; checked on the real decoder by `tests/goals/inflate-meaning`). -/
def BodyMatches (h : Heap) (s : InflateState) : DeflatePos → Prop
  | ⟨_, final, .boundary⟩ => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ final = false ∧ s.last = 0 ∧
      s.bits.toNat < 8
  | ⟨_, final, .storedHeader⟩ => s.mode = STORED ∧ s.last = (if final then 1 else 0) ∧
      s.bits.toNat < 32
  | ⟨_, final, .stored remaining⟩ =>
      (s.mode = COPY_ ∨ s.mode = COPY) ∧
      s.length.toNat = remaining ∧ s.last = (if final then 1 else 0) ∧ s.bits = 0
  | ⟨_, final, .dynamicHeader header⟩ =>
      DynamicMatches h s header ∧ s.last = (if final then 1 else 0)
  | ⟨_, final, .codes L D pending⟩ =>
      s.last = (if final then 1 else 0) ∧
      TableMeaning h s.lencode s.lenbits LENS L ∧ TableMeaning h s.distcode s.distbits DISTS D ∧
      match pending with
      | .none => (s.mode = LEN_ ∨ s.mode = LEN) ∧
          (s.bits.toNat < 8 ∨ ∀ symbol rest, decodeSym L (heldShort s) = some (symbol, rest) →
            285 < symbol)
      | .lengthExtra symbol => s.mode = LENEXT ∧ s.extra.toNat = lengthExtras.getD (symbol - 257) 0 ∧
          s.length.toNat = lengthBases.getD (symbol - 257) 0 ∧ s.bits.toNat < 8 + s.extra.toNat
      | .distance length => s.mode = DIST ∧ s.length.toNat = length ∧
          (s.bits.toNat < 8 ∨ ∀ symbol rest, decodeSym D (heldShort s) = some (symbol, rest) →
            29 < symbol)
      | .distanceExtra length distanceSymbol => s.mode = DISTEXT ∧ s.length.toNat = length ∧
          s.extra.toNat = distExtras.getD distanceSymbol 0 ∧
          s.offset.toNat = distBases.getD distanceSymbol 0 ∧ s.bits.toNat < 8 + s.extra.toNat
      | .copy remaining dist => s.mode = MATCH ∧ s.length.toNat = remaining ∧ s.offset.toNat = dist ∧
          s.bits.toNat < 8
      | .literal byte => s.mode = LIT ∧ s.length.toNat = byte.toNat ∧ s.bits.toNat < 8
  | ⟨_, final, .finished⟩ => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ final = true ∧ s.last = 1 ∧
      s.bits.toNat < 8

/-- The decoder state of a stage. The header stages leave their per-mode
fields to `HeaderMatches`, refined with the header proofs. -/
def StageMatches (h : Heap) (s : InflateState) (wrap : Api.Wrap) (dict : List UInt8) :
    WrapStage → Prop
  | .header _ => HEAD ≤ s.mode ∧ s.mode ≤ DICTID
  | .needDict _ => s.mode = DICT
  | .body header pos => BodyMatches h s pos ∧ WindowMeaning h s dict pos.out ∧
      CheckMeaning s wrap header pos.out
  | .trailer header out _ => (s.mode = CHECK ∨ s.mode = LENGTH) ∧ CheckMeaning s wrap header out
  | .done _ => s.mode = DONE

/-- The stream-side fields of a stage (`inflate.c.meaning-stream`): the
header position, the dictionary identifier and the installed dictionary, the
flags word and width a complete header chose, the trailer bit buffer, and an
empty bit buffer at the end. Before and inside the body the epoch's
dictionary is empty unless the body may use it (raw data, or a zlib header
with `FDICT`): `inflateSetDictionary` succeeds only for raw data or in
`DICT`, and the window holds the dictionary, so a body without one must not
see it. -/
def WrapMatches (h : Heap) (s : InflateState) (wrap : Api.Wrap) (configured : Nat)
    (dict : List UInt8) : WrapStage → Prop
  | .header bytes => HeaderMatches s wrap configured bytes ∧ WindowMeaning h s dict [] ∧
      (dict = [] ∨ wrap = .raw)
  | .needDict header => s.check = dictId header ∧ s.flags = 0 ∧ s.bits = 0 ∧
      HeaderWidth s configured header ∧
      (s.havedict = 0 → s.wsize = 0 ∧ s.whave = 0) ∧
      (s.havedict ≠ 0 → be32 (adler32 dict).toNat = header.drop 2 ∧ WindowMeaning h s dict [])
  | .body header _ => FlagsMatch s wrap header ∧ HeaderWidth s configured header ∧
      (dict = [] ∨ wrap = .raw ∨ header.length = 6)
  | .trailer header out bytes => FlagsMatch s wrap header ∧ HeaderWidth s configured header ∧
      TrailerMatches s wrap header out bytes
  | .done _ => s.bits = 0

/-- The output a stage has produced. -/
def WrapStage.output : WrapStage → List UInt8
  | .header _ | .needDict _ => []
  | .body _ pos => pos.out
  | .trailer _ out _ | .done out => out

/-- Format meaning of the decoder after the data epoch `log`: the decoder keeps
the configuration of the trace; the consumed input minus the held bits parses
to a stage the decoder state represents, the delivered output is that stage's
output; a data error leaves `BAD` (or `MEM` for raw data, when a later raw
`inflateSetDictionary` failed to allocate the window,
`tests/goals/inflate-meaning/data-error-then-mem.c`) and means the consumed
input has no valid completion; after
an allocation failure (`MEM`) the output facts of `Goal.inflate_sequence`
still hold for the epoch so far. -/
def ParseMeaning (wb : Int32) (r : ZStreamRef) (h : Heap) (log : DataLog) (pending : Bool) :
    Prop :=
  ∃ wrap configured i z s, Api.inflWbits wb.toInt = some (wrap, configured) ∧
    InflateInv h r i z s ∧ ConfigMatches s wrap configured ∧
    (log.result = Z_DATA_ERROR → s.mode = BAD ∨ (s.mode = MEM ∧ wrap = .raw)) ∧
    (log.result = Z_STREAM_END → s.mode = DONE ∨ s.mode = MEM) ∧
    (log.singleDictionary = true → s.mode = BAD →
      ∀ source decoded, Api.Layer.Decodes wrap configured log.dictionary source decoded →
        Api.FullWindow wrap configured source → ¬ log.input <+: source) ∧
    (log.singleDictionary = true → s.mode = MEM →
      (log.result = Z_STREAM_END →
        Api.Layer.InflateAccepted wrap configured log.dictionary log.input log.output) ∧
      ∀ source decoded, Api.Layer.Decodes wrap configured log.dictionary source decoded →
        Api.FullWindow wrap configured source → log.input <+: source →
        log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
        (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded)) ∧
    (log.singleDictionary = true → s.mode ≠ BAD → s.mode ≠ MEM → s.mode ≠ SYNC →
      ∃ consumed held stage, bytesToBits log.input = consumed ++ held ∧ HeldBits s held ∧
        WrapParsed wrap configured log.dictionary consumed stage ∧
        StageMatches h s wrap log.dictionary stage ∧
        WrapMatches h s wrap configured log.dictionary stage ∧ log.output = stage.output ∧
        (pending = true ↔ ∃ header, stage = .needDict header ∧ s.havedict = 0))

end Zlib.Inflate.Proofs
