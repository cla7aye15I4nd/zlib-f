import ZlibF.Proof.«inflate.c.invariant»
import ZlibF.Spec.Format.Token
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
* `HeaderMeaning`: the partial wrapper header.
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
  /-- Inside a stored block with `remaining` bytes left (`STORED`, `COPY_`, `COPY`). -/
  | stored (remaining : Nat)
  /-- Inside a dynamic block header; `header` are its bits so far
  (`TABLE`, `LENLENS`, `CODELENS`). -/
  | dynamicHeader (header : List Bool)
  /-- Inside a Huffman block with literal/length lengths `L` and distance
  lengths `D` (`LEN_`, `LEN`, `LENEXT`, `DIST`, `DISTEXT`, `MATCH`, `LIT`). -/
  | codes (L D : List Nat) (pending : Pending)
  /-- After the final block (`CHECK`, `LENGTH`, `DONE`). -/
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
keeps for it (`LENEXT`, `DIST`, `DISTEXT`). -/
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
  | .copy _ _ => False
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

/-- A dynamic block header that can still be completed. -/
def DynamicHeaderPrefix (header : List Bool) : Prop :=
  ∃ (more : List Bool) (L D : List Nat), DynamicHeader (header ++ more) L D

/-- `DeflateParsed dict consumed pos`: reading the deflate bits `consumed`
from the start of the data reaches `pos`. Every step is a step of
`Blocks`/`Body`/`Symbols`; a partial token or header is admitted only when it
can still be completed. -/
inductive DeflateParsed (dict : List UInt8) : List Bool → DeflatePos → Prop
  | start : DeflateParsed dict [] ⟨[], false, .boundary⟩
  /-- A block header `BFINAL`, `BTYPE` at a boundary of a non-final block. -/
  | storedHeader {consumed : List Bool} {out : List UInt8} {final : Bool}
      {pad : List Bool} {len : Nat} :
      DeflateParsed dict consumed ⟨out, false, .boundary⟩ →
      pad.length = (8 - (consumed.length + 3) % 8) % 8 →
      len < 65536 →
      DeflateParsed dict
        (consumed ++ [final, false, false] ++ pad ++ natToBitsLSB 16 len ++
          natToBitsLSB 16 (65535 - len))
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
      DynamicHeaderPrefix (header ++ more) →
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
  /-- A complete match of which `written` bytes are out (`MATCH`). -/
  | partialCopy {consumed tokenBits : List Bool} {out out' : List UInt8} {final : Bool}
      {L D : List Nat} {dist written : Nat} :
      DeflateParsed dict consumed ⟨out, final, .codes L D .none⟩ →
      Token.Step L D dict out tokenBits [] out' false →
      out' = copyBack dict dist (out'.length - out.length) out →
      written < out'.length - out.length →
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
  /-- Inside the wrapper header; `bytes` read so far. -/
  | header (bytes : List UInt8)
  /-- A zlib header with `FDICT` read; the dictionary is still missing. -/
  | needDict (header : List UInt8)
  /-- Inside the deflate body. -/
  | body (header : List UInt8) (pos : DeflatePos)
  /-- After the final block; `bytes` of the trailer read so far. -/
  | trailer (header : List UInt8) (out : List UInt8) (bytes : List UInt8)
  /-- The stream is complete. -/
  | done (out : List UInt8)

/-- `WrapParsed wrap configured dict consumed stage`: reading the bits
`consumed` of a stream reaches `stage`. Only positions that a valid stream
can pass through are reachable. -/
def WrapParsed (wrap : Api.Wrap) (configured : Nat) (dict : List UInt8)
    (consumed : List Bool) : WrapStage → Prop
  | .header bytes => consumed = bytesToBits bytes ∧
      ∃ more bodyDict, WrapHeader wrap configured dict (bytes ++ more) bodyDict ∧
        (wrap = .raw → False) ∧ more ≠ []
  | .needDict header => consumed = bytesToBits header ∧
      (wrap = .zlib ∨ wrap = .auto) ∧ header.length = 6 ∧
      ∃ window, ZlibHeader configured dict header window ∨
        ∃ dict', ZlibHeader configured dict' header window
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

/-- An installed table decodes the canonical code of `lens`. -/
def TableMeaning (h : Heap) (pointer : CodePtr) (root : UInt32) (type : UInt32)
    (lens : List Nat) : Prop :=
  ∃ ref offset codes used, pointer = .ref ref offset ∧ Space.get h ref = some codes ∧
    Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type codes offset root.toNat used lens

/-- The window holds the last bytes of dictionary and output. -/
def WindowMeaning (h : Heap) (s : InflateState) (dict out : List UInt8) : Prop :=
  InflateDictionary h s ((dict ++ out).drop ((dict ++ out).length - s.wsize.toNat)) ∨
    (s.wsize = 0 ∧ s.whave = 0)

/-- `check` and `total` are the running checksum and length of the output,
when the wrapper keeps them. -/
def CheckMeaning (s : InflateState) (wrap : Api.Wrap) (header out : List UInt8) : Prop :=
  s.total = UInt64.ofNat out.length ∧
    (s.wrap &&& 4 ≠ 0 →
      s.check = (if wrap = .gzip ∨ (wrap = .auto ∧ header.take 2 = [31, 139]) then
        (crc32 out).toUInt64 else (adler32 out).toUInt64))

/-- The modes of each deflate stage, the pending token in its fields, and the
tables of a Huffman stage. -/
def BodyMatches (h : Heap) (s : InflateState) : DeflatePos → Prop
  | ⟨_, final, .boundary⟩ => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ (final = false)
  | ⟨_, final, .stored remaining⟩ =>
      (s.mode = COPY_ ∨ s.mode = COPY ∨ (s.mode = STORED ∧ remaining = 0)) ∧
      s.length.toNat = remaining ∧ s.last = (if final then 1 else 0)
  | ⟨_, final, .dynamicHeader _⟩ =>
      (s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) ∧ s.last = (if final then 1 else 0)
  | ⟨_, final, .codes L D pending⟩ =>
      s.last = (if final then 1 else 0) ∧
      TableMeaning h s.lencode s.lenbits LENS L ∧ TableMeaning h s.distcode s.distbits DISTS D ∧
      match pending with
      | .none => s.mode = LEN_ ∨ s.mode = LEN
      | .lengthExtra symbol => s.mode = LENEXT ∧ s.extra.toNat = lengthExtras.getD (symbol - 257) 0 ∧
          s.length.toNat = lengthBases.getD (symbol - 257) 0
      | .distance length => s.mode = DIST ∧ s.length.toNat = length
      | .distanceExtra length distanceSymbol => s.mode = DISTEXT ∧ s.length.toNat = length ∧
          s.extra.toNat = distExtras.getD distanceSymbol 0 ∧
          s.offset.toNat = distBases.getD distanceSymbol 0
      | .copy remaining dist => s.mode = MATCH ∧ s.length.toNat = remaining ∧ s.offset.toNat = dist
      | .literal byte => s.mode = LIT ∧ s.length.toNat = byte.toNat
  | ⟨_, _, .finished⟩ => s.mode = CHECK ∨ s.mode = LENGTH ∨ s.mode = DONE

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

/-- The output a stage has produced. -/
def WrapStage.output : WrapStage → List UInt8
  | .header _ | .needDict _ => []
  | .body _ pos => pos.out
  | .trailer _ out _ | .done out => out

/-- Format meaning of the decoder after the data epoch `log`: the consumed
input minus the held bits parses to a stage the decoder state represents, the
delivered output is that stage's output, and a data error means the consumed
input has no valid completion. -/
def ParseMeaning (wb : Int32) (r : ZStreamRef) (h : Heap) (log : DataLog) (pending : Bool) :
    Prop :=
  ∃ wrap configured i z s, Api.inflWbits wb.toInt = some (wrap, configured) ∧
    InflateInv h r i z s ∧
    (log.result = Z_DATA_ERROR →
      s.mode = BAD ∧ ∀ source decoded, Api.Layer.Decodes wrap configured log.dictionary source decoded →
        ¬ log.input <+: source) ∧
    (s.mode ≠ BAD → s.mode ≠ MEM → s.mode ≠ SYNC →
      ∃ consumed held stage, bytesToBits log.input = consumed ++ held ∧ HeldBits s held ∧
        WrapParsed wrap configured log.dictionary consumed stage ∧
        StageMatches h s wrap log.dictionary stage ∧ log.output = stage.output ∧
        (pending = true ↔ ∃ header, stage = .needDict header ∧ s.havedict = 0))

end Zlib.Inflate.Proofs
