import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Spec.Public.Sequences
import ZlibF.Math.DeflateEncodingPrefix
import ZlibF.Math.DeflateSymbolTrace
import ZlibF.Spec.Functional.Sequences

/-!
# deflate.c: the ledger of a data epoch (definitions)

Batch D of the deflate skeleton, functional half. `LedgerAt` relates one deflate state to what
the caller has given (the dictionary and the accepted input) and what the stream has emitted
(the delivered output, the pending bytes and the held bits). It holds at every call boundary of
a data epoch (`DeflateDataTrace`: initialization, rebuffering, `deflate` calls and a dictionary
before data) and at the cut points inside a call that the `ledger_*` lemmas of the skeleton
name. The statements of those lemmas are on `skeleton/deflate`; this module holds only
definitions.

The phases of a stream:

* **header**: the zlib or gzip header is being written; no input is accepted yet; the emitted
  bits are a prefix of the header.
* **data**: the emitted bits are the header followed by complete non-final blocks, which decode
  to the accepted input up to the start of the current block; the current block (recorded
  symbols at a nonzero level, window bytes at level 0) covers the input from there up to the
  lazy literal and the lookahead.
* **finished**: the final block has been emitted and aligned; with the trailer (still to be
  written when `wrap > 0`) the emitted bytes are a stream that decodes to the accepted input.

A window index `i` holds the data index `data.length + i - (strstart + lookahead)`, where `data` is
the reachable dictionary followed by the accepted input (`WindowHolds`).

Tested before the proof: `tests/goals/deflate/ledger.c` and `ledger_check.py` check the phases,
the block decoding, the open block relations and the window on 60000 random histories of the real
C (plus 4000 under ASan and UBSan), with no failure. Evidence, not proof.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The dictionary bytes a back-reference may reach (`DecodesFor`): the last `2^wbits`. -/
def windowDictionary (p : Api.DeflParams) (dictionary : List UInt8) : List UInt8 :=
  dictionary.drop (dictionary.length - 2 ^ p.wbits)

/-- The data of an epoch as the decoder sees it: the reachable dictionary, then the input. -/
def epochData (p : Api.DeflParams) (dictionary accepted : List UInt8) : List UInt8 :=
  windowDictionary p dictionary ++ accepted

/-- The wrapper header the C writes for these parameters and this dictionary. A data epoch sets
no gzip header (`DeflateDataTrace` has no `deflateSetHeader`), so the gzip header has no
optional fields. -/
def HeaderFor (p : Api.DeflParams) (dictionary header : List UInt8) : Prop :=
  match p.wrap with
  | .raw => header = []
  | .zlib => ∃ cmf flg, Zlib.HeaderOK cmf flg ∧ cmf.toNat / 16 + 8 = p.wbits ∧
      (flg.toNat / 32 % 2 = 1 ↔ dictionary ≠ []) ∧
      header = cmf :: flg :: (if dictionary = [] then [] else be32 (ZlibF.Spec.adler32 dictionary).toNat)
  | .gzip => ∃ mtime xfl os, mtime.length = 4 ∧ header = Gzip.header 0 mtime xfl os [] [] []

/-- The window ends with the data: every window index below `strstart + lookahead` that
corresponds to a data index holds that byte. Earlier window bytes are not constrained: after
several dictionaries the window may hold bytes of an earlier dictionary beyond the last `2^wbits`
dictionary bytes the decoder sees (`tests/goals/deflate/ledger.c`, L4). -/
def WindowHolds (h : Heap) (d : DeflateState) (data : List UInt8) : Prop :=
  ∃ w a, d.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
    ∀ j, j < d.strstart.toNat + d.lookahead.toNat →
      d.strstart.toNat + d.lookahead.toNat ≤ data.length + j →
      a[j]? = data[data.length + j - (d.strstart.toNat + d.lookahead.toNat)]?

/-- The emitted bits: the delivered output, the pending bytes and the held bits. -/
def Emitted (h : Heap) (d : DeflateState) (delivered : List UInt8) (bits : List Bool) : Prop :=
  ∃ held, PendingBits h d held ∧ bits = bytesToBits delivered ++ held

/-- The data index where the current block starts: window index `block_start`. -/
def BlockStartAt (d : DeflateState) (data : List UInt8) (start : Nat) : Prop :=
  (start : Int) = (data.length : Int) - (d.strstart.toNat + d.lookahead.toNat : Nat) + d.block_start.toInt

/-- The current block, from data index `start`: at a nonzero level the recorded symbols mean the
data from `start` (`Trace`) and end before the lazy literal and the lookahead; at level 0 the
window bytes from `block_start` to `strstart` are the block, and the lookahead is empty. -/
def OpenBlock (h : Heap) (d : DeflateState) (data : List UInt8) (start : Nat) : Prop :=
  (d.level ≠ 0 → ∃ xs, Recorded h d xs ∧ Trace (fun i => data.getD i 0) start xs ∧
    start + represented xs + d.match_available.toInt.toNat + d.lookahead.toNat = data.length) ∧
  (d.level = 0 → start + (d.strstart.toNat - d.block_start.toInt.toNat) + d.lookahead.toNat = data.length)

/-- The states in which `deflate` is writing the wrapper header. -/
def HeaderPhase (d : DeflateState) : Prop :=
  d.status = INIT_STATE ∨ d.status = GZIP_STATE ∨ d.status = EXTRA_STATE ∨
    d.status = NAME_STATE ∨ d.status = COMMENT_STATE ∨ d.status = HCRC_STATE

/-- **The ledger at a cut point.** `accepted` is the input the stream has consumed in this
epoch, `delivered` the output it has written to the caller. -/
structure LedgerAt (p : Api.DeflParams) (dictionary : List UInt8) (h : Heap) (r : ZStreamRef)
    (ds : Nat) (z : ZStream) (d : DeflateState) (accepted delivered : List UInt8) : Prop where
  inv : DInv h r ds z d
  window : WindowHolds h d (epochData p dictionary accepted)
  phase :
    (HeaderPhase d ∧ accepted = [] ∧ ∃ header bits, HeaderFor p dictionary header ∧
      Emitted h d delivered bits ∧ bits <+: bytesToBits header) ∨
    (d.status = BUSY_STATE ∧ ∃ header blockBits start,
      HeaderFor p dictionary header ∧ Emitted h d delivered (bytesToBits header ++ blockBits) ∧
      start ≤ accepted.length ∧
      BlockStartAt d (epochData p dictionary accepted) ((windowDictionary p dictionary).length + start) ∧
      BlockPrefix (windowDictionary p dictionary) (8 * header.length) [] blockBits (accepted.take start) ∧
      OpenBlock h d (epochData p dictionary accepted) ((windowDictionary p dictionary).length + start)) ∨
    (d.status = FINISH_STATE ∧ d.bi_valid = 0 ∧ ∃ pend rest,
      Bytes h d.pending_out d.pending.toNat pend ∧ (d.wrap.toInt ≤ 0 → rest = []) ∧
      DecodesFor p dictionary (delivered ++ pend ++ rest) accepted)

/-- **The ledger of a data epoch** at a call boundary. -/
def Ledger (p : Api.DeflParams) (h : Heap) (r : ZStreamRef) (log : DataLog) : Prop :=
  ∃ ds z d, LedgerAt p log.dictionary h r ds z d log.input log.output

end Zlib.Deflate.Universal
