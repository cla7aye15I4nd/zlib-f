import ZlibF.Spec.Api.Inflate

/-!
# API model: the deflate stream

A heap-free model of one `z_stream` used for `deflate`, in the same style as `Inflate.lean`:
the state remembers the whole input accepted and the whole output delivered, and a call is a
relation between the state before, the inputs, and the results. What the compressor chooses
(block boundaries, match lengths, how much input a call takes before the output is full) is not
specified; what `zlib.h` promises is.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

/-- The model of an initialised deflate stream.

* `input`, `produced`: all input accepted and all output delivered since init or reset.
* `dict`: the preset dictionary; `hdr`: the header given to `deflateSetHeader`.
* `pend`, `bits`: bytes and bits the library holds and has not delivered (`deflatePending`).
* `last`: the flush value of the previous call (`last_flush`; -2 after init, -1 after a call
  that filled the output).
* `finishing`: `Z_FINISH` was accepted. `done`: the whole stream, trailer included, was delivered.
* `started`: a call got past the argument checks (the header is being written).
* `clean`: nothing since init changed the stream except input and `Z_FINISH`, so that
  `deflateBound` applies. `precise`: the data-level promises apply (cleared by priming bits, by
  setting a dictionary or a header at a time that `zlib.h` does not allow).
* `fullAt`: lengths of `produced` and `input` at the last completed `Z_FULL_FLUSH`. -/
structure DeflState where
  params : DeflParams
  dict : Option (List UInt8)
  hdr : Option GzHead
  input : List UInt8
  produced : List UInt8
  totalIn : Nat
  totalOut : Nat
  adler : UInt32
  pend : Nat
  bits : Nat
  last : Int
  finishing : Bool
  done : Bool
  started : Bool
  clean : Bool
  precise : Bool
  fullAt : Option (Nat × Nat)

/-- The state after `deflateInit2` / `deflateReset` (`deflateResetKeep`: `adler` is the CRC-32 or
Adler-32 of nothing, `last_flush = -2`, no header, no dictionary). -/
def DeflState.fresh (p : DeflParams) : DeflState where
  params := p
  dict := none
  hdr := none
  input := []
  produced := []
  totalIn := 0
  totalOut := 0
  adler := if p.wrap = .gzip then 0 else 1
  pend := 0
  bits := 0
  last := -2
  finishing := false
  done := false
  started := false
  clean := true
  precise := true
  fullAt := none

/-- The dictionary as the format specification takes it (none: empty). -/
def DeflState.dictEff (st : DeflState) : List UInt8 := st.dict.getD []

/-- The header record that is written: the one set, else the default. -/
def DeflState.header (st : DeflState) : GzHead := st.hdr.getD GzHead.default

/-- `deflateBound(strm, n)` (`deflate.c`), without the overflow clamp (the argument is below
`2^60`): wrapper length, then one of three bounds. -/
def DeflState.bound (st : DeflState) (n : Nat) : Nat :=
  let p := st.params
  let fixedlen := n + n / 8 + n / 256 + n / 512 + 4
  let storelen := n + n / 32 + n / 128 + n / 2048 + 7
  let h := st.header
  let wraplen :=
    match p.wrap with
    | .raw => 0
    | .zlib => 6 + (if st.dictEff ≠ [] then 4 else 0)
    | .gzip =>
      18 + (if st.hdr.isNone then 0 else
        (match h.extra with | some e => 2 + e.length | none => 0) +
        (match h.name with | some s => s.length + 1 | none => 0) +
        (match h.comment with | some s => s.length + 1 | none => 0) +
        (if h.hcrc then 2 else 0))
  if p.wbits ≠ 15 ∨ p.memLevel + 7 ≠ 15 then
    (if p.wbits ≤ p.memLevel + 7 ∧ p.level ≠ 0 then fixedlen else storelen) + wraplen
  else n + n / 4096 + n / 16384 + n / 2 ^ 25 + 13 - 6 + wraplen

/-- The compression function class of a level (`configuration_table`): 0 stored, 1 fast
(levels 1 to 3), 2 lazy (levels 4 to 9). -/
def funcOf (level : Nat) : Nat := if level = 0 then 0 else if level ≤ 3 then 1 else 2

/-- `F-deflate-valid` for the configuration of a stream: `produced` is a complete stream of the
stream's layer for `input` (with the stream's dictionary and header; the zlib header announces
the stream's window and has `FDICT` set exactly when the dictionary is not empty). -/
def DeflState.Valid (st : DeflState) (produced input : List UInt8) : Prop :=
  match st.params.wrap with
  | .raw => Deflate.Decodes (st.dictEff.drop (st.dictEff.length - 2 ^ st.params.wbits)) produced input
  | .zlib => Zlib.Decodes st.dictEff produced input ∧
      produced.head?.map (·.toNat / 16 + 8) = some st.params.wbits ∧
      ∃ cmf flg r, produced = cmf :: flg :: r ∧ (flg.toNat / 32 % 2 = 1 ↔ st.dictEff ≠ [])
  | .gzip => Gzip.DecodesWith (st.header.bytes st.params) produced input

/-- The stream that follows the output of a complete sync or full flush, closing the stream
without more data: an empty final fixed block (`03 00`) and the trailer of the layer. -/
def closer (w : DWrap) (input : List UInt8) : List UInt8 :=
  [3, 0] ++ (match w with
    | .raw => []
    | .zlib => be32 (adler32 input).toNat
    | .gzip => le32 (crc32 input).toNat ++ le32 (input.length % 2 ^ 32))

/-- `F-deflate-flush`: after a completed `Z_SYNC_FLUSH` or `Z_FULL_FLUSH`, the output so far
followed by `closer` is a valid stream of all input so far; in other words the output ends on a
byte boundary with an empty stored block, and a decoder that gets exactly this output can recover
all the input. -/
def DeflState.FlushedAt (st : DeflState) (produced input : List UInt8) : Prop :=
  st.Valid (produced ++ closer st.params.wrap input) input

/-- What one call of `deflate` is given. `badBuf`: `next_out` is null or `next_in` is null with
`avail_in ≠ 0`. -/
structure DeflCall where
  inp : List UInt8
  availOut : Nat
  flush : Flush
  badBuf : Bool

/-- What one call of `deflate` returns. -/
structure DeflOut where
  consumed : Nat
  produced : List UInt8
  rc : Int

/-- The checksum that `strm->adler` holds once input has been accepted: Adler-32 for zlib,
CRC-32 for gzip. -/
def DeflState.check (st : DeflState) (input : List UInt8) : Option UInt32 :=
  match st.params.wrap with
  | .raw => none | .zlib => some (adler32 input) | .gzip => some (crc32 input)

/-- The part of the effect of `deflate` and `deflateParams` that is just bookkeeping: input
accepted, output delivered, totals, and the fields that do not change. -/
def DeflFrame (st : DeflState) (c : DeflCall) (o : DeflOut) (st' : DeflState) : Prop :=
  o.consumed ≤ c.inp.length ∧ o.produced.length ≤ c.availOut ∧
  st'.input = st.input ++ c.inp.take o.consumed ∧ st'.produced = st.produced ++ o.produced ∧
  st'.totalIn = st.totalIn + o.consumed ∧ st'.totalOut = st.totalOut + o.produced.length ∧
  st'.dict = st.dict ∧ st'.hdr = st.hdr ∧ st'.fullAt = st.fullAt

/-- `deflate(strm, flush)` once it got past the argument checks, with room, on a stream
(`zlib.h` `deflate`, `A-deflate-flush`, `F-deflate-valid`, `F-deflate-flush`, `A-deflate-bound`):

1. *Frame*: `DeflFrame`; the parameters do not change; the checksum field is the checksum of
   the input accepted so far once the call returned `Z_OK` or `Z_STREAM_END`.
2. *Refused calls*: a repeated flush without new input is `Z_BUF_ERROR` and nothing else happens;
   after `Z_FINISH`, new input is refused and nothing is consumed.
3. *Return codes*: input is left over only if the output is full; `Z_FINISH` with `Z_OK` means the
   output is full; `Z_STREAM_END` only for `Z_FINISH` with all input consumed and the whole
   stream delivered, and it is a valid stream of the input (`Valid`), no longer than `bound`
   (if `clean`); for raw deflate, what follows a completed full flush is a valid stream by itself
   (the full flush forgets the history); a complete sync or full flush (`Z_OK` with room left) consumed all input and
   leaves nothing pending, on a byte boundary (`FlushedAt`); every complete flush consumed
   all input.
4. *Liveness*: `Z_FINISH` with enough room for the bound ends the stream.

The promises about the content need `precise`. -/
def DeflRun (st : DeflState) (c : DeflCall) (o : DeflOut) (st' : DeflState) : Prop :=
  let input' := st.input ++ c.inp.take o.consumed
  let produced' := st.produced ++ o.produced
  -- 1. frame
  DeflFrame st c o st' ∧ st'.params = st.params ∧ st'.precise = st.precise ∧
  (o.rc = Z.ok ∨ o.rc = Z.streamEnd → st'.started = true ∧
    ∀ v, st.check input' = some v → st'.adler = v) ∧
  (o.rc = Z.ok ∨ o.rc = Z.streamEnd ∨ o.rc = Z.bufError) ∧
  -- 2. refused calls
  ((st.pend = 0 ∧ c.inp = [] ∧ c.flush ≠ .finish ∧ Flush.rank c.flush.code ≤ Flush.rank st.last) →
    o.rc = Z.bufError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = { st with last := c.flush.code }) ∧
  (st.finishing = true → c.inp ≠ [] → o.consumed = 0 ∧
    (o.rc = Z.bufError ∨ (o.rc = Z.ok ∧ o.produced.length = c.availOut))) ∧
  -- 3. return codes
  (o.rc = Z.ok → o.consumed < c.inp.length → o.produced.length = c.availOut) ∧
  (o.rc = Z.ok → c.flush = .finish → o.produced.length = c.availOut) ∧
  (o.rc = Z.streamEnd → c.flush = .finish ∧ o.consumed = c.inp.length ∧ st'.done = true ∧
    st'.finishing = true ∧ st'.pend = 0 ∧ st'.bits = 0 ∧
    (st.precise = true → st.Valid produced' input') ∧
    (st.precise = true → st.params.wrap = .raw → st.dict = none → ∀ pl il,
      st.fullAt = some (pl, il) → Deflate.Decodes [] (produced'.drop pl) (input'.drop il)) ∧
    (st.clean = true → produced'.length ≤ st.bound input'.length)) ∧
  (o.rc = Z.ok → o.produced.length < c.availOut →
    (c.flush = .partialFlush ∨ c.flush = .syncFlush ∨ c.flush = .fullFlush ∨ c.flush = .block) →
    o.consumed = c.inp.length ∧ st'.pend = 0 ∧ st'.clean = false) ∧
  (o.rc = Z.ok → o.produced.length < c.availOut →
    (c.flush = .syncFlush ∨ c.flush = .fullFlush) →
    st'.bits = 0 ∧ (st.precise = true → st.FlushedAt produced' input')) ∧
  (o.rc = Z.ok → o.produced.length < c.availOut → c.flush = .fullFlush →
    st'.fullAt = some (produced'.length, input'.length)) ∧
  (c.flush ≠ .finish → st'.finishing = st.finishing) ∧ (st.done = true → st'.done = true) ∧
  (c.flush ≠ .finish → st'.done = st.done) ∧
  (c.flush = .noFlush → st'.clean = st.clean) ∧
  -- 4. liveness
  (c.flush = .finish → st.clean = true → st.precise = true → st.finishing = false → st.done = false →
    st.bound (st.input.length + c.inp.length) ≤ st.produced.length + c.availOut →
    o.rc = Z.streamEnd)

/-- `deflate(strm, flush)` (`deflate.c`, start of `deflate`): `Z_TREES` is not a deflate flush
value, a bad buffer, or a flush other than `Z_FINISH` after `Z_FINISH`, is `Z_STREAM_ERROR`;
no room (`avail_out = 0`) is `Z_BUF_ERROR`; all without changing the state. -/
def DeflStep (st : DeflState) (c : DeflCall) (o : DeflOut) (st' : DeflState) : Prop :=
  (c.flush = .trees →
    o.rc = Z.streamError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st) ∧
  (c.flush ≠ .trees →
    (c.badBuf = true ∨ (st.finishing = true ∧ c.flush ≠ .finish)) →
      o.rc = Z.streamError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st) ∧
  (c.flush ≠ .trees → c.badBuf = false → ¬ (st.finishing = true ∧ c.flush ≠ .finish) →
    c.availOut = 0 → o.rc = Z.bufError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st) ∧
  (c.flush ≠ .trees → c.badBuf = false → ¬ (st.finishing = true ∧ c.flush ≠ .finish) →
    c.availOut ≠ 0 → DeflRun st c o st')

/-! ## The other deflate functions -/

/-- `deflateInit2_` / `deflateInit_`: the result and the new stream. `Z_MEM_ERROR` is an
allocation failure (then there is no stream and nothing stays allocated). -/
def DeflInit (level method wbits memLevel strategy : Int) (versionOK : Bool) (rc : Int)
    (r : Option DeflState) : Prop :=
  if versionOK = false then rc = Z.versionError ∧ r = none
  else match deflInit? level method wbits memLevel strategy with
    | none => rc = Z.streamError ∧ r = none
    | some p => (rc = Z.ok ∧ r = some (DeflState.fresh p)) ∨ (rc = Z.memError ∧ r = none)

/-- `deflateReset(strm)`: forgets all data, the dictionary and the header, keeps the parameters
(`Z_OK`). The parameters are those last set by `deflateParams`. -/
def DeflReset (st : DeflState) (rc : Int) (st' : DeflState) : Prop :=
  rc = Z.ok ∧ st' = DeflState.fresh st.params

/-- `deflateEnd(strm)`: `Z_DATA_ERROR` only if the stream is freed while it is busy, that is
after a call that started it and before `Z_FINISH`; `Z_OK` if it never started or finished. -/
def DeflEnd (st : DeflState) (rc : Int) : Prop :=
  (rc = Z.ok ∨ rc = Z.dataError) ∧ ((st.started = false ∨ st.finishing = true) → rc = Z.ok)

/-- `deflateParams(strm, level, strategy)` with the input and the output room that the stream
has at the time of the call. If the strategy or the compression function changes after the
stream started, zlib first completes the current block (`deflate(strm, Z_BLOCK)`), into the
output room and from the input that is there. It then returns `Z_OK` with the new parameters
(all input accepted), or `Z_BUF_ERROR` with the old ones. An invalid level or strategy is
`Z_STREAM_ERROR`. The model: if no flush is needed, nothing is consumed or produced. -/
def DeflParamsFn (st : DeflState) (level strategy : Int) (c : DeflCall) (o : DeflOut)
    (st' : DeflState) : Prop :=
  let level' : Int := if level = -1 then 6 else level
  if level' < 0 ∨ level' > 9 ∨ strategy < 0 ∨ strategy > 4 then
    o.rc = Z.streamError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st
  else
    let p' := { st.params with level := level'.toNat, strategy := strategy.toNat }
    if (strategy.toNat ≠ st.params.strategy ∨ funcOf level'.toNat ≠ funcOf st.params.level) ∧
        st.last ≠ -2 then
      (st.finishing = true ∧ o.rc = Z.streamError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st) ∨
      (st.finishing = false ∧ DeflFrame st c o st' ∧ st'.clean = false ∧
        ((o.rc = Z.ok ∧ o.consumed = c.inp.length ∧ st'.params = p') ∨
         (o.rc = Z.bufError ∧ st'.params = st.params)))
    else
      o.rc = Z.ok ∧ o.consumed = 0 ∧ o.produced = [] ∧
        st' = { st with params := p', clean := false }

/-- `deflateTune(strm, ...)`: `Z_OK`; only the choice of matches changes (not modelled), and
`deflateBound` no longer applies. -/
def DeflTune (st : DeflState) (rc : Int) (st' : DeflState) : Prop :=
  rc = Z.ok ∧ st' = { st with clean := false }

/-- `deflateBound(strm, n)`: the value `DeflState.bound`, an upper bound on the size of the
complete output for `n` bytes of input (`DeflRun`, clause 3). -/
def DeflBound (st : DeflState) (n r : Nat) : Prop := r = st.bound n

/-- `deflateSetDictionary(strm, dict, len)`. Not for gzip (`Z_STREAM_ERROR`); for zlib only
before the first `deflate`, and then the adler field becomes the Adler-32 of the dictionary (the
`DICTID`) and the dictionary becomes the preset dictionary. For raw deflate it is allowed
when no accepted input is still unflushed; the model gives the data-level promises only when
no input has been accepted. -/
def DeflSetDict (st : DeflState) (d : List UInt8) (rc : Int) (st' : DeflState) : Prop :=
  match st.params.wrap with
  | .gzip => rc = Z.streamError ∧ st' = st
  | .zlib =>
    if st.started = true then rc = Z.streamError ∧ st' = st
    else rc = Z.ok ∧ st' = { st with dict := some d, adler := adler32 d }
  | .raw =>
    if st.input = [] then rc = Z.ok ∧ st' = { st with dict := some d }
    else (rc = Z.streamError ∧ st' = st) ∨
      (rc = Z.ok ∧ st' = { st with dict := some d, precise := false, clean := false })

/-- `deflateGetDictionary(strm, buf, &len)`: `Z_OK`; the dictionary returned is a suffix of the
history (the preset dictionary and the input since the last full flush), at most the window, and
at least the window less 262 bytes (the part that the compressor may already have dropped), or
all of it if shorter. -/
def DeflGetDict (st : DeflState) (buf : List UInt8) (rc : Int) : Prop :=
  let hist := st.dictEff ++ st.input.drop ((st.fullAt.map (·.2)).getD 0)
  let w := 2 ^ st.params.wbits
  rc = Z.ok ∧ buf <:+ hist ∧ buf.length ≤ w ∧ min hist.length (w - 262) ≤ buf.length

/-- `deflateCopy(dest, source)`: an independent copy of the same model state; `Z_MEM_ERROR` leaves
`dest` without a state. -/
def DeflCopy (st : DeflState) (rc : Int) (dest : Option DeflState) : Prop :=
  (rc = Z.ok ∧ dest = some st) ∨ (rc = Z.memError ∧ dest = none)

/-- `deflatePending(strm, &pending, &bits)`: the bytes and the bits not delivered yet. -/
def DeflPending (st : DeflState) (pending bits : Nat) (rc : Int) : Prop :=
  rc = Z.ok ∧ pending = st.pend ∧ bits = st.bits

/-- `deflatePrime(strm, bits, value)`: `Z_BUF_ERROR` if `bits` is not in 0 to 16 or the pending
buffer has no room; otherwise `Z_OK` and the low `bits` bits of `value` are inserted in the
output (not modelled: the stream no longer follows the format specification). -/
def DeflPrime (st : DeflState) (bits _value : Int) (rc : Int) (st' : DeflState) : Prop :=
  if bits < 0 ∨ bits > 16 then rc = Z.bufError ∧ st' = st
  else (rc = Z.bufError ∧ st' = st) ∨
    (rc = Z.ok ∧ st' = { st with precise := false, clean := false })

/-- `deflateSetHeader(strm, head)`: only for a gzip stream (`Z_STREAM_ERROR` otherwise). It must
come before the first `deflate`; later it is accepted but the data-level promises stop. -/
def DeflSetHeader (st : DeflState) (h : GzHead) (rc : Int) (st' : DeflState) : Prop :=
  if st.params.wrap ≠ .gzip then rc = Z.streamError ∧ st' = st
  else rc = Z.ok ∧
    (if st.started = true then st' = { st with hdr := some h, precise := false, clean := false }
     else st' = { st with hdr := some h })

end ZlibF.Spec.Api
