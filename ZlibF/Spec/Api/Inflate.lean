import ZlibF.Spec.Api.Header

/-!
# API model: the inflate stream

A heap-free model of one `z_stream` used for `inflate`. The model state remembers the whole
history (all input consumed and all output delivered since the last reset), so that what a call
may do is stated against the format specification (`Layer.Decodes`), independent of how the
caller cuts the input and the output room. Every function is a *relation* between the state
before, the inputs of the call, and the results: zlib does not promise how much input a call
consumes, only the properties below. `docs/spec/api-lean.md` explains the choices.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

/-- The mode of an inflate stream as far as the caller can see it. `needDict` is after
`Z_NEED_DICT`, `done` after `Z_STREAM_END`, `bad` after `Z_DATA_ERROR`, `mem` after `Z_MEM_ERROR`, `syncing` after a failed `inflateSync` (`inflate` then
returns `Z_STREAM_ERROR` until the pattern is found or the stream is reset). -/
inductive IPhase where
  | running | needDict | done | bad | mem | syncing
  deriving DecidableEq, Repr

/-- The model of an initialised inflate stream.

* `seen`, `out`: all input consumed and all output delivered since init or reset
  (`total_in`, `total_out` are their lengths, plus what `Reset`/`Sync` keep: see `totalIn`).
* `dict`: the preset dictionary given to `inflateSetDictionary`.
* `adler`: the field `strm->adler`.
* `precise`: the data-level promises apply. It is cleared by operations after which `zlib.h`
  promises less (priming bits, `inflateSync`, switching the checksum off).
* `validate`: the checksum is checked (`inflateValidate`).
* `pre`: bits inserted by `inflatePrime`, read before `seen`.
* `syncHave`: how much of the pattern `00 00 FF FF` `inflateSync` has matched.
* `hdrReq`, `hdr`: `inflateGetHeader`'s request and the record that `inflate` filled. -/
structure InflState where
  wrap : Wrap
  wbits : Nat
  phase : IPhase
  seen : List UInt8
  out : List UInt8
  dict : Option (List UInt8)
  totalIn : Nat
  totalOut : Nat
  adler : UInt32
  precise : Bool
  validate : Bool
  pre : List Bool
  syncHave : Nat
  hdrReq : Option HdrReq
  hdr : Option GzHdrOut

/-- The state after a successful `inflateInit2` or `inflateReset2` with these parameters
(`inflateResetKeep`: `adler` is `wrap & 1`, the totals are 0). -/
def InflState.fresh (w : Wrap) (b : Nat) : InflState where
  wrap := w
  wbits := b
  phase := .running
  seen := []
  out := []
  dict := none
  totalIn := 0
  totalOut := 0
  adler := if w = .zlib ∨ w = .auto then 1 else 0
  precise := true
  validate := true
  pre := []
  syncHave := 0
  hdrReq := none
  hdr := none

/-- The data-level promises apply to this state. -/
def InflState.Exact (st : InflState) : Prop := st.precise = true ∧ st.validate = true

/-- The dictionary the decoder uses: the one supplied, else none. -/
def InflState.dictEff (st : InflState) : List UInt8 := st.dict.getD []

/-- Dictionaries still available to a legal continuation. A supplied dictionary is fixed.
A raw stream with no dictionary uses the empty dictionary. A wrapped stream that has not
received one may still request a preset dictionary: ignorance of that dictionary is not
evidence that the input is corrupt. Gzip ignores this argument in the format relation. -/
def InflState.PermitsDictionary (st : InflState) (dictionary : List UInt8) : Prop :=
  match st.dict with
  | some known => dictionary = known
  | none => st.wrap ≠ .raw ∨ dictionary = []

/-- The checksum that `strm->adler` holds for the output `out` of `seen`
(`A-adler-field`): Adler-32 for zlib, CRC-32 for gzip, nothing promised for raw. For `auto` the
first two bytes decide. -/
def checkValue (w : Wrap) (seen out : List UInt8) : Option UInt32 :=
  match w with
  | .raw => none
  | .zlib => some (adler32 out)
  | .gzip => some (crc32 out)
  | .auto => if seen.take 2 = [31, 139] then some (crc32 out) else some (adler32 out)

/-- `Consistent x out`: the bytes `x` begin a stream (or are one) that a decoder with this
configuration accepts, and `out` is a prefix of what that stream decodes to. -/
def Layer.Consistent (w : Wrap) (wbits : Nat) (dict x out : List UInt8) : Prop :=
  (x.length < hdrLag w ∧ out = []) ∨
    ∃ (t o : List UInt8) (n : Nat), x.length ≤ n ∧
      Layer.Decodes w wbits dict ((x ++ t).take n) o ∧ out <+: o

/-- Output determined by consumed bytes. For every complete stream compatible with the bytes
already read, the output is a prefix of its decoding. Compatibility includes a stream that ends
within the consumed bytes, so unread trailing data cannot select a different decoding. This is
a universal condition: one favourable future continuation is not enough. It does not constrain
which input the caller may supply, or assume a decoder implementation obeys this condition. -/
def Layer.Determined (w : Wrap) (wbits : Nat) (dict x out : List UInt8) : Prop :=
  ∀ (stream decoded : List UInt8), (x <+: stream ∨ stream <+: x) →
    Layer.Decodes w wbits dict stream decoded → out <+: decoded

/-- At least one still-permitted dictionary makes the consumed prefix and output consistent.
Before DICTID is complete this must not silently assume an empty preset dictionary. -/
def InflState.Consistent (st : InflState) (input output : List UInt8) : Prop :=
  ∃ dictionary, st.PermitsDictionary dictionary ∧
    Layer.Consistent st.wrap st.wbits dictionary input output

/-- The bytes already read determine the output for every dictionary still permitted by the
state. A dictionary not yet supplied cannot be chosen to justify speculative output. -/
def InflState.Determined (st : InflState) (input output : List UInt8) : Prop :=
  ∀ dictionary, st.PermitsDictionary dictionary →
    Layer.Determined st.wrap st.wbits dictionary input output

/-- What one call of `inflate` is given: the input bytes (`avail_in` of them), the room
`avail_out`, the flush value, and `badBuf` when `next_out` is null or `next_in` is null with
`avail_in ≠ 0` (the model has no null buffers). -/
structure InflCall where
  inp : List UInt8
  availOut : Nat
  flush : Flush
  badBuf : Bool

/-- What one call of `inflate` returns: the number of input bytes consumed, the bytes written, the
return code. -/
structure InflOut where
  consumed : Nat
  produced : List UInt8
  rc : Int

/-- The call made progress: it consumed input or produced output. -/
def InflOut.Progress (o : InflOut) : Prop := 0 < o.consumed ∨ o.produced ≠ []

/-- The record that `inflateGetHeader` asked for, after the bytes `seen'` were read: filled with the
header if it is complete in `seen'`, else unchanged. -/
def InflHdrClause (st : InflState) (seen' : List UInt8) (st' : InflState) : Prop :=
  ∀ req, st.hdrReq = some req → (∃ h, st'.hdr = some h ∧ HeaderRead req seen' h) ∨
    (¬ ∃ h, HeaderRead req seen' h) ∧ st'.hdr = st.hdr

/-- `inflate(strm, flush)` on a running stream, the outcomes other than `Z_MEM_ERROR`
(`A-inflate-progress`, `A-inflate-err-data`, `zlib.h` `inflate`). The clauses:

1. *Frame.* It consumes a prefix of the input and writes at most `avail_out` bytes; the history
   and the totals grow by exactly that; everything else keeps its value, except `adler` and `hdr`.
2. *Return codes.* `Z_OK` needs progress and no `Z_FINISH`; `Z_BUF_ERROR` is no progress, or
   `Z_FINISH` that did not finish; the other codes change the mode.
3. *Soundness* (needs `Exact`). What was written is compatible with a valid continuation
   (`Layer.Consistent`) and is determined by the consumed bytes (`Layer.Determined`), so it must
   be a prefix of the decoding of every compatible complete stream. `Z_STREAM_END` only for a complete
   stream with all its output written; `Z_DATA_ERROR` only if the input consumed is not viable
   (or the window is smaller than 32 KiB: `FullWindow`).
4. *Stopping.* With input left over, the call stopped because the output is full, or the stream
   ended or failed, or the flush value asked for a block boundary.
5. *Liveness* (needs `Exact`, flush `Z_NO_FLUSH`, `Z_SYNC_FLUSH` or `Z_FINISH`, a full window).
   The call ends the stream if the stream ends within the input and the output fits; it
   reports a data error that shows at least `detectLag` bytes before the end of the input if
   there is room left; it returns `Z_NEED_DICT` when the header asks for a dictionary. (In every
   case `InflRunMem` is the other allowed outcome of such a call.)
6. *Checksum field.* After the call `adler` is the checksum of the output so far
   (`checkValue`), once there is output or the stream ended. -/
def InflRunOk (st : InflState) (c : InflCall) (o : InflOut) (st' : InflState) : Prop :=
  let all := st.seen ++ c.inp
  let seen' := st.seen ++ c.inp.take o.consumed
  let out' := st.out ++ o.produced
  -- 1. frame
  o.consumed ≤ c.inp.length ∧ o.produced.length ≤ c.availOut ∧
  st'.seen = seen' ∧ st'.out = out' ∧
  st'.totalIn = st.totalIn + o.consumed ∧ st'.totalOut = st.totalOut + o.produced.length ∧
  st'.wrap = st.wrap ∧ st'.wbits = st.wbits ∧ st'.dict = st.dict ∧ st'.precise = st.precise ∧
  st'.validate = st.validate ∧ st'.pre = st.pre ∧ st'.syncHave = st.syncHave ∧
  st'.hdrReq = st.hdrReq ∧
  -- 2. return codes
  (o.rc = Z.ok ∨ o.rc = Z.streamEnd ∨ o.rc = Z.needDict ∨ o.rc = Z.dataError ∨
    o.rc = Z.bufError) ∧
  (o.rc = Z.ok → o.Progress ∧ c.flush ≠ .finish ∧ st'.phase = .running) ∧
  (o.rc = Z.bufError → (¬ o.Progress ∨ c.flush = .finish) ∧ st'.phase = .running) ∧
  (o.rc = Z.streamEnd → st'.phase = .done) ∧
  (o.rc = Z.dataError → st'.phase = .bad) ∧
  (o.rc = Z.needDict → st'.phase = .needDict ∧ o.produced = [] ∧ st.dict = none ∧
    seen'.length = 6 ∧ HdrNeedsDict st.wrap st.wbits seen') ∧
  -- 3. soundness
  (st.Exact → (o.rc = Z.ok ∨ o.rc = Z.bufError) →
    st.Consistent seen' out') ∧
  (st.Exact → o.rc = Z.streamEnd → Layer.Decodes st.wrap st.wbits st.dictEff seen' out') ∧
  (st.Exact → o.rc = Z.dataError → FullWindow st.wrap st.wbits all →
    ∀ dictionary, st.PermitsDictionary dictionary →
      ¬ Layer.Viable st.wrap st.wbits dictionary seen') ∧
  -- 4. stopping
  (o.consumed < c.inp.length →
    o.produced.length = c.availOut ∨ o.rc = Z.streamEnd ∨ o.rc = Z.dataError ∨
    o.rc = Z.needDict ∨ c.flush = .block ∨ c.flush = .trees) ∧
  -- 5. liveness
  (st.Exact → (c.flush = .noFlush ∨ c.flush = .syncFlush ∨ c.flush = .finish) →
    FullWindow st.wrap st.wbits all →
    (st.dict = none → ¬ HdrNeedsDict st.wrap st.wbits all) →
    (∃ (n : Nat) (o' : List UInt8), st.seen.length ≤ n ∧ n ≤ all.length ∧
        Layer.Decodes st.wrap st.wbits st.dictEff (all.take n) o' ∧ st.out <+: o' ∧
        o'.length ≤ st.out.length + c.availOut) →
    o.rc = Z.streamEnd) ∧
  (st.Exact → (c.flush = .noFlush ∨ c.flush = .syncFlush ∨ c.flush = .finish) →
    (st.dict = none → ¬ HdrNeedsDict st.wrap st.wbits all) →
    Layer.Detectable st.wrap st.wbits st.dictEff all → o.produced.length < c.availOut →
    o.rc = Z.dataError) ∧
  (st.dict = none → st.seen.length < 6 → 6 ≤ all.length → HdrNeedsDict st.wrap st.wbits all →
    o.rc = Z.needDict ∧ o.consumed = 6 - st.seen.length) ∧
  -- 6. checksum field
  (st.Exact → (checkValue st.wrap seen' out').isSome → (out' ≠ [] ∨ o.rc = Z.streamEnd) →
    some st'.adler = checkValue st.wrap seen' out') ∧
  -- Consistency with one possible future does not permit guessing output from unread input.
  (st.Exact → (o.rc = Z.ok ∨ o.rc = Z.bufError) →
    st.Determined seen' out') ∧
  -- header record
  InflHdrClause st seen' st'

/-- `inflate(strm, flush)` on a running stream, the outcome `Z_MEM_ERROR` (`inflate.c`, `inf_leave`:
`updatewindow` fails to allocate the window, `mode = MEM`, and the function returns *before* it
updates `total_in`, `total_out` and `adler`). The call has read input and written output
(`consumed`, `produced`, as `avail_in` and `avail_out` show; `produced` is not empty, since the window
is allocated only when output was written), but the totals and `adler` keep their old values.
The stream is in the state `mem`: every later `inflate` returns `Z_MEM_ERROR`, and only `inflateEnd`,
`inflateReset` and `inflateReset2` are meaningful. The data written is correct (a prefix of the
decoding). Checked against the real library with a window allocation that fails. -/
def InflRunMem (st : InflState) (c : InflCall) (o : InflOut) (st' : InflState) : Prop :=
  let seen' := st.seen ++ c.inp.take o.consumed
  let out' := st.out ++ o.produced
  o.rc = Z.memError ∧ o.consumed ≤ c.inp.length ∧ o.produced.length ≤ c.availOut ∧ o.produced ≠ [] ∧
  st'.phase = .mem ∧ st'.seen = seen' ∧ st'.out = out' ∧
  st'.totalIn = st.totalIn ∧ st'.totalOut = st.totalOut ∧ st'.adler = st.adler ∧
  st'.wrap = st.wrap ∧ st'.wbits = st.wbits ∧ st'.dict = st.dict ∧ st'.precise = st.precise ∧
  st'.validate = st.validate ∧ st'.pre = st.pre ∧ st'.syncHave = st.syncHave ∧
  st'.hdrReq = st.hdrReq ∧
  (st.Exact → st.Consistent seen' out') ∧
  (st.Exact → st.Determined seen' out') ∧
  InflHdrClause st seen' st'

/-- `inflate(strm, flush)` on a running stream: one of the two outcomes above. -/
def InflRun (st : InflState) (c : InflCall) (o : InflOut) (st' : InflState) : Prop :=
  InflRunOk st c o st' ∨ InflRunMem st c o st'

/-- `inflate(strm, flush)` for any stream state (`zlib.h`; `inflate.c` start of `inflate` and the
modes `DONE`, `BAD`, `MEM`, `DICT`):
a bad buffer is `Z_STREAM_ERROR`; a finished stream keeps returning `Z_STREAM_END`, a failed one
`Z_DATA_ERROR`, one out of memory `Z_MEM_ERROR`, one waiting for a dictionary `Z_NEED_DICT`,
one in the sync search `Z_STREAM_ERROR`, all without consuming or producing anything. -/
def InflStep (st : InflState) (c : InflCall) (o : InflOut) (st' : InflState) : Prop :=
  (c.badBuf = true → o.rc = Z.streamError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st) ∧
  (c.badBuf = false →
    match st.phase with
    | .running => InflRun st c o st'
    | .done => o.rc = Z.streamEnd ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st
    | .bad => o.rc = Z.dataError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st
    | .mem => o.rc = Z.memError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st
    | .needDict => o.rc = Z.needDict ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st
    | .syncing => o.rc = Z.streamError ∧ o.consumed = 0 ∧ o.produced = [] ∧ st' = st)

/-! ## The other inflate functions

Each is a relation `rc`, `st'` for the state before `st`; a call that fails leaves the state
unchanged unless said otherwise. -/

/-- `inflateInit2_` / `inflateInit_` (`windowBits` 15): the result code and the new stream.
`versionOK` says that the version string and the structure size are the library's. `Z_MEM_ERROR`
is the failure of an allocation; then there is no stream. -/
def InflInit (wb : Int) (versionOK : Bool) (rc : Int) (r : Option InflState) : Prop :=
  if versionOK = false then rc = Z.versionError ∧ r = none
  else match inflWbits wb with
    | none => rc = Z.streamError ∧ r = none
    | some (w, b) => (rc = Z.ok ∧ r = some (InflState.fresh w b)) ∨ (rc = Z.memError ∧ r = none)

/-- `inflateReset2(strm, windowBits)`: forgets all data (history, dictionary, header request);
`total_in`, `total_out` are 0. A bad `windowBits` is `Z_STREAM_ERROR` and changes nothing.
`inflateReset` is `windowBits` of the stream (`InflReset`). -/
def InflReset2 (st : InflState) (wb : Int) (rc : Int) (st' : InflState) : Prop :=
  match inflWbits wb with
  | none => rc = Z.streamError ∧ st' = st
  | some (w, b) => rc = Z.ok ∧ st' = InflState.fresh w b

/-- `inflateReset(strm)`: as `InflReset2` with the configuration the stream was last given. -/
def InflReset (st : InflState) (rc : Int) (st' : InflState) : Prop :=
  rc = Z.ok ∧ st' = InflState.fresh st.wrap st.wbits

/-- `inflateEnd(strm)`: succeeds and ends the stream (the model has no further state). -/
def InflEnd (_st : InflState) (rc : Int) : Prop := rc = Z.ok

/-- `inflatePrime(strm, bits, value)`: `bits = 0` does nothing; `bits < 0` clears the bit buffer;
`bits > 16`, or more than 32 bits in the buffer, is `Z_STREAM_ERROR`. Otherwise the `bits` low
bits of `value` are put in front of the pending input, and the data-level promises stop
(`precise := false`). The bits in the buffer are known exactly only while no input has been
consumed; afterwards `Z_STREAM_ERROR` is allowed when the buffer may be full
(`zlib.h`: "inflatePrime"). -/
def InflPrime (st : InflState) (bits value : Int) (rc : Int) (st' : InflState) : Prop :=
  if bits = 0 then rc = Z.ok ∧ st' = st
  else if bits < 0 then rc = Z.ok ∧ st' = { st with pre := [] }
  else if bits > 16 then rc = Z.streamError ∧ st' = st
  else if st.seen = [] ∧ st.pre.length + bits.toNat > 32 then rc = Z.streamError ∧ st' = st
  else (rc = Z.ok ∧
      st' = { st with pre := st.pre ++ (List.range bits.toNat).map (fun i => (value % (2 ^ bits.toNat : Int)).toNat.testBit i),
                      precise := false }) ∨
    (st.seen ≠ [] ∧ rc = Z.streamError ∧ st' = st)

/-- `inflateSetDictionary(strm, dict, len)`. A stream with a zlib header accepts it only after
`Z_NEED_DICT`, and checks its Adler-32 against the `DICTID` read from the header
(`Z_DATA_ERROR` if different). A raw stream accepts it before any input is consumed; zlib also
accepts it later (it then amends the window), which this model leaves out (`seen = []`). -/
def InflSetDict (st : InflState) (d : List UInt8) (rc : Int) (st' : InflState) : Prop :=
  match st.wrap with
  | .raw => st.seen = [] ∧ ((rc = Z.ok ∧ st' = { st with dict := some d }) ∨
      (rc = Z.memError ∧ st' = { st with phase := .mem }))
  | _ =>
    if st.phase = .needDict then
      if st.seen.drop 2 = be32 (adler32 d).toNat then
        (rc = Z.ok ∧ st' = { st with dict := some d, phase := .running }) ∨
        (rc = Z.memError ∧ st' = { st with phase := .mem })
      else rc = Z.dataError ∧ st' = st
    else rc = Z.streamError ∧ st' = st

/-- The window size in bytes, when the configuration fixes it (`wbits ≠ 0`). -/
def InflState.winSize (st : InflState) : Nat := 2 ^ st.wbits

/-- `inflateGetDictionary(strm, buf, &len)`: `Z_OK`. While the stream is running with a fixed window
size, the dictionary returned is a suffix of the dictionary and the output so far, at most the window.
(It is exactly the last `min(window, history)` bytes unless the last call was `Z_FINISH` and ended
inside the trailer, when the window is not updated; the model does not track that.) -/
def InflGetDict (st : InflState) (buf : List UInt8) (rc : Int) : Prop :=
  rc = Z.ok ∧ (st.phase = .running → st.wbits ≠ 0 →
    buf <:+ (st.dictEff ++ st.out) ∧ buf.length ≤ st.winSize)

/-- One byte of `syncsearch` (`inflate.c`): `got` bytes of the pattern `00 00 FF FF` are matched. -/
def syncStep (got : Nat) (b : UInt8) : Nat :=
  if b = (if got < 2 then 0 else 255) then got + 1 else if b ≠ 0 then 0 else 4 - got

/-- `syncsearch(&have, buf, len)`: the new `have` and the number of bytes looked at. -/
def syncSearch : Nat → List UInt8 → Nat × Nat
  | got, [] => (got, 0)
  | got, b :: r =>
    if got < 4 then
      let p := syncSearch (syncStep got b) r
      (p.1, p.2 + 1)
    else (got, 0)

/-- `inflateSync(strm)` on the input `inp` (`avail_in` bytes; the bit buffer is assumed to hold
less than a byte): `Z_BUF_ERROR` if there is no input. Otherwise the input is searched with
`syncSearch`, starting from the partial match of an earlier failed call. If the pattern is
found, `Z_OK`, the input up to and including it is consumed, the stream is reset as by
`inflateReset` but the totals are kept, and the data-level promises stop. If not, `Z_DATA_ERROR`,
all the input is consumed and the stream is in the sync search (`syncing`). -/
def InflSync (st : InflState) (inp : List UInt8) (consumed : Nat) (rc : Int) (st' : InflState) :
    Prop :=
  if inp = [] then rc = Z.bufError ∧ consumed = 0 ∧ st' = st
  else
    let r := syncSearch (if st.phase = .syncing then st.syncHave else 0) inp
    consumed = r.2 ∧
    (if r.1 = 4 then
      rc = Z.ok ∧ st' = { InflState.fresh st.wrap st.wbits with
                totalIn := st.totalIn + consumed, totalOut := st.totalOut, precise := false,
                adler := st.adler }
    else
      rc = Z.dataError ∧
        st' = { st with phase := .syncing, syncHave := r.1, totalIn := st.totalIn + consumed })

/-- `inflateSyncPoint(strm)`: 0 or 1, never an error for a valid stream. The model promises that
a stream that has consumed nothing, has ended or has failed is not at a sync point. -/
def InflSyncPoint (st : InflState) (r : Int) : Prop :=
  (r = 0 ∨ r = 1) ∧ ((st.seen = [] ∨ st.phase ≠ .running) → r = 0)

/-- `inflateCopy(dest, source)`: `dest` becomes an independent copy of the same model state
(`C6`); `Z_MEM_ERROR` leaves `dest` without a state. -/
def InflCopy (st : InflState) (rc : Int) (dest : Option InflState) : Prop :=
  (rc = Z.ok ∧ dest = some st) ∨ (rc = Z.memError ∧ dest = none)

/-- `inflateGetHeader(strm, head)`: only for a gzip or automatic stream (`Z_STREAM_ERROR`
otherwise). It must be called before the first `inflate`; the model requires `seen = []`.
`head->done` is 0 until `inflate` completes the header. -/
def InflGetHeader (st : InflState) (req : HdrReq) (rc : Int) (st' : InflState) : Prop :=
  if st.wrap = .raw ∨ st.wrap = .zlib then rc = Z.streamError ∧ st' = st
  else st.seen = [] ∧ rc = Z.ok ∧ st' = { st with hdrReq := some req, hdr := none }

/-- `inflateUndermine(strm, subvert)`: in the default build (without
`INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR`) it returns `Z_DATA_ERROR` and changes nothing. -/
def InflUndermine (st : InflState) (_subvert : Int) (rc : Int) (st' : InflState) : Prop :=
  rc = Z.dataError ∧ st' = st

/-- `inflateValidate(strm, check)`: switches checking of the trailer on or off; the data-level
promises hold only while it is on and was on from the start. -/
def InflValidate (st : InflState) (check : Int) (rc : Int) (st' : InflState) : Prop :=
  rc = Z.ok ∧ st' = { st with validate := decide (check ≠ 0) , precise := st.precise && st.validate }

/-- `inflateMark(strm)`: upper 16 bits and lower 16 bits as in `zlib.h`. Note that `-65536` is
both the answer for an inconsistent stream and "upper -1, lower 0" (outside a block). The model
promises only that a stream that has consumed nothing is outside a block. -/
def InflMark (st : InflState) (v : Int) : Prop :=
  (st.seen = [] → st.pre = [] → v = -65536)

/-! ## `inflateBack`: callbacks as a function parameter -/

/-- The callbacks of `inflateBack`: the buffer returned by the `k`-th call of `in` (`[]` means "no
input": `inflateBack` then returns `Z_BUF_ERROR`), and whether the `k`-th call of `out` fails. -/
structure BackCallbacks where
  input : Nat → List UInt8
  outFails : Nat → Bool

/-- What `inflateBack` did: the buffers passed to `out` in order, the return code, the unused
part of the last input buffer, and whether `strm->next_in` is `Z_NULL` (set when `in` returned
nothing). -/
structure BackResult where
  chunks : List (List UInt8)
  rc : Int
  unused : List UInt8
  nextInNull : Bool

/-- `inflateBack(strm, in, in_desc, out, out_desc)` for a stream initialised with `windowBits`
`wb` (8 to 15), with the first input `first` (`strm->next_in`, `avail_in`) and the callbacks
`cb` (`zlib.h`). The stream read is a raw deflate stream. The consumed input is `first` followed by
whole buffers of `cb.input 0, cb.input 1, ...` minus `unused` at the end.

* `Z_OK` is never returned (the return code is one of the three below).
* `Z_STREAM_END`: the consumed input is exactly one raw deflate stream; the buffers given to `out`
  concatenate to its decoding; each buffer has at most `2^wb` bytes.
* `Z_DATA_ERROR`: the consumed input is not viable (or the window is smaller than 32 KiB, where
  a valid stream with a far distance may be refused).
* `Z_BUF_ERROR`: `in` returned nothing (and `next_in` is null), or `out` failed.

In all cases the buffers passed to `out` (the last one may be the one that failed) concatenate to
a prefix of what the input consumed so far decodes to (soundness). -/
def InflBack (wb : Nat) (first : List UInt8) (cb : BackCallbacks) (r : BackResult) : Prop :=
  8 ≤ wb ∧ wb ≤ 15 ∧
  (r.rc = Z.streamEnd ∨ r.rc = Z.dataError ∨ r.rc = Z.bufError) ∧
  (∀ ch, ch ∈ r.chunks → ch.length ≤ 2 ^ wb) ∧
  ∃ (k : Nat) (consumed : List UInt8),
    consumed ++ r.unused = first ++ ((List.range k).map cb.input).flatten ∧
    r.unused.length ≤ (if k = 0 then first else cb.input (k - 1)).length ∧
    (r.rc = Z.streamEnd → Deflate.Decodes [] consumed r.chunks.flatten) ∧
    (r.rc = Z.dataError → wb = 15 → ¬ Layer.Viable .raw wb [] consumed) ∧
    (r.rc = Z.bufError →
      (r.nextInNull = true ∧ cb.input k = []) ∨ (r.nextInNull = false ∧ ∃ i, cb.outFails i = true)) ∧
    ∃ m, m ≤ consumed.length ∧ Layer.Consistent .raw wb [] (consumed.take m) r.chunks.flatten

end ZlibF.Spec.Api
