import ZlibF.Spec.Public.Sequences
import ZlibF.Spec.Public.Streams
import ZlibF.Spec.Public.Utilities
import ZlibF.Proof.«inflate.c.meaning»

/-!
# inflate.c: the decoder facts that completion and the decompression utilities use

`InflateCompletes` and the four `uncompress*` goals are compositions. Besides
`Goal.inflate`, the safety part of `Goal.inflate_sequence` and its two format
clauses, they need seven facts about the actual decoder that those goals do not
state. Each is a statement about the translated `inflate` over the actual
protocol histories of `Spec/Public/Sequences.lean`; none is a model step.

* `TraceEvidence`: after every admitted history the delivered output is
  justified and determined by the consumed input, also when the input is not
  valid. The decompression utilities report output on a data error.
* `ConsumesWithinStream`: a call given input comparable with a valid stream
  never reads past the end of the stream, and reading its last byte ends the
  stream (or fails to allocate the window).
* `StopsWhenBlocked`: a call that returns `Z_OK` or `Z_BUF_ERROR` with input
  left stopped because the output is full and more output is due.
* `NeedDictionaryCall`: `Z_NEED_DICT` comes only from a zlib header that asks
  for a dictionary, with no dictionary installed and no output.
* `MemErrorAllocates`: outside the `MEM` mode, a `Z_MEM_ERROR` return that
  leaves the decoder in `MEM` comes only from a failed allocation.
* `InflateKeepsObjectSize`: a call keeps the platform object-size limit, which
  the history relation asks for before the next call.
* `CallKeepsControl`: a call never enters `SYNC`, enters `MEM` only with
  `Z_MEM_ERROR`, keeps the header record and its own blocks, and owns no block that
  was live and not its own before.

These are proof obligations of the decoder's format meaning (`ParseMeaning`,
`inflate.c.meaning`), not assumptions of a public goal. `MeaningStep`, the
open `meaning_step` of the inflate skeleton, is the step of that meaning over
one call. Theorems on `dev` take the open ones as explicit hypotheses until
they are proved.
-/

namespace Zlib.Inflate.Proofs
open C ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The output of every admitted single-dictionary history is justified by a
checked bit prefix of the consumed input and determined by the consumed input,
for the dictionary actually installed. This holds for every input, valid or not.
A zlib dictionary with a configured window is excluded: zlib then keeps more of
the dictionary than the window of the header, which `Zlib.Decodes` keeps, and
can write bytes no valid stream decodes to
(`tests/verification/regressions/inflate-dictionary-header-window.lean`). -/
def TraceEvidence : Prop :=
  ∀ (wb : Int32) wrap bits r h log pending,
    Api.inflWbits wb.toInt = some (wrap, bits) →
    InflateProtocolTrace wb r h log pending → log.singleDictionary = true →
    (log.dictionary = [] ∨ wrap = .raw ∨ bits = 0) →
    Api.Layer.OutputEvidence wrap bits (fun d => d = log.dictionary) log.input log.output ∧
    Api.Layer.Determined wrap bits log.dictionary log.input log.output

/-- A call whose offered input is comparable with a valid stream consumes only
bytes of that stream. A call that consumes its last byte returns `Z_STREAM_END`,
or `Z_MEM_ERROR` when the window allocation at the end of the call fails, if the
stream has a trailer (not raw data) or the output has room for the rest of the
decoding and the call does not stop at a block boundary (`Z_BLOCK`, `Z_TREES`).
The last byte of raw data can hold the end of a literal and the whole end-of-block
code: without room inflate reads it and stops before the literal
(`tests/goals/inflate-meaning/raw-last-byte-no-room.c`). The heap of the call is
within the object-size limit, as the history records. -/
def ConsumesWithinStream : Prop :=
  ∀ (wb : Int32) wrap bits r h after log pending (flush rc : Int32) input output used
    source decoded,
    Api.inflWbits wb.toInt = some (wrap, bits) →
    InflateProtocolTrace wb r h log pending → log.singleDictionary = true →
    ZlibF.PlatformMemory.ByteObjectsFit h →
    Api.Layer.Decodes wrap bits log.dictionary source decoded → Api.FullWindow wrap bits source →
    log.input <+: source → (log.input ++ input <+: source ∨ source <+: log.input ++ input) →
    DataStep .inflate h after r flush rc input output used →
    log.input ++ input.take used <+: source ∧
      (log.input ++ input.take used = source →
        (wrap ≠ .raw ∨ ((∀ z, r.get h = some z → decoded.length ≤ log.output.length + z.avail_out.toNat) ∧
          flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)) →
        rc = Z_STREAM_END ∨ rc = Z_MEM_ERROR)

/-- On a valid stream, a call with flush `Z_NO_FLUSH`, `Z_SYNC_FLUSH` or `Z_FINISH`
that returns `Z_OK` or `Z_BUF_ERROR` and leaves input unread has filled the output,
and the stream still has output to deliver. The heap of the call is within the
object-size limit, as the history records. -/
def StopsWhenBlocked : Prop :=
  ∀ (wb : Int32) wrap bits r h after log pending (flush rc : Int32) input output used
    source decoded z',
    Api.inflWbits wb.toInt = some (wrap, bits) →
    InflateProtocolTrace wb r h log pending → log.singleDictionary = true →
    ZlibF.PlatformMemory.ByteObjectsFit h →
    Api.Layer.Decodes wrap bits log.dictionary source decoded → Api.FullWindow wrap bits source →
    log.input <+: source → (log.input ++ input <+: source ∨ source <+: log.input ++ input) →
    DataStep .inflate h after r flush rc input output used →
    (flush = Z_NO_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FINISH) →
    (rc = Z_OK ∨ rc = Z_BUF_ERROR) → r.get after = some z' → z'.avail_in ≠ 0 →
    z'.avail_out = 0 ∧ log.output.length + output.length < decoded.length

/-- `Z_NEED_DICT` is returned in `DICT` mode with no dictionary installed, before
any output, for a zlib header (zlib or detected wrapper) that sets `FDICT` and
whose window fits. Stated for a single-dictionary history (every non-raw history
is one) and a heap within the object-size limit (as the history records before
each call). -/
def NeedDictionaryCall : Prop :=
  ∀ (wb : Int32) wrap bits r h after log pending (flush rc : Int32) input output used i z s,
    Api.inflWbits wb.toInt = some (wrap, bits) →
    InflateProtocolTrace wb r h log pending → log.singleDictionary = true →
    ZlibF.PlatformMemory.ByteObjectsFit h → Zlib.Inflate.Spec.Good h r i z s →
    DataStep .inflate h after r flush rc input output used → rc = Z_NEED_DICT →
    s.havedict = 0 ∧ output = [] ∧ (wrap = .zlib ∨ wrap = .auto) ∧
    (∃ cmf flg tail, log.input ++ input.take used = cmf :: flg :: tail ∧
      Zlib.HeaderOK cmf flg ∧ flg.toNat / 32 % 2 = 1 ∧
      Api.ZlibFits bits (log.input ++ input.take used)) ∧
    ∃ z' s', Zlib.Inflate.Spec.Good after r i z' s' ∧ s'.mode = DICT ∧ s'.havedict = 0

/-- Outside the `MEM` mode, a call that returns `Z_MEM_ERROR` and leaves the
decoder in `MEM` (as `Goal.inflate` states) reports an actual allocator failure
during the call. -/
def MemErrorAllocates : Prop :=
  ∀ h r i z s (flush : Int32) after z' s',
    Zlib.Inflate.Spec.Good h r i z s → s.mode ≠ MEM →
    C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (Z_MEM_ERROR, after) →
    Zlib.Inflate.Spec.Good after r i z' s' → s'.mode = MEM →
    AllocationFailed h after

/-- A call keeps the object-size limit: it allocates at most a window of
`2^wbits` bytes and resizes no object. `StreamReachable` asks for the limit
before every call, so a run of calls with no caller edit in between needs it. -/
def InflateKeepsObjectSize : Prop :=
  ∀ h r i z s (flush rc : Int32) after,
    StreamReachable .inflate h r → Zlib.Inflate.Spec.Good h r i z s →
    ZlibF.PlatformMemory.ByteObjectsFit h → StreamBuffers h r → ActiveHeader h r →
    C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) →
    ZlibF.PlatformMemory.ByteObjectsFit after

/-- An `inflate` call never enters `SYNC` (only `inflateSync` sets it), enters `MEM`
only when it returns `Z_MEM_ERROR` (a decoder already in `MEM` stays there, even on a
refused call), never changes the attached header record, keeps
the blocks it owns, and owns afterwards only blocks it owned before or that were not
live before (a new window). -/
def CallKeepsControl : Prop :=
  ∀ h r i z s (flush rc : Int32) after z' s',
    StreamReachable .inflate h r → Zlib.Inflate.Spec.Good h r i z s →
    C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) →
    Zlib.Inflate.Spec.Good after r i z' s' →
    (s.mode ≠ SYNC → s'.mode ≠ SYNC) ∧ (s'.mode = MEM → rc = Z_MEM_ERROR ∨ s.mode = MEM) ∧ s'.head = s.head ∧
    (∀ b, InflateOwned i s b → InflateOwned i s' b) ∧
    ∀ b, InflateOwned i s' b → InflateOwned i s b ∨ ¬ h.live b

/-- `meaning_step` of the inflate skeleton: one `inflate` call of a protocol
history keeps the format meaning, with the dictionary request token. The call
runs on a heap within the object-size limit, as the history records. -/
def MeaningStep : Prop :=
  ∀ (wb : Int32) (r : ZStreamRef) (h after : Heap) (log : DataLog) (pending : Bool)
    (flush rc : Int32) (input output : List UInt8) (used : Nat),
    ParseMeaning wb r h log pending → ZlibF.PlatformMemory.ByteObjectsFit h →
    DataStep .inflate h after r flush rc input output used →
    ParseMeaning wb r after
      { log with
        input := log.input ++ input.take used, output := log.output ++ output
        result := rc, finished := log.finished || rc == Z_STREAM_END }
      (rc == Z_NEED_DICT)

/-- The output delivered so far is the output of a stage that the format grammar
reaches on a prefix of the consumed input bits (heap-free; `TraceEvidence` follows
from it, `inflate.c.completes-evidence`). -/
def EvidenceInv (wb : Int32) (log : DataLog) : Prop :=
  log.singleDictionary = true →
    ∃ wrap bits consumed stage, Api.inflWbits wb.toInt = some (wrap, bits) ∧
      consumed <+: bytesToBits log.input ∧
      WrapParsed wrap bits log.dictionary consumed stage ∧ log.output = stage.output

/-- A call of a protocol history that leaves the decoder in `BAD` or `MEM` keeps
`EvidenceInv`: the output it delivered before the error is the output of a stage
reached on the bits it consumed. For every other call `EvidenceInv` follows from
`ParseMeaning` after the call. This is part of the functional correctness of one
call (the side of `meaning_step`), open. -/
def StepEvidence : Prop :=
  ∀ (wb : Int32) (r : ZStreamRef) (h after : Heap) (log : DataLog) (pending : Bool)
    (flush rc : Int32) (input output : List UInt8) (used i : Nat) (z : ZStream) (s : InflateState),
    ParseMeaning wb r h log pending → ZlibF.PlatformMemory.ByteObjectsFit h →
    DataStep .inflate h after r flush rc input output used →
    Zlib.Inflate.Spec.Good after r i z s → (s.mode = BAD ∨ s.mode = MEM) →
    EvidenceInv wb log →
    EvidenceInv wb
      { log with
        input := log.input ++ input.take used, output := log.output ++ output
        result := rc, finished := log.finished || rc == Z_STREAM_END }

/-- The format clauses of `Goal.inflate_sequence` (`inflate_sequence_format` on the
skeleton branch). -/
def SequenceFormat : Prop :=
  ∀ (wb : Int32) wrap bits r h log, Api.inflWbits wb.toInt = some (wrap, bits) →
    AllowedInflateProtocol wb r h log →
    (log.singleDictionary = true → log.result = Z_STREAM_END →
      Api.Layer.InflateAccepted wrap bits log.dictionary log.input log.output) ∧
    (∀ source decoded, Api.Layer.Decodes wrap bits log.dictionary source decoded →
      log.singleDictionary = true → Api.FullWindow wrap bits source → log.input <+: source →
      log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
      (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded))

/-- Everything the compositions of batch 3 take from the decoder proofs: the
per-call goal, sequence safety, the step of the format meaning, its evidence
part for a call that fails, and two of the facts above. Each field is a
statement about the translated code that another lemma proves.
`MemErrorAllocates`, `InflateKeepsObjectSize` and `CallKeepsControl` are theorems
(`inflate.c.completes-percall`), and so are `SequenceFormat` (`sequence_format`,
from `MeaningStep`), `NeedDictionaryCall` (`need_dictionary_call`, from
`Goal.inflate` and `MeaningStep`) and `TraceEvidence` (`trace_evidence`, from
`MeaningStep` and `StepEvidence`). -/
structure DecoderFacts : Prop where
  call : ZlibF.Spec.Public.Goal.inflate
  safety : StreamSequenceSafety .inflate
  step : MeaningStep
  stepEvidence : StepEvidence
  within : ConsumesWithinStream
  stops : StopsWhenBlocked

end Zlib.Inflate.Proofs
