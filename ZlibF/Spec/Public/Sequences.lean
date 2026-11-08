import ZlibF.Spec.Public.Domains
import ZlibF.Spec.Public.GzTrace
import ZlibF.Spec.Api.Goals

namespace ZlibF.Spec.Public
open C Zlib.GzFs ZlibF.Spec

/-- An invariant is a conclusion about every actual history, never an assumed callee contract. -/
def StreamInvariant : StreamKind → Heap → ZStreamRef → Prop
  | .inflate, h, r => ∃ i z s, Zlib.Inflate.Spec.Good h r i z s ∧ Zlib.Inflate.Spec.DefAlloc z
  | .deflate, h, r => ∃ i z s, Zlib.Deflate.Spec.DGood h r i z s ∧ Zlib.Deflate.Spec.DefAlloc z

def StreamWriteRegions (h : Heap) (r : ZStreamRef) : Call → List Region
  | .inflate _ _ | .deflate _ _ | .deflateParams _ _ _ =>
      match r.get h with
      | none => []
      | some z => ⟨z.next_out, z.avail_out.toNat⟩ ::
          (match z.state with
           | some (.inflate i) => match h.istates i with
             | some s => HeaderRegions h s.head
             | none => []
           | _ => [])
  | .inflateGetDictionary _ p _ | .deflateGetDictionary _ p _ => [⟨p, 32768⟩]
  | _ => []

def StreamHeaderRecord (h : Heap) (r : ZStreamRef) (call : Call) (b : Nat) : Prop :=
  call = .inflateGetHeader (some r) (some (.tab b)) ∨
  (∃ z i s, r.get h = some z ∧ z.state = some (.inflate i) ∧ h.istates i = some s ∧
    s.head = some (.tab b) ∧ ∃ flush, call = .inflate (some r) flush)

/-- One more call must return from every permitted history, not merely preserve an invariant
when a caller assumes one. The ledger is exact, including failed calls and released windows. -/
def StreamSequenceSafety (kind : StreamKind) : Prop :=
  (∀ h r, StreamReachable kind h r → StreamInvariant kind h r) ∧
  (∀ h r call, StreamReachable kind h r → StreamOperation kind r call → StreamArguments h r call →
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      StreamInvariant kind after r ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b)) ∧
  (∀ h r, StreamReachable kind h r →
    ∃ rc after z, C.run ((match kind with
      | .inflate => Zlib.Inflate.inflateEnd
      | .deflate => Zlib.Deflate.deflateEnd) (some r)) h = .ok (rc, after) ∧
      (rc = Z_OK ∨ kind = .deflate ∧ rc = Z_DATA_ERROR) ∧
      r.get after = some z ∧ z.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r))

structure DataLog where
  input : List UInt8 := []
  output : List UInt8 := []
  dictionary : List UInt8 := []
  result : Int32 := Z_OK
  /-- False only after a raw dictionary replacement during an already-started data epoch.
  Such a continuation has multiple dictionary contexts, not one ordinary RFC stream. -/
  singleDictionary : Bool := true
  finished : Bool := false
  boundEligible : Bool := true

/-- Observations of actual calls. These equations neither assume accounting correctness nor
assume that output is valid compressed data. That is required by the sequence targets. -/
def DataStep (kind : StreamKind) (h after : Heap) (r : ZStreamRef)
    (flush rc : Int32) (input output : List UInt8) (used : Nat) : Prop :=
  ∃ z z', r.get h = some z ∧ r.get after = some z' ∧ StreamBuffers h r ∧ ActiveHeader h r ∧
    Bytes h z.next_in z.avail_in.toNat input ∧
    used = z.avail_in.toNat - z'.avail_in.toNat ∧
    Bytes after z.next_out (z.avail_out.toNat - z'.avail_out.toNat) output ∧
    C.run ((match kind with | .inflate => Zlib.Inflate.inflate | .deflate => Zlib.Deflate.deflate)
      (some r) flush) h = .ok (rc, after)

/-- A data epoch begins with the actual init. Rebinding buffers changes no private state.
Dictionary calls are recorded with their actual result; no earlier specification is assumed.
Reset starts another epoch; its safety and ownership are covered by StreamSequenceSafety. -/
inductive InflateDataTrace (wb : Int32) (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Inflate.inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) →
      InflateDataTrace wb r after {}
  | caller {h after log} : InflateDataTrace wb r h log → Rebuffer h after r →
      InflateDataTrace wb r after log
  | step {h after log flush rc input output used} : InflateDataTrace wb r h log →
      DataStep .inflate h after r flush rc input output used →
      InflateDataTrace wb r after
        { log with
          input := log.input ++ input.take used, output := log.output ++ output
          result := rc, finished := log.finished || rc == Z_STREAM_END }
  | dictionary {h after log p n bytes rc} : InflateDataTrace wb r h log →
      StreamArguments h r (.inflateSetDictionary (some r) p n) → Bytes h p n.toNat bytes →
      C.run (Zlib.Inflate.inflateSetDictionary (some r) p n) h = .ok (rc, after) →
      InflateDataTrace wb r after
        { log with
          dictionary := if rc = Z_OK then
            if wb.toInt < 0 then log.dictionary ++ bytes else bytes else log.dictionary
          singleDictionary := log.singleDictionary &&
            !(rc = Z_OK && wb.toInt < 0 && (log.input != [] || log.output != [])) }

inductive DeflateDataTrace (level method wb mem strategy : Int32) (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h = .ok (Z_OK, after) →
      DeflateDataTrace level method wb mem strategy r after {}
  | caller {h after log} : DeflateDataTrace level method wb mem strategy r h log → Rebuffer h after r →
      DeflateDataTrace level method wb mem strategy r after log
  | step {h after log flush rc input output used} : DeflateDataTrace level method wb mem strategy r h log →
      DataStep .deflate h after r flush rc input output used →
      DeflateDataTrace level method wb mem strategy r after
        { log with
          input := log.input ++ input.take used, output := log.output ++ output
          result := rc, finished := log.finished || rc == Z_STREAM_END
          boundEligible := log.boundEligible && flush == Z_FINISH }
  | dictionary {h after log p n bytes rc} : DeflateDataTrace level method wb mem strategy r h log →
      log.input = [] → log.output = [] →
      StreamArguments h r (.deflateSetDictionary (some r) p n) → Bytes h p n.toNat bytes →
      C.run (Zlib.Deflate.deflateSetDictionary (some r) p n) h = .ok (rc, after) →
      DeflateDataTrace level method wb mem strategy r after
        { log with dictionary := if rc = Z_OK then log.dictionary ++ bytes else log.dictionary }

def DecodesFor (p : Api.DeflParams) (dictionary compressed plain : List UInt8) : Prop :=
  match p.wrap with
  | .raw => Deflate.Decodes (dictionary.drop (dictionary.length - 2 ^ p.wbits)) compressed plain
  | .zlib => Zlib.Decodes dictionary compressed plain
  | .gzip => Gzip.Decodes compressed plain

/-- With the remainder of a valid stream and sufficient output room, a returning, non-failing
decoder finishes. A pending dictionary must have been supplied. No assumed model step occurs. -/
def InflateCompletes : Prop :=
  ∀ wb wrap bits r h log source decoded z i s flush,
    Api.inflWbits wb.toInt = some (wrap, bits) → InflateDataTrace wb r h log →
    log.singleDictionary = true → log.finished = false →
    Api.Layer.Decodes wrap bits log.dictionary source decoded → Api.FullWindow wrap bits source →
    log.input <+: source → Zlib.Inflate.Spec.Good h r i z s →
    s.mode ≠ BAD → s.mode ≠ MEM → s.mode ≠ SYNC → (s.mode = DICT → s.havedict ≠ 0) →
    StreamBuffers h r → ActiveHeader h r → NoAllocationFailure h →
    Bytes h z.next_in z.avail_in.toNat (source.drop log.input.length) →
    decoded.length ≤ log.output.length + z.avail_out.toNat →
    (flush = Z_NO_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FINISH) →
    ∃ after, C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (Z_STREAM_END, after) ∧
      Bytes after z.next_out (decoded.length - log.output.length) (decoded.drop log.output.length)

/-- The documented finish-only bound supplies enough space for completion. Eligibility is
computed by the actual trace constructors; a proof cannot choose or reset that flag. -/
def DeflateCompletes : Prop :=
  ∀ level method wb mem strategy p r h log input z i s,
    Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
    DeflateDataTrace level method wb mem strategy r h log →
    log.boundEligible = true → log.finished = false →
    Zlib.Deflate.Spec.DGood h r i z s → StreamBuffers h r → ActiveHeader h r →
    z.next_out ≠ .null →
    (s.status = FINISH_STATE → z.avail_in = 0) →
    Bytes h z.next_in z.avail_in.toNat input → 0 < z.avail_out.toNat →
    ({ Api.DeflState.fresh p with dict := some log.dictionary }).bound (log.input.length + input.length) ≤
      log.output.length + z.avail_out.toNat →
    ∃ after, C.run (Zlib.Deflate.deflate (some r) Z_FINISH) h = .ok (Z_STREAM_END, after)

/-- All legal public histories are safe and retain cleanup. For ordinary data epochs every
input/output split is covered, including allocation failures and dictionary handshakes.
Completion is stated against the independent byte-format relation. -/
def Goal.inflate_sequence : Prop :=
  StreamSequenceSafety .inflate ∧
  (∀ wb wrap bits r h log, Api.inflWbits wb.toInt = some (wrap, bits) →
    InflateDataTrace wb r h log →
    (log.singleDictionary = true → log.result = Z_STREAM_END →
      Api.Layer.Decodes wrap bits log.dictionary log.input log.output) ∧
    (∀ source decoded, Api.Layer.Decodes wrap bits log.dictionary source decoded →
      log.singleDictionary = true → Api.FullWindow wrap bits source → log.input <+: source →
      log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
      (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded))) ∧
  InflateCompletes

/-- All legal public histories are safe and retain cleanup. A finished ordinary data epoch
encodes exactly its accepted input, for every accepted parameter set and flush schedule. -/
def Goal.deflate_sequence : Prop :=
  StreamSequenceSafety .deflate ∧
  (∀ level method wb mem strategy p r h log,
    Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
    DeflateDataTrace level method wb mem strategy r h log →
    log.result = Z_STREAM_END → DecodesFor p log.dictionary log.output log.input) ∧
  DeflateCompletes

/-- Callback histories use the same caller-owned window across repeated decoding calls. -/
inductive BackReachable : Heap → ZStreamRef → Nat → BPtr → Nat → Prop
  | init {h after r version wb window} : InitDomain h r version →
      8 ≤ wb.toInt → wb.toInt ≤ 15 → Writable h window (2 ^ wb.toInt.toNat) → window ≠ .null →
      C.run (Zlib.Infback.inflateBackInit_ (some r) wb window version 112) h = .ok (Z_OK, after) →
      BackReachable after r h.nextBlk window (2 ^ wb.toInt.toNat)
  | caller {h after r i window n} : BackReachable h r i window n → Rebuffer h after r →
      SameBytePrefix h after window window n → BackReachable after r i window n
  | step {h after r i window n z input inDesc output outDesc first rc}
      (protocol : CallbackProtocol r i window n input inDesc output outDesc) :
      BackReachable h r i window n → r.get h = some z →
      (if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first) →
      Separate z.next_in first.length window n →
      protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first } →
      C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (rc, after) →
      BackReachable after r i window n

/-- Includes actual callback execution and raw-format delivery, re-use of the window, and
complete end cleanup. Callback memory and returning/finite-input obligations remain explicit. -/
def Goal.inflate_back_sequence : Prop :=
  Goal.inflateBack ∧
  (∀ h r i window n, BackReachable h r i window n →
    (∃ z s, BackValid h r i z s ∧ s.window = window ∧ s.wsize.toNat = n) ∧
    ∃ after z, C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_OK, after) ∧
      r.get after = some z ∧ z.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ b = i) ∧
      LiveChange h after (fun _ => False) (fun b => b = i))

/-- The gz lifecycle includes every admitted operation, external file growth and final close.
The per-entry read contracts express transparent/concatenated-member decoding and the
per-entry write contracts account for accepted bytes and seek zeros. -/
def Goal.gz_sequence : Prop :=
  (∀ h fs i, GzReachable h fs i → FileSystem fs ∧ ∃ s, GzValid h i s) ∧
  (∀ h fs i s call, GzReachable h fs i → h.gzstates i = some s →
    GzOperation i call → GzArguments h i s call →
    ∃ value fs' after s', call.execute fs h = .ok ((value, fs'), after) ∧
      GzValid after i s' ∧ FileSystem fs' ∧
      LiveChange h after
        (fun b => GzOwned after i s' b ∧ ¬ h.live b)
        (fun b => GzOwned h i s b ∧ ¬ GzOwned after i s' b)) ∧
  (∀ h fs i s, GzReachable h fs i → h.gzstates i = some s →
    ∃ rc fs' after, Zlib.Gzclose.gzclose (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      CloseEffects h after fs fs' i s) ∧
  Goal.gzread ∧ Goal.gzfread ∧ Goal.gzgetc ∧ Goal.gzgets ∧
  Goal.gzwrite ∧ Goal.gzfwrite ∧ Goal.gzflush ∧ Goal.gzclose ∧ GzWriterFormat

end ZlibF.Spec.Public
