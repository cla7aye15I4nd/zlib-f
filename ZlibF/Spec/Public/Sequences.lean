import ZlibF.Spec.Public.Domains
import ZlibF.Spec.Public.GzTrace

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
  (∀ h r call, StreamReachable kind h r → ZlibF.PlatformMemory.ByteObjectsFit h →
    StreamOperation kind r call → StreamArguments h r call →
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

/-- Every heap on which a call runs and every heap a caller edit leaves satisfies the LP64
object-size limit, as in `StreamReachable` (docs/deviations.md).
A data epoch begins with the actual init. Rebinding buffers changes no private state.
Dictionary calls are recorded with their actual result; no earlier specification is assumed.
Reset starts another epoch; its safety and ownership are covered by StreamSequenceSafety. -/
inductive InflateDataTrace (wb : Int32) (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Inflate.inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) →
      InflateDataTrace wb r after {}
  | caller {h after log} : InflateDataTrace wb r h log → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → InflateDataTrace wb r after log
  | step {h after log flush rc input output used} : InflateDataTrace wb r h log →
      ZlibF.PlatformMemory.ByteObjectsFit h → DataStep .inflate h after r flush rc input output used →
      InflateDataTrace wb r after
        { log with
          input := log.input ++ input.take used, output := log.output ++ output
          result := rc, finished := log.finished || rc == Z_STREAM_END }
  | dictionary {h after log p n bytes rc} : InflateDataTrace wb r h log → ZlibF.PlatformMemory.ByteObjectsFit h →
      StreamArguments h r (.inflateSetDictionary (some r) p n) → Bytes h p n.toNat bytes →
      C.run (Zlib.Inflate.inflateSetDictionary (some r) p n) h = .ok (rc, after) →
      InflateDataTrace wb r after
        { log with
          dictionary := if rc = Z_OK then
            if wb.toInt < 0 then log.dictionary ++ bytes else bytes else log.dictionary
          singleDictionary := log.singleDictionary &&
            !(rc = Z_OK && wb.toInt < 0 && (log.input != [] || log.output != [])) }

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

/-- The platform side of a callback protocol, for the safety goal: a call-back step that starts
on a heap whose byte objects fit (`ZlibF.PlatformMemory.ByteObjectsFit`, fewer than `2^63` bytes
each) leaves one whose byte objects fit, and a chunk that `in` hands out lies in a heap byte block
(`docs/deviations.md`, "Callback decoder input chunks"). -/
def BackPlatform {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {input : Zlib.Infback.InCb}
    {inDesc : BPtr} {output : Zlib.Infback.OutCb} {outDesc : BPtr}
    (protocol : CallbackProtocol r i window n input inDesc output outDesc) : Prop :=
  (∀ h log next count pointer after, protocol.invariant h log → ZlibF.PlatformMemory.ByteObjectsFit h →
    input inDesc next h = .ok ((count, pointer), after) →
    ZlibF.PlatformMemory.ByteObjectsFit after ∧ (count ≠ 0 → ∃ b off, pointer = .ref (.blk b) off)) ∧
  (∀ h log pointer count rc after, protocol.invariant h log → ZlibF.PlatformMemory.ByteObjectsFit h →
    output outDesc pointer count h = .ok (rc, after) → ZlibF.PlatformMemory.ByteObjectsFit after)

/-- The caller's first chunk of a call lies in a heap byte block. -/
def BackFirstChunk (z : ZStream) (first : List UInt8) : Prop :=
  first ≠ [] → ∃ b off, z.next_in = .ref (.blk b) off

/-- Callback histories of the safety goal: those of `BackReachable` whose window is a slice of a
heap byte block, and whose calls start on a heap whose byte objects fit, with a protocol that
keeps them fitting and hands out chunks in heap byte blocks (`docs/deviations.md`, "Callback
decoder window" and "Callback decoder input chunks"). A caller's edit between calls keeps the
read-only flag of every block that stays live, as `ExternalFrame` does for the call-backs: C code
cannot make memory read-only, and `Rebuffer` alone lets a window at a nonzero offset (a block the
stream does not own) become read-only in the model. -/
inductive BackSafeReachable : Heap → ZStreamRef → Nat → BPtr → Nat → Prop
  | init {h after r version wb window} : InitDomain h r version →
      8 ≤ wb.toInt → wb.toInt ≤ 15 → Writable h window (2 ^ wb.toInt.toNat) → window ≠ .null →
      (∃ w off, window = .ref (.blk w) off) →
      C.run (Zlib.Infback.inflateBackInit_ (some r) wb window version 112) h = .ok (Z_OK, after) →
      BackSafeReachable after r h.nextBlk window (2 ^ wb.toInt.toNat)
  | caller {h after r i window n} : BackSafeReachable h r i window n → Rebuffer h after r →
      SameBytePrefix h after window window n →
      (∀ b, h.live b → after.live b → after.ro b = h.ro b) → BackSafeReachable after r i window n
  | step {h after r i window n z input inDesc output outDesc first rc}
      (protocol : CallbackProtocol r i window n input inDesc output outDesc) :
      BackSafeReachable h r i window n → r.get h = some z →
      (if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first) →
      Separate z.next_in first.length window n →
      protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first } →
      ZlibF.PlatformMemory.ByteObjectsFit h → BackPlatform protocol → BackFirstChunk z first →
      C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (rc, after) →
      BackSafeReachable after r i window n

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

/-- **Safety of every permitted callback-decoder sequence** (the safety half of
`Goal.inflate_back_sequence`). A null stream is refused. Every reachable history leaves a valid
state over the caller's window. One more `inflateBack` call, for every caller protocol whose total
input is below `2^48` bytes (the runtime bounds every loop by `2^64` iterations; `docs/deviations.md`),
returns without a fault with one of its three results, keeps the state valid over the same window,
changes only the stream record, the state record, the callback's own blocks and the window slice,
and leaves the live blocks outside the callback's own unchanged (no leak). `inflateBackEnd` frees the
state. The histories are those of `BackSafeReachable`: the window is a slice of a heap byte block,
every byte object has fewer than `2^63` bytes on the heap of each call and after each call-back
step (`BackPlatform`), and every input chunk lies in a heap byte block (`BackFirstChunk`,
`BackPlatform`); `docs/deviations.md` lists these premises. The decoding clauses of
`Goal.inflateBack` (what reaches `out`, `Decodes`) are not planned (`docs/progress.md`, Scope). -/
def Goal.inflate_back_sequence_safety : Prop :=
  (∀ h input inDesc output outDesc,
    C.run (Zlib.Infback.inflateBack none input inDesc output outDesc) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r i window n, BackSafeReachable h r i window n →
    ∃ z s, BackValid h r i z s ∧ s.window = window ∧ s.wsize.toNat = n) ∧
  (∀ h r i window n z s input inDesc output outDesc
      (protocol : CallbackProtocol r i window n input inDesc output outDesc) first,
    BackSafeReachable h r i window n → BackValid h r i z s →
    (if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first) →
    Separate z.next_in first.length window n →
    protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first } →
    protocol.inputBound < 2 ^ 48 →
    ZlibF.PlatformMemory.ByteObjectsFit h → BackPlatform protocol → BackFirstChunk z first →
    ∃ rc after z' s' log,
      C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (rc, after) ∧
      BackValid after r i z' s' ∧ s'.window = window ∧ s'.wsize = s.wsize ∧
      protocol.invariant after log ∧
      (rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) ∧
      CallbackFrame protocol.own h after r i window n ∧
      (∀ b, ¬ protocol.own b → (after.live b ↔ h.live b))) ∧
  (∀ h r i window n, BackSafeReachable h r i window n →
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
    GzOperation i call → GzArguments h i s call → RegularOs fs →
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
