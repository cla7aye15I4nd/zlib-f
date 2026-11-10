import ZlibF.Proof.«inflate.c.global-token-composition»
import ZlibF.Proof.«inflate.c.symbols-retained-context»
import ZlibF.Proof.«inflate.c.header-payload-progress»
import ZlibF.Proof.«inftrees.c.decode.fast-flags»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees SlowTokenPath
set_option autoImplicit false

/-- The recorded actual constructor run also supplies the operation-flag
property needed by the fast decoder's different branch order. -/
theorem actual_constructor_fast_flags
    {h : Heap} {type : UInt32} {rl rw : WRef} {ol ow countOffset : Nat}
    {count bits : UInt32} {rc : CodeRef} {result : Int32 × CodePtr × UInt32} {codes : Array Code}
    (trace : PayloadStable.CallTrace h type rl ol count rc countOffset bits rw ow result codes)
    (kind : type = LENS ∨ type = DISTS) (success : result.1 = 0) :
    Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible type codes countOffset result.2.2.toNat := by
  obtain ⟨pre, after, actual, _frame, get⟩ := trace
  obtain ⟨other, otherHeap, source, _result, flags⟩ :=
    Zlib.Inftrees.Proofs.constructor_establishes_fast_leaf_flags _ _ _ _ _ _ _ _ _ _ pre kind
  rw [actual] at source
  cases source
  exact flags success codes get

theorem pair_distance_fast_flags
    {h : Heap} {zs offset : Nat} {before middle state : InflateState}
    (trace : PayloadStable.PairTrace h zs before middle state offset) :
    Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS state.codes offset state.distbits.toNat := by
  obtain ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD,
    _middle, stateEq, _next, _lengthCall, distanceCall⟩ := trace
  have flags := actual_constructor_fast_flags distanceCall (Or.inr rfl) rfl
  rw [stateEq]
  exact flags

theorem packet_distance_fast_flags
    {h : Heap} {r : ZStreamRef} {zs : Nat} {input : List UInt8} {flush : Int32}
    {future rest : List Bool} {dict prior decoded : List UInt8}
    (packet : PayloadPhaseView.Packet h r zs input flush future rest dict prior decoded) :
    Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS packet.boundary.state.codes
      packet.boundary.offset packet.boundary.state.distbits.toNat :=
  pair_distance_fast_flags packet.boundary.construction

/-- The same actual header packet, augmented with the derived global
logical window, an independent first-token continuation and an output-prefix
ghost. Construction provenance and the real outer while remain in packet.
This valid-source representation does not assert a full future token exists
at arbitrary malformed-history states. -/
structure DynamicPayloadReady (h : Heap) (r : ZStreamRef) (zs : Nat) (log : DataLog)
    (input : List UInt8) (flush : Int32) (future rest : List Bool) (decodedOutput : List UInt8) where
  packet : PayloadPhaseView.Packet h r zs input flush future rest log.dictionary log.output decodedOutput
  representation : PayloadRepresentation
    (setI packet.codeHeap zs packet.boundary.state) r zs packet.codeZ packet.boundary.state
    {packet.boundary.regs with ret := 0} (input.drop (packet.headerUsed + packet.boundary.used))
    (packet.decoded.take packet.codeState.nlen.toNat) (packet.decoded.drop packet.codeState.nlen.toNat)
    (log.dictionary ++ log.output)
  outputPrefix : log.output <+: decodedOutput
  token : TokenSyntax (packet.decoded.take packet.codeState.nlen.toNat) (packet.decoded.drop packet.codeState.nlen.toNat)
  tokenInput : token.input =
    stream {packet.boundary.regs with ret := 0} (input.drop (packet.headerUsed + packet.boundary.used)) ++ future
  tokenAdmissible : token.admissible log.dictionary log.output
  tokenPhase : TokenPhase token packet.boundary.state token.input
  tokenContinuation :
    (token.ended = true ∧ token.rest = rest ∧ decodedOutput = log.output) ∨
    (token.ended = false ∧
      Symbols (packet.decoded.take packet.codeState.nlen.toNat) (packet.decoded.drop packet.codeState.nlen.toNat)
        log.dictionary (token.effect log.dictionary log.output) token.rest rest decodedOutput)

/-- Actual dynamic construction establishes the common payload invariant.
Installed tables and StableQuery come from its two actual constructor
traces; the saved logical dictionary comes from the admitted protocol and
the real zero-window state, including an empty dictionary handshake. -/
theorem dynamic_packet_ready
    {h : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {pending : Bool}
    {input : List UInt8} {flush : Int32} {future rest : List Bool} {decodedOutput : List UInt8}
    {phase : HeaderPhaseView.Phase}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (before : HeaderPhaseView.Meaning phase h r zs log)
    (p : PayloadPhaseView.Packet h r zs input flush future rest log.dictionary log.output decodedOutput) :
    Nonempty (DynamicPayloadReady h r zs log input flush future rest decodedOutput) := by
  obtain ⟨oldZ, oldState, origin, _allocator, oldWindow, _emptyOutput, data⟩ := before
  have emptyHistory := protocol_zero_window_history trace scope origin.good
    (header_phase_before_check data) oldWindow
  obtain ⟨_bound, current, buffers, bits, _cursor, _have, _put, _left, _out,
    window, mode, symbols, _actual⟩ := p.endpoint
  let state := p.boundary.state
  let heap := setI p.codeHeap zs state
  have get : Space.get heap (CodeRef.istate_codes zs) = some state.codes :=
    CodeRef.get_istate_codes (setI_istates_same ..)
  have tables : InstalledTables heap state (p.decoded.take p.codeState.nlen.toNat)
      (p.decoded.drop p.codeState.nlen.toNat) := by
    exact ⟨⟨.istate_codes zs, 0, state.codes, p.boundary.offset, p.boundary.lenPtr, get,
      p.boundary.lens, p.boundary.stableL⟩,
      ⟨.istate_codes zs, p.boundary.offset, state.codes, p.boundary.tableUsed, p.boundary.distPtr,
        get, p.boundary.dists, p.boundary.stableD⟩⟩
  have dictionary : InflateDictionary heap state
      ((log.dictionary ++ log.output).drop
        ((log.dictionary ++ log.output).length - 2 ^ state.wbits.toNat)) := by
    rw [emptyHistory]
    simpa only [List.drop_nil] using zero_window_dictionary current.good window
  obtain ⟨token, inputEq, admissible, phase, continuation⟩ := payload_token_from_symbols symbols mode
  refine ⟨{
    packet := p
    representation := ⟨current, buffers, bits, tables, dictionary⟩
    outputPrefix := symbols_history_prefix symbols
    token := token
    tokenInput := inputEq
    tokenAdmissible := admissible
    tokenPhase := by rw [inputEq]; exact phase
    tokenContinuation := continuation }⟩

/-- The source CODELENS producer is consumed at the actual protocol and
global semantic layer. It exhaustively returns a real public header wait
with its functional ledger, or the same-call dynamic payload ready packet.
No outgoing mode, installed table, J or expected output is a history premise. -/
theorem code_public_global_packet_exhaustive
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {pending : Bool}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (before : HeaderPhaseView.Meaning .code h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    ∃ (z : ZStream) (s : InflateState) (record : HeaderPhaseView.AlphabetMeta) (received : List Bool),
      r.get h = some z ∧ h.istates zs = some s ∧
      HeaderPhaseView.View HeaderPhaseView.readAlphabet record (bytesBits log.input) received ∧
      ∀ (future payloadInput rest : List Bool) (decodedOutput : List UInt8) (decoded : List Nat),
        CodeLens record.alphabet (s.nlen.toNat + s.ndist.toNat) []
          ((received ++ bytesBits input) ++ future) payloadInput decoded →
        HasEndOfBlock (decoded.take s.nlen.toNat) → Acceptable .litLen (decoded.take s.nlen.toNat) →
        Acceptable .dist (decoded.drop s.nlen.toNat) →
        Symbols (decoded.take s.nlen.toNat) (decoded.drop s.nlen.toNat)
          log.dictionary log.output payloadInput rest decodedOutput →
        (HeaderPhaseView.Meaning .code after r zs (credit log input output used rc) ∧
          Meaning after r (credit log input output used rc)) ∨
        Nonempty (DynamicPayloadReady h r zs log input flush future rest decodedOutput) := by
  obtain ⟨z, s, record, received, getZ, getS, view, consume⟩ :=
    HeaderPhaseView.Meaning.code_public_packet_exhaustive (platform_to_header_scope scope) before observed accepted
  refine ⟨z, s, record, received, getZ, getS, view, ?_⟩
  intro future payloadInput rest decodedOutput decoded parsed eob validL validD symbols
  rcases consume future payloadInput rest log.dictionary log.output decodedOutput decoded
      parsed eob validL validD symbols with wait | payload
  · exact Or.inl ⟨wait, header_wait_functional trace scope observed wait⟩
  · obtain ⟨packet⟩ := payload
    exact Or.inr (dynamic_packet_ready trace scope before packet)

def DynamicHeaderContinuation (h after : Heap) (r : ZStreamRef) (zs : Nat) (log : DataLog)
    (input output : List UInt8) (used : Nat) (flush rc : Int32) (future rest : List Bool)
    (decoded : List UInt8) : Prop :=
  (∃ phase, HeaderPhaseView.Meaning phase after r zs (credit log input output used rc) ∧
    Meaning after r (credit log input output used rc)) ∨
  Nonempty (DynamicPayloadReady h r zs log input flush future rest decoded)

/-- All five actual public header phases and the rich same-call dynamic
payload packet join the same protocol, logical-window and functional
interface. No installed-table or expected-output oracle is inserted. -/
theorem header_packet_global_composition
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {pending : Bool}
    {input output : List UInt8} {used : Nat} {flush rc : Int32} {future rest : List Bool}
    {decoded : List UInt8} {phase : HeaderPhaseView.Phase}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (before : HeaderPhaseView.Meaning phase h r zs log)
    (actual : DataStep .inflate h after r flush rc input output used)
    (progress : HeaderPhaseView.HeaderPacketProgress h after r zs log input output used flush rc
      future rest log.dictionary log.output decoded) :
    DynamicHeaderContinuation h after r zs log input output used flush rc future rest decoded := by
  rcases progress with head | block | table | lens | code | payload
  · exact Or.inl ⟨.head, head, header_wait_functional trace scope actual head⟩
  · exact Or.inl ⟨.block, block, header_wait_functional trace scope actual block⟩
  · exact Or.inl ⟨.table, table, header_wait_functional trace scope actual table⟩
  · exact Or.inl ⟨.lens, lens, header_wait_functional trace scope actual lens⟩
  · exact Or.inl ⟨.code, code, header_wait_functional trace scope actual code⟩
  · obtain ⟨packet⟩ := payload
    exact Or.inr (dynamic_packet_ready trace scope before packet)

/-- Actual initialized plain-header history now reaches the installed
dynamic payload representation, not only a lossy source-equality cut.
Arbitrary current/future byte boundaries and all public waiting phases
remain included in this selected first-dynamic-block scope. -/
theorem head_dynamic_global_ready
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {pending : Bool}
    {flush rc : Int32} {input output futureBytes bodyBytes decoded : List UInt8}
    {used last : Nat} {cmf flg : UInt8} {middle bodyInput rest : List Bool}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (selected : HeaderPhaseView.Epoch r zs .head trace.erase)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (allBytes : (log.input ++ input) ++ futureBytes = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (first : readBits 1 (bytesBits bodyBytes) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body log.dictionary 2 log.output bodyInput rest decoded) :
    DynamicHeaderContinuation h after r zs log input output used flush rc (bytesBits futureBytes) rest decoded := by
  exact header_packet_global_composition trace scope selected.checked.2 observed
    (selected.head_dynamic_call_packet observed flushing accepted allBytes valid plain first second body)

theorem block_dynamic_global_ready
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {pending : Bool}
    {flush rc : Int32} {input output decoded : List UInt8} {used last : Nat}
    {future middle bodyInput rest : List Bool}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (before : HeaderPhaseView.Meaning .block h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (first : readBits 1 (bytesBits input ++ future) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body log.dictionary 2 log.output bodyInput rest decoded) :
    DynamicHeaderContinuation h after r zs log input output used flush rc future rest decoded := by
  exact header_packet_global_composition trace scope before observed
    (HeaderPhaseView.Meaning.block_dynamic_call_packet (platform_to_header_scope scope) before
      observed flushing accepted first second body)

#print axioms dynamic_packet_ready
#print axioms actual_constructor_fast_flags
#print axioms pair_distance_fast_flags
#print axioms packet_distance_fast_flags
#print axioms code_public_global_packet_exhaustive
#print axioms header_packet_global_composition
#print axioms head_dynamic_global_ready
#print axioms block_dynamic_global_ready
end Zlib.Inflate.Proofs.FunctionalEpoch
