import ZlibF.Proof.«inflate.c.global-functional-epoch»
import ZlibF.Proof.«inflate.c.header-exhaustive-progress»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The protocol's accepted platform scope supplies the earlier header
producer's scope on the same erased actual history. Successful init itself
discharges its allocation observation. -/
theorem platform_to_header_scope
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    {trace : InflateProtocolTrace 15 r h log pending} (scope : ProtocolWindow.PlatformScope trace) :
    HeaderDataTrace.PlatformScope trace.erase := by
  induction scope with
  | @init before after version domain actual platform =>
    exact .init (domain := domain) (actual := actual) platform
      (ProtocolWindow.successful_init_allocation domain actual)
  | @caller before after log pending prior edit earlier platform ih =>
    exact .caller (edit := edit) ih platform
  | @step before after log pending flush rc input output used prior actual earlier ih =>
    exact .step (actual := actual) ih
  | @dictionary before after log pending p n bytes rc prior arguments input actual allowed earlier ih =>
    exact .dictionary (arguments := arguments) (input := input) (actual := actual) ih

/-- All protocol-admitted default histories also have actual source-origin
fields. No caller supplies either Origin or a callee preservation contract. -/
theorem protocol_origin
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace) :
    ∃ zs z s, DefaultOriginState h r zs z s ∧ DefAlloc z :=
  HeaderDataTrace.origin_from_init trace.erase (platform_to_header_scope scope)

theorem header_phase_before_check
    {phase : HeaderPhaseView.Phase} {s : InflateState} {log : DataLog}
    (data : HeaderPhaseView.PhaseData phase s log) : s.mode < CHECK := by
  cases phase with
  | head => rw [data.1]; decide
  | block =>
    rcases data.1 with mode | mode <;> rw [mode] <;> decide
  | table => rw [data.1]; decide
  | lens => rw [data.1]; decide
  | code => rw [data.1]; decide

/-- A source-produced public header wait carries its causal parser view
and establishes the global functional ledger on that same actual state.
This applies to HEAD/TYPE/TABLE/LENLENS/CODELENS; no desired return code
or empty-output premise is added to a history constructor. -/
theorem header_wait_functional
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {flush rc : Int32} {input output : List UInt8} {used zs : Nat}
    {phase : HeaderPhaseView.Phase}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (actual : DataStep .inflate h after r flush rc input output used)
    (header : HeaderPhaseView.Meaning phase after r zs (credit log input output used rc)) :
    Meaning after r (credit log input output used rc) := by
  obtain ⟨z, s, origin, allocator, _window, empty, data⟩ := header
  obtain ⟨index, stream, state, current, _alloc, modes⟩ := dataStep_observed_modes trace scope actual
  have sameZ : stream = z := Option.some.inj (current.good.live.hz.symm.trans origin.good.live.hz)
  subst stream
  have sameIndex : index = zs := by simpa using current.good.live.zst.symm.trans origin.good.live.zst
  subst index
  have sameS : state = s := Option.some.inj (current.good.live.hs.symm.trans origin.good.live.hs)
  subst state
  have early := header_phase_before_check data
  refine Meaning.of_empty origin.toDefaultStateJ allocator empty ?_ ?_
  · intro ended
    change rc = Z_STREAM_END at ended
    rw [modes.1 ended] at early
    exact (by decide : ¬ DONE < CHECK) early
  · intro error
    change rc = Z_DATA_ERROR at error
    rw [modes.2.2.1 error] at early
    exact (by decide : ¬ BAD < CHECK) early

/-- A global header continuation retains either an actual public parser
phase plus its functional ledger, or the real in-call payload construction
cut. A call which already ran payload is not forced to be a header wait. -/
def HeaderContinuation (h after : Heap) (r : ZStreamRef) (zs : Nat) (log : DataLog)
    (input output : List UInt8) (used : Nat) (flush rc : Int32) (future rest : List Bool)
    (dict prior decoded : List UInt8) : Prop :=
  (∃ phase, HeaderPhaseView.Meaning phase after r zs (credit log input output used rc) ∧
    Meaning after r (credit log input output used rc)) ∨
  HeaderPhaseView.PayloadConstructionCut h r zs input flush future rest dict prior decoded

theorem header_progress_composition
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {pending : Bool}
    {input output : List UInt8} {used : Nat} {flush rc : Int32} {future rest : List Bool}
    {dict prior decoded : List UInt8}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (actual : DataStep .inflate h after r flush rc input output used)
    (progress : HeaderPhaseView.HeaderProgress h after r zs log input output used flush rc future rest dict prior decoded) :
    HeaderContinuation h after r zs log input output used flush rc future rest dict prior decoded := by
  rcases progress with head | block | table | lens | code | payload
  · exact Or.inl ⟨.head, head, header_wait_functional trace scope actual head⟩
  · exact Or.inl ⟨.block, block, header_wait_functional trace scope actual block⟩
  · exact Or.inl ⟨.table, table, header_wait_functional trace scope actual table⟩
  · exact Or.inl ⟨.lens, lens, header_wait_functional trace scope actual lens⟩
  · exact Or.inl ⟨.code, code, header_wait_functional trace scope actual code⟩
  · exact Or.inr payload

/-- The exhaustive first plain dynamic-header producer is now consumed at
the global protocol/functional layer. Every current/future byte boundary
returns a public causal phase with ledger, or the actual same-call payload
cut. This is not a whole-call payload or trailer completion theorem. -/
theorem head_dynamic_global_progress
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {pending : Bool}
    {flush rc : Int32} {input output futureBytes bodyBytes : List UInt8} {used last : Nat} {cmf flg : UInt8}
    {middle bodyInput rest : List Bool} {dict prior decoded : List UInt8}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (selected : HeaderPhaseView.Epoch r zs .head trace.erase)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (allBytes : (log.input ++ input) ++ futureBytes = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (first : readBits 1 (bytesBits bodyBytes) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body dict 2 prior bodyInput rest decoded) :
    HeaderContinuation h after r zs log input output used flush rc (bytesBits futureBytes) rest dict prior decoded := by
  exact header_progress_composition trace scope observed
    (selected.head_dynamic_call_exhaustive observed flushing accepted allBytes valid plain first second body)

#print axioms platform_to_header_scope
#print axioms protocol_origin
#print axioms header_phase_before_check
#print axioms header_wait_functional
#print axioms header_progress_composition
#print axioms head_dynamic_global_progress
end Zlib.Inflate.Proofs.FunctionalEpoch
