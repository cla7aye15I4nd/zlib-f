import ZlibF.Proof.«inflate.c.header-progress-observed»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A finite segment of actual public waiting calls and legal buffer edits.
The step guard reads the incoming record and selects input exhaustion.
Constructors record the original DataStep, never the desired invariant,
phase word or decoded-format conclusion. The segment starts at a phase
boundary; it is not a replacement for the full initialized data history. -/
inductive LenlensWaitingTrace (start : Heap) (r : ZStreamRef) (zs : Nat) :
    Heap → List UInt8 → List UInt8 → Prop where
  | begin : LenlensWaitingTrace start r zs start [] []
  | caller {h after input output} : LenlensWaitingTrace start r zs h input output →
      Rebuffer h after r → ZlibF.PlatformMemory.ByteObjectsFit after →
      LenlensWaitingTrace start r zs after input output
  | step {h after priorInput priorOutput z s flush rc input output used} :
      LenlensWaitingTrace start r zs h priorInput priorOutput →
      r.get h = some z → h.istates zs = some s → s.mode = LENLENS →
      (s.bits.toNat + 8 * z.avail_in.toNat) / 3 < s.ncode.toNat - s.«have».toNat →
      DataStep .inflate h after r flush rc input output used →
      LenlensWaitingTrace start r zs after (priorInput ++ input.take used) (priorOutput ++ output)

/-- Every finite selected waiting segment retains its initialized state
and explicit phase word for the cumulative actually observed input.
Caller replacements do not retain or constrain any unread suffix. -/
theorem LenlensWaitingTrace.sound
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (progress : LenlensProgress s s.hold s.bits received)
    (history : LenlensWaitingTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      LenlensProgress state state.hold state.bits (received ++ bytesBits input) ∧ output = [] := by
  induction history with
  | begin =>
    exact ⟨z, s, initial, allocator, by simpa only [bytesBits, List.flatMap_nil, List.append_nil] using progress, rfl⟩
  | @caller before after inputs outputs prior edit platform ih =>
    obtain ⟨stream, state, current, currentAllocator, trace, empty⟩ := ih
    obtain ⟨nextStream, next, _get, nextTrace⟩ := rebuffer_header_progress current edit platform trace
    obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherStream = nextStream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherStream
    refine ⟨nextStream, state, next, ?_, nextTrace, empty⟩
    rw [fields]
    exact currentAllocator
  | @step before after inputs outputs callerStream callerState flush rc freshInput freshOutput used
      prior streamGet stateGet mode short actual ih =>
    obtain ⟨stream, state, current, currentAllocator, trace, empty⟩ := ih
    have sameZ : callerStream = stream := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    have sameS : callerState = state := Option.some.inj (stateGet.symm.trans current.good.live.hs)
    subst callerStream
    subst callerState
    obtain ⟨nextStream, nextState, next, nextAllocator, nextTrace, noOutput⟩ :=
      inflate_dataStep_LENLENS_header_wait current currentAllocator entry actual mode trace short
    refine ⟨nextStream, nextState, next, nextAllocator, ?_, ?_⟩
    · simpa only [bytesBits_append, List.append_assoc] using nextTrace
    · rw [empty, noOutput]
      rfl

/-- A zero counter supplies the conditional seed from the actual stored
held word. Initial mode and actual TABLE phase origin are separate facts
to be supplied by the phase-entry producer. -/
theorem LenlensWaitingTrace.sound_from_zero
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (zero : s.«have» = 0) (history : LenlensWaitingTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      LenlensProgress state state.hold state.bits
        (natBits s.bits.toNat s.hold.toNat ++ bytesBits input) ∧ output = [] := by
  exact history.sound initial allocator (LenlensProgress.initial zero _ _)

#print axioms LenlensWaitingTrace.sound
#print axioms LenlensWaitingTrace.sound_from_zero
end Zlib.Inflate.Proofs
