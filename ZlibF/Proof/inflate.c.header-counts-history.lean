import ZlibF.Proof.«inflate.c.header-counts-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual waiting history retains TABLE counts and its observed word. -/
theorem LenlensWaitingTrace.sound_with_counts
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (progress : LenlensProgress s s.hold s.bits received)
    (history : LenlensWaitingTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      LenlensProgress state state.hold state.bits (received ++ bytesBits input) ∧ output = [] ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist := by
  induction history with
  | begin =>
    exact ⟨z, s, initial, allocator, by simpa only [bytesBits, List.flatMap_nil, List.append_nil] using progress, rfl, rfl, rfl, rfl⟩
  | @caller before after inputs outputs prior edit platform ih =>
    obtain ⟨stream, state, current, currentAllocator, trace, empty, codeCount, litCount, distCount⟩ := ih
    obtain ⟨nextStream, next, _get, nextTrace⟩ := rebuffer_header_progress current edit platform trace
    obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherStream = nextStream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherStream
    refine ⟨nextStream, state, next, ?_, nextTrace, empty, codeCount, litCount, distCount⟩
    rw [fields]
    exact currentAllocator
  | @step before after inputs outputs callerStream callerState flush rc freshInput freshOutput used
      prior streamGet stateGet mode short actual ih =>
    obtain ⟨stream, state, current, currentAllocator, trace, empty, codeCount, litCount, distCount⟩ := ih
    have sameZ : callerStream = stream := Option.some.inj (streamGet.symm.trans current.good.live.hz)
    have sameS : callerState = state := Option.some.inj (stateGet.symm.trans current.good.live.hs)
    subst callerStream
    subst callerState
    obtain ⟨nextStream, nextState, next, nextAllocator, nextTrace, noOutput⟩ :=
      inflate_dataStep_LENLENS_header_wait current currentAllocator entry actual mode trace short
    obtain ⟨countStream, countState, countOrigin, _countAllocator, code1, lit1, dist1⟩ :=
      inflate_dataStep_LENLENS_header_wait_counts current currentAllocator entry actual mode trace short
    have sameCount : countState = nextState :=
      Option.some.inj (countOrigin.good.live.hs.symm.trans next.good.live.hs)
    subst countState
    refine ⟨nextStream, nextState, next, nextAllocator, ?_, ?_,
      code1.trans codeCount, lit1.trans litCount, dist1.trans distCount⟩
    · simpa only [bytesBits_append, List.append_assoc] using nextTrace
    · rw [empty, noOutput]
      rfl
#print axioms LenlensWaitingTrace.sound_with_counts

/-- Cumulative observed phase input is read using the original count,
which real waiting/rebuffer executions retain. Initial TABLE provenance
and the first stored phase relation remain separate producer facts. -/
theorem LenlensWaitingTrace.alphabet_with_counts
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output : List UInt8} {received : List Bool}
    (initial : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (progress : LenlensProgress s s.hold s.bits received)
    (history : LenlensWaitingTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧ output = [] ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      ∀ c bs, c.strm = some r → c.st = some (.tab zs) → state.mode = LENLENS →
        Bytes after stream.next_in stream.avail_in.toNat bs →
        3 * (state.ncode.toNat - state.«have».toNat) ≤
          (Zlib.Inflate.Proofs.stream (dispatchRegs stream state) bs).length →
        ∃ regs used filled, used ≤ bs.length ∧
          BitInv after regs (bs.drop used) ∧ filled.WellFormed ∧ Good3 filled.lens 19 ∧
          runX (inflate_LENLENS c) (dispatchRegs stream state) after =
            runX (llTail c) regs (setI after zs filled) ∧
          ∀ future, readCodeLenLens s.ncode.toNat
            (((received ++ bytesBits input) ++ bytesBits (bs.take used)) ++ future) = some
            (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19,
             natBits regs.bits.toNat regs.hold.toNat ++ future) := by
  obtain ⟨stream, state, current, currentAllocator, trace, empty, codeCount, litCount, distCount⟩ :=
    history.sound_with_counts initial allocator progress
  refine ⟨stream, state, current, currentAllocator, empty, codeCount, litCount, distCount, ?_⟩
  intro c bs _streamPointer statePointer mode inputBytes enough
  obtain ⟨ncode, haveBound, _nlen, _ndist, prefixValues⟩ := current.headerLengths mode
  have view := header_input_view_of_bytes (s := state) inputBytes current.held
  obtain ⟨regs, used, filled, bound, inv, wf, good, cut, alphabet⟩ :=
    inflate_LENLENS_resumed_alphabet_prefix statePointer current.good.live.hs
      current.good.inv.wf ncode haveBound prefixValues view trace enough
  refine ⟨regs, used, filled, bound, inv, wf, good, cut, ?_⟩
  intro future
  have parsed := alphabet future
  rw [codeCount] at parsed
  exact parsed

#print axioms LenlensWaitingTrace.alphabet_with_counts

end Zlib.Inflate.Proofs
