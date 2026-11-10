import ZlibF.Proof.«inflate.c.fast-committed-callee-join»
import ZlibF.Proof.«inflate.c.fast-exit-loaded-source»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Math.InflateFastSource
set_option autoImplicit false

/-- A real accepted final body supplies both the physical residual stream
and the exact committed word content after the translated suffix and LOAD. -/
theorem WordSource.loaded_event
    {ctx : FastLoopContext} {p : Parameters ctx}
    {loopHeap finished : Heap} {result : Zlib.Inffast.L}
    {zNext : ZStream} {sNext : InflateState} {loaded : IL}
    {inputArray : Array UInt8} {used : Nat}
    (final : FastLoopExit ctx loopHeap result)
    (obs : Observation p loopHeap result)
    (source : WordSource obs)
    (outputRange : FastLoopOutputRange ctx loopHeap result)
    (smallEntry : p.entry.bits.toNat < 8)
    (inputWidth : p.input.length < 2 ^ 32)
    (inputGet : Space.get loopHeap ctx.inputRef = some inputArray)
    (inputBound : p.startOff + p.input.length ≤ inputArray.size)
    (suffixRun : C.run (fastAfterLoopView ctx.c result) loopHeap = .ok ((), finished))
    (finalJ : DefaultStateJ finished ctx.r ctx.zs zNext sNext)
    (loadedBits : loaded.bits = sNext.bits)
    (loadedHold : loaded.hold = sNext.hold)
    (loadedHave : loaded.have_ = zNext.avail_in)
    (count : loaded.have_.toNat + used = p.input.length) :
    stream loaded (p.input.drop used) =
      stream obs.slow (p.input.drop obs.pulled) ∧
    natBits p.entry.bits.toNat p.entry.hold.toNat ++
      bytesBits (p.input.take used) =
      obs.word ++ natBits loaded.bits.toNat loaded.hold.toNat := by
  obtain ⟨usedEq, streamEq, _content⟩ :=
    final.loaded_source_identity_of_origin obs.packet obs.origin
      obs.physical outputRange smallEntry p.initialLast p.rawMargin
      inputWidth inputGet inputBound suffixRun finalJ
      loadedBits loadedHold loadedHave count
  have cursor : result.in_ = .ref ctx.inputRef (p.startOff + obs.pulled) :=
    obs.physical
  have account : FastLoopInputBudget ctx p.startOff p.entry.bits.toNat result := by
    refine ⟨p.startOff + obs.pulled, cursor, by omega, ?_⟩
    have ledger := obs.origin.accounting
    omega
  have limit : FastLoopInputLimit ctx result := by
    refine ⟨p.startOff + obs.pulled,
      p.startOff + p.input.length - 5, cursor, p.initialLast, ?_⟩
    have bound := obs.origin.pulledBound
    omega
  obtain ⟨io, resultPtr, _lower, _upper, _returned, _writtenPtr,
    _writtenCount, writtenBits, writtenHold⟩ :=
    final.writeback_input_scalar_fields account limit outputRange smallEntry
      p.initialLast p.rawMargin inputWidth inputGet inputBound suffixRun finalJ
  have loadedBitNat : loaded.bits.toNat = result.bits.toNat % 8 := by
    rw [loadedBits]
    exact writtenBits
  have loadedHoldNat : loaded.hold.toNat =
      result.hold.toNat % 2 ^ (result.bits.toNat % 8) := by
    rw [loadedHold]
    exact writtenHold
  exact ⟨streamEq, source.loaded_prefix smallEntry usedEq
    loadedBitNat loadedHoldNat⟩

/-- A causal fast exit keeps the accepted normal/EOB source certificate,
or exposes the actual BAD state. No accepted source is asserted for BAD. -/
theorem WordExit.loaded_source_cases
    {ctx : FastLoopContext} {p : Parameters ctx}
    {loopHeap finished : Heap} {result : Zlib.Inffast.L}
    {zNext : ZStream} {sNext : InflateState} {loaded : IL}
    {inputArray : Array UInt8} {used : Nat}
    (exit : WordExit p loopHeap result)
    (outputRange : FastLoopOutputRange ctx loopHeap result)
    (smallEntry : p.entry.bits.toNat < 8)
    (inputWidth : p.input.length < 2 ^ 32)
    (inputGet : Space.get loopHeap ctx.inputRef = some inputArray)
    (inputBound : p.startOff + p.input.length ≤ inputArray.size)
    (suffixRun : C.run (fastAfterLoopView ctx.c result) loopHeap = .ok ((), finished))
    (finalJ : DefaultStateJ finished ctx.r ctx.zs zNext sNext)
    (loadedBits : loaded.bits = sNext.bits)
    (loadedHold : loaded.hold = sNext.hold)
    (loadedHave : loaded.have_ = zNext.avail_in)
    (count : loaded.have_.toNat + used = p.input.length) :
    (∃ tracked : Tracked p loopHeap result,
      WordSource tracked.toObservation ∧
      stream loaded (p.input.drop used) =
        stream tracked.slow (p.input.drop tracked.pulled) ∧
      natBits p.entry.bits.toNat p.entry.hold.toNat ++
        bytesBits (p.input.take used) =
        tracked.word ++ natBits loaded.bits.toNat loaded.hold.toNat) ∨
    (∃ ended : Ended p loopHeap result,
      WordSource ended.toObservation ∧
      stream loaded (p.input.drop used) =
        stream ended.slow (p.input.drop ended.pulled) ∧
      natBits p.entry.bits.toNat p.entry.hold.toNat ++
        bytesBits (p.input.take used) =
        ended.word ++ natBits loaded.bits.toNat loaded.hold.toNat) ∨
    (result.broke = true ∧ ∃ i,
      DefaultStateJ loopHeap ctx.r ctx.zs
        {ctx.z with msg := .ref (.str i) 0}
        {ctx.s with mode := BAD}) := by
  rcases exit.2 with accepted | ended | bad
  · obtain ⟨tracked, source⟩ := accepted
    obtain ⟨streamEq, wordEq⟩ :=
      source.loaded_event exit.1 tracked.toObservation outputRange
        smallEntry inputWidth inputGet inputBound suffixRun finalJ
        loadedBits loadedHold loadedHave count
    exact Or.inl ⟨tracked, source, streamEq, wordEq⟩
  · obtain ⟨eob, source⟩ := ended
    obtain ⟨streamEq, wordEq⟩ :=
      source.loaded_event exit.1 eob.toObservation outputRange
        smallEntry inputWidth inputGet inputBound suffixRun finalJ
        loadedBits loadedHold loadedHave count
    exact Or.inr (Or.inl ⟨eob, source, streamEq, wordEq⟩)
  · exact Or.inr (Or.inr bad)

#print axioms WordSource.loaded_event
#print axioms WordExit.loaded_source_cases
end Zlib.Inflate.Proofs.FastCommittedLoop
