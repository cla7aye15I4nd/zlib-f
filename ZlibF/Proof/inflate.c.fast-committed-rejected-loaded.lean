import ZlibF.Proof.«inflate.c.fast-committed-output-credit»
import ZlibF.Proof.«inflate.c.fast-causal-loop-rejected-word-final»
import ZlibF.Proof.«inflate.c.fast-committed-exit-source»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false

/-- A BAD outcome retains its actual rejected word and physical residual
source after the translated rollback and LOAD. Normal and EOB keep their
accepted words. No future input is assumed. -/
def LoadedRejectedOutcome {ctx : FastLoopContext}
    (p : Parameters ctx) (loopHeap : Heap) (result : Zlib.Inffast.L)
    (loaded : IL) (used : Nat) : Prop :=
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
  (∃ rejected : RejectedObservation p loopHeap result,
    WordSource rejected.toObservation ∧
    stream loaded (p.input.drop used) =
      stream rejected.slow (p.input.drop rejected.pulled) ∧
    natBits p.entry.bits.toNat p.entry.hold.toNat ++
      bytesBits (p.input.take used) =
      rejected.word ++ natBits loaded.bits.toNat loaded.hold.toNat ∧
    ∀ future rest output, ¬ Symbols p.L p.D p.dict p.start
      ((p.initialWords ++ rejected.word) ++ future) rest output)

theorem WordRejectedExit.loaded_source_cases
    {ctx : FastLoopContext} {p : Parameters ctx}
    {loopHeap finished : Heap} {result : Zlib.Inffast.L}
    {zNext : ZStream} {sNext : InflateState} {loaded : IL}
    {inputArray : Array UInt8} {used : Nat}
    (exit : WordRejectedExit p loopHeap result)
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
    LoadedRejectedOutcome p loopHeap result loaded used := by
  rcases exit.2 with ⟨tracked, source, _⟩ | ⟨ended, source⟩ |
      ⟨rejected, source⟩
  · obtain ⟨streamEq, wordEq⟩ :=
      source.loaded_event exit.1 tracked.toObservation outputRange
        smallEntry inputWidth inputGet inputBound suffixRun finalJ
        loadedBits loadedHold loadedHave count
    exact Or.inl ⟨tracked, source, streamEq, wordEq⟩
  · obtain ⟨streamEq, wordEq⟩ :=
      source.loaded_event exit.1 ended.toObservation outputRange
        smallEntry inputWidth inputGet inputBound suffixRun finalJ
        loadedBits loadedHold loadedHave count
    exact Or.inr (Or.inl ⟨ended, source, streamEq, wordEq⟩)
  · obtain ⟨streamEq, wordEq⟩ :=
      source.loaded_event exit.1 rejected.toObservation outputRange
        smallEntry inputWidth inputGet inputBound suffixRun finalJ
        loadedBits loadedHold loadedHave count
    exact Or.inr (Or.inr ⟨rejected, source, streamEq,
      wordEq, rejected.no_symbols⟩)

#print axioms WordRejectedExit.loaded_source_cases
end Zlib.Inflate.Proofs.FastCommittedLoop
