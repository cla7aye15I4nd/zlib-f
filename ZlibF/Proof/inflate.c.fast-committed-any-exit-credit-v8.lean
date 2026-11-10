import ZlibF.Proof.«inflate.c.fast-committed-any-exit-v8»
import ZlibF.Proof.«inflate.c.fast-committed-output-credit»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FastCommittedLoop
open Zlib.Inflate.Proofs.FunctionalTrailer
set_option autoImplicit false

/-- The same physical output ledger is extended for every actual fast exit,
including BAD after an already emitted accepted prefix. -/
theorem FastCommittedCallCutV8.observation_credit
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    {L D : List Nat} {dict past current prior : List UInt8} {credited : Nat}
    (full : FastCommittedCallCutV8 c h r zs z s slow bs L D dict past current)
    (observation : Observation full.cut.p full.cut.loopHeap full.cut.result)
    (ledger : OutputCredit full.cut.restored (leaveStream z slow)
      (leaveState s slow) slow prior current credited)
    (slowCount : slow.left.toNat ≤ slow.out_.toNat) :
    ∃ more : List UInt8,
      observation.history = current ++ more ∧
      OutputCredit full.cut.loadedHeap full.cut.zNext full.cut.loadedState
        full.cut.loaded prior observation.history credited := by
  let cut := full.cut
  obtain ⟨more, length, bytes, history⟩ := full.observationSegment observation
  have credit := FastPassiveFrame.adler_credit cut.passive ledger.checksum
  have delta := loaded_output_delta slowCount cut.loadedOut cut.leftCount
  have physical : ∃ ref off arr,
      slow.put = .ref ref off ∧
      cut.loaded.put = .ref ref (off + more.length) ∧
      Space.get cut.loadedHeap ref = some arr ∧
      off + more.length ≤ arr.size ∧
      ZlibF.Math.LZ77Copy.writtenBytes arr
        (off + more.length) more.length = more := by
    refine ⟨cut.ctx.dest, cut.ctx.oo, cut.array,
      cut.ctxPut, ?_, cut.outputGet, ?_, ?_⟩
    · rw [cut.loadedPut, cut.ctxPut, length]
      rfl
    · simpa only [length] using cut.outputBound
    · simpa only [length] using bytes
  have applied := OutputCredit.append_observed ledger
    (by simpa only [length] using cut.frame)
    credit (by simpa only [length] using delta) physical
  exact ⟨more, history, by simpa only [history] using applied⟩

#print axioms FastCommittedCallCutV8.observation_credit
end Zlib.Inflate.Proofs.FunctionalEpoch
