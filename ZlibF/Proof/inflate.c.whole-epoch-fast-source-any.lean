import ZlibF.Proof.«inflate.c.whole-epoch-fast-observation»
import ZlibF.Proof.«inflate.c.fast-committed-any-exit-credit-v8»
namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FastCommittedLoop
set_option autoImplicit false

/-- A single chosen actual observation retains the consumed word after
rollback and LOAD, including BAD after prior accepted tokens. -/
theorem FastCommittedCallCut.observation_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8} {L D : List Nat} {dict past current : List UInt8}
    (cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current)
    (observation : Observation cut.p cut.loopHeap cut.result) (source : WordSource observation) :
    natBits slow.bits.toNat slow.hold.toNat ++ bytesBits (bs.take cut.used) =
      observation.word ++ natBits cut.loaded.bits.toNat cut.loaded.hold.toNat := by
  rcases cut.rejectedLoaded with normal | eob | bad
  · obtain ⟨other, otherSource, _residual, credit⟩ := normal
    have same := observation.word_unique other.toObservation source otherSource
    rw [← same] at credit
    simpa only [cut.pEntry, cut.qBits, cut.qHold, cut.pInput] using credit
  · obtain ⟨other, otherSource, _residual, credit⟩ := eob
    have same := observation.word_unique other.toObservation source otherSource
    rw [← same] at credit
    simpa only [cut.pEntry, cut.qBits, cut.qHold, cut.pInput] using credit
  · obtain ⟨other, otherSource, _residual, credit, _reject⟩ := bad
    have same := observation.word_unique other.toObservation source otherSource
    rw [← same] at credit
    simpa only [cut.pEntry, cut.qBits, cut.qHold, cut.pInput] using credit

#print axioms FastCommittedCallCut.observation_source
end Zlib.Inflate.Proofs.FunctionalEpoch
