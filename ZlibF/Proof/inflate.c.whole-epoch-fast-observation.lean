import ZlibF.Proof.«inflate.c.fast-committed-call-mode-v7»
namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- Physical input cursors and complete word-source identities identify
one consumed word; matching lengths alone would not identify its content. -/
theorem Observation.word_unique {ctx : FastLoopContext} {p : Parameters ctx}
    {h : Heap} {q : Zlib.Inffast.L} (left right : Observation p h q)
    (leftSource : WordSource left) (rightSource : WordSource right) : left.word = right.word := by
  have lp := left.physical
  have rp := right.physical
  change q.in_ = .ref ctx.inputRef (p.startOff + left.pulled) at lp
  change q.in_ = .ref ctx.inputRef (p.startOff + right.pulled) at rp
  have offsets := (Ptr.ref.inj (lp.symm.trans rp)).2
  have pulled : left.pulled = right.pulled := by omega
  unfold WordSource at leftSource rightSource
  have words := leftSource.symm.trans rightSource
  rw [pulled] at words
  exact List.append_cancel_right words

/-- One actual output array and cursor identify the common physical
history even when two existential exit packets expose it separately. -/
theorem Observation.history_unique {ctx : FastLoopContext} {p : Parameters ctx}
    {h : Heap} {q : Zlib.Inffast.L} (left right : Observation p h q)
    {off : Nat} {array : Array UInt8} (pointer : q.out = .ref ctx.dest off)
    (get : Space.get h ctx.dest = some array) : left.history = right.history :=
  (left.historyView off array pointer get).symm.trans (right.historyView off array pointer get)
end Zlib.Inflate.Proofs.FastCommittedLoop

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FastCommittedLoop
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

theorem FastCommittedCallCut.observation_history_unique
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8} {L D : List Nat} {dict past current : List UInt8}
    (cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current)
    (left right : Observation cut.p cut.loopHeap cut.result) : left.history = right.history := by
  obtain ⟨_input, _get, _bound, off, array, pointer, _lower, _upper, get, _room⟩ :=
    cut.ready.loop_source_geometry cut.loopRun
  exact left.history_unique right pointer get

/-- The same chosen observation carries the physical committed source
through rollback/LOAD. Separate existential packets cannot be mixed by
word length or byte-value coincidence. -/
theorem FastCommittedCallCut.accepted_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8} {L D : List Nat} {dict past current : List UInt8}
    (cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current)
    (observation : Observation cut.p cut.loopHeap cut.result) (source : WordSource observation)
    (notBad : cut.loadedState.mode ≠ BAD) :
    natBits slow.bits.toNat slow.hold.toNat ++ bytesBits (bs.take cut.used) =
      observation.word ++ natBits cut.loaded.bits.toNat cut.loaded.hold.toNat := by
  rcases cut.sourceLoaded with normal | eob | bad
  · obtain ⟨other, otherSource, _residual, credit⟩ := normal
    have same := observation.word_unique other.toObservation source otherSource
    rw [← same] at credit
    simpa only [cut.pEntry, cut.qBits, cut.qHold, cut.pInput] using credit
  · obtain ⟨other, otherSource, _residual, credit⟩ := eob
    have same := observation.word_unique other.toObservation source otherSource
    rw [← same] at credit
    simpa only [cut.pEntry, cut.qBits, cut.qHold, cut.pInput] using credit
  · obtain ⟨_broke, i, actual⟩ := bad
    have mode := cut.loaded_mode_of_loop_j actual
    exact False.elim (notBad (by simpa only using mode))

/-- Accepted source and output use one actual observation. The physical
segment, newly emitted byte list and semantic history are correlated. -/
theorem FastCommittedCallCut.accepted_output
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8} {L D : List Nat} {dict past current : List UInt8}
    (cut : FastCommittedCallCut c h r zs z s slow bs L D dict past current)
    (observation : Observation cut.p cut.loopHeap cut.result)
    (notBad : cut.loadedState.mode ≠ BAD) :
    ∃ more, more.length = cut.made ∧ writtenBytes cut.array (cut.ctx.oo + cut.made) cut.made = more ∧
      observation.history = current ++ more := by
  rcases cut.outputSegment with normal | eob | bad
  · obtain ⟨other, _source, more, count, bytes, history⟩ := normal
    exact ⟨more, count, bytes, (cut.observation_history_unique observation other.toObservation).trans history⟩
  · obtain ⟨other, _source, more, count, bytes, history⟩ := eob
    exact ⟨more, count, bytes, (cut.observation_history_unique observation other.toObservation).trans history⟩
  · obtain ⟨_broke, i, actual⟩ := bad
    have mode := cut.loaded_mode_of_loop_j actual
    exact False.elim (notBad (by simpa only using mode))

#print axioms Observation.word_unique
#print axioms Observation.history_unique
#print axioms FastCommittedCallCut.observation_history_unique
#print axioms FastCommittedCallCut.accepted_source
#print axioms FastCommittedCallCut.accepted_output
end Zlib.Inflate.Proofs.FunctionalEpoch
