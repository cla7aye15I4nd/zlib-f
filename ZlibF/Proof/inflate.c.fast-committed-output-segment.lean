import ZlibF.Proof.«inflate.c.fast-committed-callee-passive»
import ZlibF.Proof.«inflate.c.fast-segment-output»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- An accepted causal fast-loop exit identifies its newly written physical
bytes with the extension of the tracked history. A BAD exit is kept separate. -/
def OutputSegment {ctx : FastLoopContext} (p : Parameters ctx)
    (loopHeap : Heap) (result : Zlib.Inffast.L)
    (array : Array UInt8) (made : Nat) (old : List UInt8) : Prop :=
  (∃ tracked : Tracked p loopHeap result,
    WordSource tracked.toObservation ∧
    ∃ more : List UInt8, more.length = made ∧
      writtenBytes array (ctx.oo + made) made = more ∧
      tracked.history = old ++ more) ∨
  (∃ ended : Ended p loopHeap result,
    WordSource ended.toObservation ∧
    ∃ more : List UInt8, more.length = made ∧
      writtenBytes array (ctx.oo + made) made = more ∧
      ended.history = old ++ more) ∨
  (result.broke = true ∧ ∃ i,
    DefaultStateJ loopHeap ctx.r ctx.zs
      {ctx.z with msg := .ref (.str i) 0} {ctx.s with mode := BAD})

theorem FastLoopReady.output_array
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ array : Array UInt8, Space.get h ctx.dest = some array := by
  rcases ready with ⟨_, _, output, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, outputGet, _⟩
  exact ⟨output, outputGet⟩

theorem WordReady.entry_history_eq
    {ctx : FastLoopContext} {p : Parameters ctx}
    {h : Heap} {q : Zlib.Inffast.L} {array : Array UInt8}
    {current : List UInt8}
    (ready : WordReady p h q)
    (ptr : q.out = .ref ctx.dest ctx.oo)
    (get : Space.get h ctx.dest = some array)
    (observed : writtenBytes array ctx.oo (ctx.oo - ctx.bg) = current) :
    ready.state.tracked.history = current := by
  exact (ready.state.tracked.historyView ctx.oo array ptr get).symm.trans observed

theorem WordReady.output_segment
    {ctx : FastLoopContext} {p : Parameters ctx}
    {h loopHeap loadedHeap : Heap} {q result : Zlib.Inffast.L}
    {made : Nat} {array : Array UInt8}
    (ready : WordReady p h q)
    (exit : WordExit p loopHeap result)
    (range : FastLoopOutputRange ctx loopHeap result)
    (frame : BufferFrame h loadedHeap
      (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
      [⟨.ref ctx.dest ctx.oo, made⟩])
    (views : ∀ ref : BRef, Space.get loadedHeap ref = Space.get loopHeap ref)
    (initialPtr : q.out = .ref ctx.dest ctx.oo)
    (finalPtr : result.out = .ref ctx.dest (ctx.oo + made))
    (outputGet : Space.get loadedHeap ctx.dest = some array) :
    OutputSegment p loopHeap result array made ready.state.tracked.history := by
  rcases ready.state.safety with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, beforeGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨finalOff, loopArray, rangePtr, rangeLower,
    rangeUpper, loopGet, loopBound⟩ := range
  have finalOffEq : finalOff = ctx.oo + made :=
    (Ptr.ref.inj (rangePtr.symm.trans finalPtr)).2
  subst finalOff
  have sameArray : array = loopArray := Option.some.inj
    (outputGet.symm.trans ((views ctx.dest).trans loopGet))
  subst loopArray
  have oldCountBound : ctx.oo - ctx.bg ≤ ctx.oo := Nat.sub_le _ _
  have oldBound : ctx.oo ≤ output.size := by omega
  have newBound : ctx.oo + made ≤ array.size := by omega
  have oldBytes : writtenBytes output ctx.oo (ctx.oo - ctx.bg) =
      ready.state.tracked.history :=
    ready.state.tracked.historyView ctx.oo output initialPtr beforeGet
  have oldLen : ready.state.tracked.history.length = ctx.oo - ctx.bg := by
    rw [← oldBytes]
    simp only [writtenBytes, List.length_take, List.length_drop,
      Array.length_toList]
    have bgLe : ctx.bg ≤ ctx.oo := by
      rw [ctx.beginEq]
      exact Nat.sub_le _ _
    omega
  have more_of_history {whole : List UInt8}
      (wholeBytes : writtenBytes array (ctx.oo + made)
        (ctx.oo + made - ctx.bg) = whole) :
      ∃ more : List UInt8, more.length = made ∧
        writtenBytes array (ctx.oo + made) made = more ∧
        whole = ready.state.tracked.history ++ more := by
    have count : ctx.oo + made - ctx.bg = (ctx.oo - ctx.bg) + made := by
      have bgLe : ctx.bg ≤ ctx.oo := by
        rw [ctx.beginEq]; exact Nat.sub_le _ _
      omega
    rw [count] at wholeBytes
    exact fast_segment_of_whole frame beforeGet outputGet
      oldCountBound oldBound newBound oldLen oldBytes wholeBytes
  rcases exit.2 with ⟨tracked, source⟩ | ⟨ended, source⟩ | bad
  · have whole := tracked.historyView (ctx.oo + made) array finalPtr
      ((views ctx.dest).symm.trans outputGet)
    obtain ⟨more, length, bytes, append⟩ := more_of_history whole
    exact Or.inl ⟨tracked, source, more, length, bytes, append⟩
  · have whole := ended.historyView (ctx.oo + made) array finalPtr
      ((views ctx.dest).symm.trans outputGet)
    obtain ⟨more, length, bytes, append⟩ := more_of_history whole
    exact Or.inr (Or.inl ⟨ended, source, more, length, bytes, append⟩)
  · exact Or.inr (Or.inr bad)

#print axioms WordReady.output_segment
end Zlib.Inflate.Proofs.FastCommittedLoop
