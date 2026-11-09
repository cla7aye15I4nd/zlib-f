import ZlibF.Proof.«inflate.c.local-fast-copy-bad-data-invariant»
import ZlibF.Proof.«inflate.c.local-fast-state»
import ZlibF.Proof.«inflate.c.local-fast-copy-match-cases-invariant»
import ZlibF.Proof.«inflate.c.fast-view-invalid»
import ZlibF.Proof.«inflate.c.fast-view-match-cases-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An invalid fast distance updates only the message and mode. The BAD
state remains in the default decoder relation and the caller buffers keep
their original views. -/
theorem FastInputPacket.copyMatch_invalid_local_state
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (windowBranch : l.dist > l.op)
    (invalidBack : l.dist - l.op > c.whave)
    {dest : BRef} {output : Array UInt8}
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false) :
    ∃ i after,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok ({ l with op := l.dist - l.op, broke := true }, after) ∧
      after = setI
        (r.put h { z with msg := .ref (.str i) 0 }) zs
        { s with mode := BAD } ∧
      FastInputPacket after slow bs
        { l with op := l.dist - l.op, broke := true } ∧
      LocalStateJ after cutoff r zs { z with msg := .ref (.str i) 0 }
        { s with mode := BAD } ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      Space.get after dest = some output ∧
      Space.ro after dest = false := by
  obtain ⟨i, after, badRun, heapEq, _, nextInvariant, nextBuffers, sizes⟩ :=
    Zlib.Inflate.Local.FastInputPacket.badData_local_state packet invariant buffers streamPtr statePtr
      "invalid distance too far back" (by decide +kernel)
  have stateLoad : ldInflateState c.state h = .ok (s, h) := by
    rw [statePtr]
    exact ldInflateState_ok invariant.good.live.hs
  have run : Zlib.Inffast.copyMatch c l h =
      .ok ({ l with op := l.dist - l.op, broke := true }, after) := by
    have saneBool : (s.sane != 0) = true := by
      rw [invariant.pending.sane]
      decide
    unfold Zlib.Inffast.copyMatch
    simp only [windowBranch, ite_true, invalidBack]
    rw [bind_ok stateLoad]
    simp only [saneBool, ite_true]
    change Zlib.Inffast.badData c "invalid distance too far back" h =
      .ok ((), after) at badRun
    simp only [bind_app, badRun]
    rfl
  have views : ∀ ref : BRef,
      (Space.get after ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [heapEq]
    unfold badHeap
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have resultPacket : FastInputPacket after slow bs
      { l with op := l.dist - l.op, broke := true } :=
    ⟨packet.source.byte_views views, packet.cursor, packet.hold, packet.bits⟩
  refine ⟨i, after, run, heapEq, resultPacket, nextInvariant,
    nextBuffers, sizes, ?_, ?_⟩
  · rw [views]
    exact outputGet
  · rw [heapEq]
    unfold badHeap
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
    exact outputWrite

#print axioms FastInputPacket.copyMatch_invalid_local_state
end Zlib.Inflate.Local
