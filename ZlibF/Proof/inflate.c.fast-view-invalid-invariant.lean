import ZlibF.Proof.«inflate.c.fast-view-invalid»
import ZlibF.Proof.«inflate.c.fast-view-match-cases-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An invalid fast distance updates only the message and mode. The BAD
state remains in the default decoder relation and the caller buffers keep
their original views. -/
theorem FastInputPacket.copyMatch_invalid_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
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
      DefaultStateJ after r zs { z with msg := .ref (.str i) 0 }
        { s with mode := BAD } ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      Space.get after dest = some output ∧
      Space.ro after dest = false := by
  have sane : s.sane ≠ 0 := by
    rw [invariant.pending.sane]
    decide
  obtain ⟨i, after, run, heapEq, resultPacket, bytes, write⟩ :=
    packet.copyMatch_invalid_view invariant.good streamPtr statePtr
      sane windowBranch invalidBack outputGet outputWrite
  have bad := head_bad_packet invariant.good invariant.pending buffers
    buffers.bits (by rfl : HeadRegFrame slow slow) i
  rcases bad with ⟨nextGood, nextTables, nextPending,
    nextBuffers, sizes, static⟩
  have nextInvariant : DefaultStateJ after r zs
      { z with msg := .ref (.str i) 0 } { s with mode := BAD } := by
    rw [heapEq]
    refine ⟨⟨nextGood, nextTables, nextPending, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro active
      have impossible : BAD = CODELENS := by simpa using active
      contradiction
    · intro active
      have impossible : BAD = LENLENS := by simpa using active
      contradiction
    · exact invariant.held
    · exact invariant.window
    · exact invariant.wrapper
    · exact invariant.header
    · right; left
      change DICTID ≤ BAD ∧ BAD ≤ SYNC
      decide
    · intro active
      rcases active with check | length
      · have impossible : BAD = CHECK := by simpa using check
        contradiction
      · have impossible : BAD = LENGTH := by simpa using length
        contradiction
    · change (badHeap h r zs z s i).static = _
      rw [static]
      exact invariant.globals
    · exact sizes.platform invariant.platform
    · exact invariant.requestedBits
    · exact invariant.requestedWrap
    · exact Or.inr (Or.inl rfl)
  exact ⟨i, after, run, heapEq, resultPacket, nextInvariant,
    by rw [heapEq]; exact nextBuffers,
    by rw [heapEq]; exact sizes, bytes, write⟩

end Zlib.Inflate.Proofs
