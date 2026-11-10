import ZlibF.Proof.«inflate.c.payload-packet-unique»
import ZlibF.Proof.«inflate.c.payload-body-future-safety-aligned»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false

/-- The actual continuing-loop geometry transports an independent parser
residual to the safety loop's next packet, including repeated byte values. -/
theorem fast_continuing_future_symbols_transport
    {h : Heap} {result : Zlib.Inffast.L}
    {semanticSlow nextSlow : IL}
    {raw nextRaw : List UInt8} {used off nextOff : Nat}
    {inputRef : BRef} {last : BPtr}
    {L D : List Nat} {dict history target : List UInt8}
    {tail future : List Bool}
    (semanticPacket : FastInputPacket h semanticSlow (raw.drop used) result)
    (nextPacket : FastInputPacket h nextSlow nextRaw result)
    (rawMargin : 6 ≤ raw.length)
    (nextMargin : 6 ≤ nextRaw.length)
    (usedBound : used ≤ raw.length)
    (startLast : last = .ref inputRef (off + raw.length - 5))
    (nextLast : last = .ref inputRef (nextOff + nextRaw.length - 5))
    (cursor : result.in_ = inputAdvance (.ref inputRef off) used)
    (nextPtr : nextSlow.next = .ref inputRef nextOff)
    (parsed : Symbols L D dict history
      (stream semanticSlow (raw.drop used) ++ future) tail target) :
    nextRaw = raw.drop used ∧
      stream nextSlow nextRaw = stream semanticSlow (raw.drop used) ∧
      Symbols L D dict history (stream nextSlow nextRaw ++ future) tail target := by
  have nextCursor : result.in_ = .ref inputRef nextOff := by
    rw [nextPacket.cursor, nextPtr]
  have lengthEq : (raw.drop used).length = nextRaw.length :=
    fast_remaining_length_of_cursor rawMargin nextMargin usedBound
      startLast nextLast cursor nextCursor
  have nonempty : raw.drop used ≠ [] := by
    intro empty
    rw [empty] at lengthEq
    have zero : nextRaw.length = 0 := by simpa using lengthEq.symm
    omega
  have sameRaw := semanticPacket.unread_unique_of_length
    nextPacket nonempty lengthEq
  have bits : semanticSlow.bits = nextSlow.bits :=
    semanticPacket.bits.symm.trans nextPacket.bits
  have hold : semanticSlow.hold = nextSlow.hold :=
    semanticPacket.hold.symm.trans nextPacket.hold
  have sameStream : stream nextSlow nextRaw =
      stream semanticSlow (raw.drop used) := by
    rw [sameRaw]
    simp only [stream, bits, hold]
  exact ⟨sameRaw.symm, sameStream, by rwa [sameStream]⟩

#print axioms fast_continuing_future_symbols_transport
end Zlib.Inflate.Proofs
