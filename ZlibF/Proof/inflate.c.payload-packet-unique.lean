import ZlibF.Proof.«inflate.c.payload-body-safety-aligned»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A nonempty unread slice is unique at a fixed actual fast pointer and
length. This uses physical array offsets, never byte-value uniqueness. -/
theorem FastInputPacket.unread_unique_of_length
    {h : Heap} {first second : IL} {one two : List UInt8}
    {result : Zlib.Inffast.L}
    (left : FastInputPacket h first one result)
    (right : FastInputPacket h second two result)
    (nonempty : one ≠ []) (lengthEq : one.length = two.length) :
    one = two := by
  have nonempty2 : two ≠ [] := by
    intro empty
    rw [empty] at lengthEq
    cases one with
    | nil => exact nonempty rfl
    | cons _ _ => simp at lengthEq
  rcases left.source.next with empty | ⟨ref1, array1, off1, ptr1, get1, bound1, bytes1⟩
  · exact False.elim (nonempty empty)
  rcases right.source.next with empty | ⟨ref2, array2, off2, ptr2, get2, bound2, bytes2⟩
  · exact False.elim (nonempty2 empty)
  have ptr : (Ptr.ref ref1 off1 : BPtr) = .ref ref2 off2 := by
    calc
      (.ref ref1 off1 : BPtr) = first.next := ptr1.symm
      _ = result.in_ := left.cursor.symm
      _ = second.next := right.cursor
      _ = .ref ref2 off2 := ptr2
  have refEq : ref1 = ref2 := (Ptr.ref.inj ptr).1
  have offEq : off1 = off2 := (Ptr.ref.inj ptr).2
  subst ref2
  subst off2
  have arrayEq : array1 = array2 := Option.some.inj (get1.symm.trans get2)
  subst array2
  rw [bytes1, bytes2, lengthEq]

#print axioms FastInputPacket.unread_unique_of_length
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The immutable `last` pointer fixes the remaining unread length after
an actual body cursor advance. This is the source loop geometry. -/
theorem fast_remaining_length_of_cursor
    {ref : BRef} {off nextOff used : Nat}
    {raw remaining : List UInt8} {last finish : BPtr}
    (rawMargin : 6 ≤ raw.length)
    (nextMargin : 6 ≤ remaining.length)
    (usedBound : used ≤ raw.length)
    (startLast : last = .ref ref (off + raw.length - 5))
    (nextLast : last = .ref ref (nextOff + remaining.length - 5))
    (cursor : finish = inputAdvance (.ref ref off) used)
    (nextCursor : finish = .ref ref nextOff) :
    (raw.drop used).length = remaining.length := by
  have nextOffEq : nextOff = off + used := by
    have same := cursor.symm.trans nextCursor
    change (Ptr.ref ref (off + used) : BPtr) = .ref ref nextOff at same
    exact (Ptr.ref.inj same).2.symm
  have lastOffEq : off + raw.length - 5 =
      nextOff + remaining.length - 5 :=
    (Ptr.ref.inj (startLast.symm.trans nextLast)).2
  rw [List.length_drop]
  omega

#print axioms fast_remaining_length_of_cursor
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A normal fast output write preserves the separately owned saved ring.
The input byte object may still equal the output byte object. -/
theorem fast_window_view_after_output
    {h after : Heap} {c : Zlib.Inffast.Ctx} {dest : BRef}
    {out : Array UInt8} {saved : Array UInt8} {woff : Nat}
    (view : 0 < c.whave.toNat → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size)
    (write : after = Space.put h dest out) :
    0 < c.whave.toNat → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get after window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size := by
  intro positive
  obtain ⟨window, different, ptr, get, bound⟩ := view positive
  refine ⟨window, different, ptr, ?_, bound⟩
  rw [write, byte_view_get_put_ne h different]
  exact get

#print axioms fast_window_view_after_output
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
set_option autoImplicit false

/-- The actual continuing-loop geometry transports an independent parser
residual to the safety loop's next packet, including repeated byte values. -/
theorem fast_continuing_symbols_transport
    {h : Heap} {result : Zlib.Inffast.L}
    {semanticSlow nextSlow : IL}
    {raw nextRaw : List UInt8} {used off nextOff : Nat}
    {inputRef : BRef} {last : BPtr}
    {L D : List Nat} {dict history target : List UInt8}
    {tail : List Bool}
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
      (stream semanticSlow (raw.drop used)) tail target) :
    nextRaw = raw.drop used ∧
      stream nextSlow nextRaw = stream semanticSlow (raw.drop used) ∧
      Symbols L D dict history (stream nextSlow nextRaw) tail target := by
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

#print axioms fast_continuing_symbols_transport
end Zlib.Inflate.Proofs
