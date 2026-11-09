import ZlibF.Proof.«inflate.c.caller-input-frame»
import ZlibF.Proof.«inflate.c.fast-buffers»
import ZlibF.Proof.«inflate.c.borrowed-view-stability»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The existing view-size observation includes presence. An admitted old
view is readable after the transition, so its borrow is stable. -/
theorem ByteViewSizes.readable_stable {before after : Heap}
    (sizes : ByteViewSizes before after) {ref : BRef} {a : Array UInt8}
    (get : Space.get before ref = some a) : C.LibcBorrow.BorrowStable before after ref := by
  obtain ⟨b, current, _⟩ := sizes.view get
  exact readable_view_stable get current

/-- An actual output frame preserves the unconsumed input bytes after
cursor rollback. The held-bit bound is supplied for the returned registers. -/
theorem BitInv.output_frame_advance
    {before after : Heap} {r : ZStreamRef} {zs writeOff capacity used : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    {dest : BRef} {output : Array UInt8}
    (good : Good before r zs z s) (B : BitInv before l bs)
    (sizes : ByteViewSizes before after)
    (range : CallerRange before r l.next l.have_.toNat false)
    (outputGet : Space.get before dest = some output)
    (separate : Separate l.next l.have_.toNat (.ref dest writeOff) capacity)
    (frame : BufferFrame before after
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest writeOff, capacity⟩])
    (bound : used ≤ bs.length)
    (cursor : regs.next = inputAdvance l.next used)
    (count : regs.have_.toNat + used = l.have_.toNat)
    (held : regs.hold.toNat < 2 ^ regs.bits.toNat) :
    BitInv after regs (bs.drop used) := by
  have retained : BitInv after l bs := by
    refine ⟨B.have_eq, ?_, B.hold_lt⟩
    rcases B.next with empty | ⟨ref, array, off, pointer, get, fit, content⟩
    · exact Or.inl empty
    · have read : Bytes before l.next bs.length bs :=
        Or.inr ⟨ref, off, array, pointer, get, fit, content⟩
      have range' : CallerRange before r l.next bs.length false := by
        simpa only [B.have_eq] using range
      have separate' : Separate l.next bs.length (.ref dest writeOff) capacity := by
        simpa only [B.have_eq] using separate
      have readAfter := caller_input_bytes_preserved good range' outputGet read separate' frame
        (fun _ get => sizes.readable_stable get)
      rcases readAfter with ⟨_, zero, empty⟩ | ⟨ref, off, array, ptr, get, fit, content⟩
      · exact Or.inl empty
      · exact Or.inr ⟨ref, array, off, ptr, get, fit, content⟩
  have advanced := retained.advance_bytes (regs := { regs with hold := l.hold, bits := l.bits })
    bound cursor count rfl rfl
  exact ⟨advanced.have_eq, advanced.next, held⟩

/-- Exact caller byte accounting and the output interval frame retain the
whole dispatch packet on generic input/output views. -/
theorem DispatchBuffers.output_frame_advance
    {before after : Heap} {r : ZStreamRef} {zs used made : Nat}
    {z zNext : ZStream} {s sNext : InflateState} {l regs : IL} {bs : List UInt8}
    {dest : BRef} {writeOff : Nat} {output : Array UInt8}
    (buffers : DispatchBuffers before r l bs)
    (good : Good before r zs z s) (current : Good after r zs zNext sNext)
    (window : sNext.window = s.window)
    (sizes : ByteViewSizes before after)
    (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro before ref)
    (outputPtr : l.put = .ref dest writeOff)
    (outputGet : Space.get before dest = some output)
    (frame : BufferFrame before after
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨l.put, l.left.toNat⟩])
    (next : regs.next = inputAdvance l.next used)
    (haveCount : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = inputAdvance l.put made)
    (left : regs.left.toNat + made = l.left.toNat)
    (total : regs.out_ = l.out_)
    (held : regs.hold.toNat < 2 ^ regs.bits.toNat) :
    DispatchBuffers after r regs (bs.drop used) := by
  have bound : used ≤ bs.length := by rw [← buffers.bits.have_eq]; omega
  have separate : Separate l.next l.have_.toNat (.ref dest writeOff) l.left.toNat := by
    simpa only [outputPtr] using buffers.separate
  have normalizedFrame : BufferFrame before after
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest writeOff, l.left.toNat⟩] := by
    simpa only [outputPtr] using frame
  have bits := buffers.bits.output_frame_advance good sizes buffers.input outputGet
    separate normalizedFrame bound next haveCount held
  exact buffers.advance_both good current window sizes readonly next haveCount
    put left total bits

#print axioms ByteViewSizes.readable_stable
#print axioms BitInv.output_frame_advance
#print axioms DispatchBuffers.output_frame_advance
end Zlib.Inflate.Proofs
