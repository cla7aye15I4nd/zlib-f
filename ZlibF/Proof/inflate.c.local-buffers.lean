import ZlibF.Proof.«inflate.c.local-operations»

/-! Buffer-packet preservation from local decoder representation.
These mathematical transports retain the original shared-allocation interval domain. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem callerRange_capacity_local {h after : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (before : LocalGood h first r zs z s) (current : LocalGood after first r zs stream state)
    (window : state.window = s.window) (sizes : ByteViewSizes h after)
    (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    {pointer : BPtr} {size : Nat} {write : Bool} (range : CallerRange h r pointer size write) :
    CallerRange after r pointer size write := by
  rcases range with null | ⟨readable, writable, unowned⟩
  · exact Or.inl null
  · right
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨bytes, bytesRead⟩ := readable
      rcases bytesRead with null | ⟨ref, off, old, ptr, get, fit, _⟩
      · exact ⟨bytes, Or.inl null⟩
      · obtain ⟨array, arrayGet, sizeEq⟩ := sizes.view get
        exact ⟨(array.toList.drop off).take size, Or.inr ⟨ref, off, array, ptr, arrayGet, by omega, rfl⟩⟩
    · intro writing
      rcases writable writing with null | ⟨ref, off, old, ptr, get, ro, fit⟩
      · exact Or.inl null
      · obtain ⟨array, arrayGet, sizeEq⟩ := sizes.view get
        exact Or.inr ⟨ref, off, array, ptr, arrayGet, by rw [readonly]; exact ro, by omega⟩
    · intro b root owned
      apply unowned b root
      rw [current.streamOwned_iff] at owned
      rw [before.streamOwned_iff]
      simpa only [InflateOwned, window] using owned


theorem output_emit_local {h after : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {made : Nat}
    (output : OutputCursorInvariant h r l) (before : LocalGood h first r zs z s)
    (current : LocalGood after first r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (put : regs.put = inputAdvance l.put made) (left : regs.left.toNat + made = l.left.toNat)
    (total : regs.out_ = l.out_) : OutputCursorInvariant after r regs := by
  have bound : made ≤ l.left.toNat := by omega
  have range := callerRange_capacity_local before current window sizes readonly output.range
  have advanced := callerRange_advance range bound
  have remaining : regs.left.toNat = l.left.toNat - made := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [← put, ← remaining] using advanced
  · cases ptr : l.put with
    | null => exact False.elim (output.nonnull ptr)
    | ref ref off => rw [put, ptr]; simp [inputAdvance]
  · rw [total]
    have := output.count
    omega
  · intro ref off ptr
    cases initial : l.put with
    | null => exact False.elim (output.nonnull initial)
    | ref source start =>
      have produced := output.produced source start initial
      rw [put, initial] at ptr
      change Ptr.ref source (start + made) = Ptr.ref ref off at ptr
      cases ptr
      rw [total]
      have := output.count
      omega


theorem dispatch_emit_local {h after : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (buffers : DispatchBuffers h r l bs) (before : LocalGood h first r zs z s)
    (current : LocalGood after first r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (frame : EmitRegFrame l regs) (output : OutputCursorInvariant after r regs)
    (bits : BitInv after regs bs)
    (separate : Separate regs.next regs.have_.toNat regs.put regs.left.toNat) :
    DispatchBuffers after r regs bs := by
  have input := callerRange_capacity_local before current window sizes readonly buffers.input
  refine ⟨?_, output, separate, bits⟩
  rw [frame]
  exact input


theorem dispatch_consume_local {h after : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used : Nat}
    (buffers : DispatchBuffers h r l bs) (before : LocalGood h first r zs z s)
    (current : LocalGood after first r zs stream state) (window : state.window = s.window)
    (views : ∀ ref : BRef, Space.get after ref = Space.get h ref)
    (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (shape : SymbolRegShape l regs) (cursor : regs.next = inputAdvance l.next used)
    (bound : used ≤ bs.length) (bits : BitInv after regs (bs.drop used)) :
    DispatchBuffers after r regs (bs.drop used) := by
  have sizes : ByteViewSizes h after := by intro ref; rw [views]
  have input := callerRange_local_transport before current window views readonly buffers.input
  have advanced := callerRange_advance input (by simpa only [buffers.bits.have_eq] using bound)
  have count : regs.have_.toNat = l.have_.toNat - used := by
    rw [bits.have_eq, buffers.bits.have_eq, List.length_drop]
  have output : OutputCursorInvariant after r regs :=
    output_emit_local buffers.output before current window sizes readonly
      (made := 0) (by rw [shape, inputAdvance_zero]) (by rw [shape]; rfl) (by rw [shape])
  refine ⟨?_, output, ?_, bits⟩
  · simpa only [← cursor, ← count] using advanced
  · have separate := buffers.bits.cursor_separate bits bound cursor buffers.separate
    have put : regs.put = l.put := by rw [shape]
    have left : regs.left = l.left := by rw [shape]
    simpa only [put, left] using separate


theorem dispatch_advance_both_local {h after : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used made : Nat}
    (buffers : DispatchBuffers h r l bs) (before : LocalGood h first r zs z s)
    (current : LocalGood after first r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (next : regs.next = inputAdvance l.next used) (haveCount : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = inputAdvance l.put made) (left : regs.left.toNat + made = l.left.toNat)
    (total : regs.out_ = l.out_) (bits : BitInv after regs (bs.drop used)) :
    DispatchBuffers after r regs (bs.drop used) := by
  have input := callerRange_capacity_local before current window sizes readonly buffers.input
  have inputBound : used ≤ l.have_.toNat := by omega
  have outputBound : made ≤ l.left.toNat := by omega
  have inputAdvance := callerRange_advance input inputBound
  have nextCount : regs.have_.toNat = l.have_.toNat - used := by omega
  have nextLeft : regs.left.toNat = l.left.toNat - made := by omega
  have output := output_emit_local buffers.output before current window sizes readonly put left total
  have separate := inputAdvance_separate l.next l.put l.have_.toNat l.left.toNat used inputBound buffers.separate
  have separate := separate_advance_output _ _ _ _ made outputBound separate
  refine ⟨?_, output, ?_, bits⟩
  · simpa only [← next, ← nextCount] using inputAdvance
  · simpa only [← next, ← put, ← nextCount, ← nextLeft] using separate


#print axioms callerRange_capacity_local
#print axioms output_emit_local
#print axioms dispatch_emit_local
#print axioms dispatch_consume_local
#print axioms dispatch_advance_both_local
end Zlib.Inflate.Local
