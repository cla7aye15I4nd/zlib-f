import ZlibF.Proof.«inflate.c.caller-buffers»
import ZlibF.Proof.PlatformMemory
import ZlibF.Spec.InflateOutputInvariant

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The buffer clauses carried between actual dispatch iterations. The
bit-source relation records values; caller ranges record capacity and
ownership; separation permits disjoint intervals in the same allocation. -/
structure DispatchBuffers (h : Heap) (r : ZStreamRef) (l : IL) (bs : List UInt8) : Prop where
  input : CallerRange h r l.next l.have_.toNat false
  output : OutputCursorInvariant h r l
  separate : Separate l.next l.have_.toNat l.put l.left.toNat
  bits : BitInv h l bs

/-- Both presence and extent of every represented byte view are retained. -/
def ByteViewSizes (before after : Heap) : Prop :=
  ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)).map Array.size =
    (Space.get before ref : Option (Array UInt8)).map Array.size

theorem ByteViewSizes.refl (h : Heap) : ByteViewSizes h h := fun _ => rfl

theorem ByteViewSizes.symm {before after : Heap} (sizes : ByteViewSizes before after) :
    ByteViewSizes after before := fun ref => (sizes ref).symm

theorem ByteViewSizes.trans {first second third : Heap} (left : ByteViewSizes first second)
    (right : ByteViewSizes second third) : ByteViewSizes first third := fun ref => (right ref).trans (left ref)

theorem ByteViewSizes.view {before after : Heap} (sizes : ByteViewSizes before after)
    {ref : BRef} {old : Array UInt8} (get : Space.get before ref = some old) :
    ∃ array, Space.get after ref = some array ∧ array.size = old.size := by
  have eq := sizes ref
  rw [get] at eq
  cases current : Space.get after ref with
  | none => simp [current] at eq
  | some array => exact ⟨array, rfl, by simpa only [current, Option.map_some, Option.some.injEq] using eq⟩

theorem ByteViewSizes.platform {before after : Heap} (sizes : ByteViewSizes before after)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit before) : ZlibF.PlatformMemory.ByteObjectsFit after := by
  apply fit.of_sizes_le
  intro ref array get
  obtain ⟨old, oldGet, size⟩ := sizes.symm.view get
  exact ⟨old, oldGet, by omega⟩

theorem byte_view_sizes_put {h : Heap} {dest : BRef} {old : Array UInt8}
    (get : Space.get h dest = some old) (write : Space.ro h dest = false)
    (array : Array UInt8) (size : array.size = old.size) : ByteViewSizes h (Space.put h dest array) := by
  intro ref
  by_cases same : ref = dest
  · subst ref
    rw [byte_view_get_put get write, get]
    simp only [Option.map_some, size]
  · rw [byte_view_get_put_ne h same array]

theorem byte_view_sizes_setI (h : Heap) (zs : Nat) (s : InflateState) : ByteViewSizes h (setI h zs s) := by
  intro ref
  rw [byte_view_get_setI]

theorem byte_view_sizes_stream_put (h : Heap) (r : ZStreamRef) (z : ZStream) : ByteViewSizes h (r.put h z) := by
  intro ref
  rw [byte_view_get_stream_put]

theorem byte_view_ro_write (h : Heap) (dest : BRef) (array : Array UInt8) (ref : BRef) :
    Space.ro (Space.put h dest array) ref = Space.ro h ref := by
  cases ref <;> simp only [Space.ro, byte_view_put_ro]

/-- On a good stream the public ownership graph is exactly the actual
inflate state and window. No independent ownership set is assumed. -/
theorem _root_.Zlib.Inflate.Spec.Good.streamOwned_iff {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) (b : Nat) :
    StreamOwned h r b ↔ InflateOwned zs s b := by
  constructor
  · rintro ⟨stream, get, cases⟩
    have sameStream : stream = z := Option.some.inj (get.symm.trans good.live.hz)
    subst stream
    rcases cases with ⟨i, state, kind, live, owned⟩ | ⟨i, state, kind, _, _⟩
    · have sameIndex : i = zs := by
        have eq := kind.symm.trans good.live.zst
        cases eq
        rfl
      subst i
      have sameState : state = s := Option.some.inj (live.symm.trans good.live.hs)
      rwa [sameState] at owned
    · have impossible := kind.symm.trans good.live.zst
      cases impossible
  · intro owned
    exact ⟨z, good.live.hz, Or.inl ⟨zs, s, good.live.zst, good.live.hs, owned⟩⟩

/-- A private decoder update preserves a caller range when its byte views
and window root are unchanged. This transports the public range across
scalar-mode transitions without assuming another API's contract. -/
theorem callerRange_transport {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (before : Good h r zs z s) (current : Good after r zs stream state)
    (window : state.window = s.window)
    (views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref)
    (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    {pointer : BPtr} {size : Nat} {write : Bool} (range : CallerRange h r pointer size write) :
    CallerRange after r pointer size write := by
  rcases range with null | ⟨readable, writable, unowned⟩
  · exact Or.inl null
  · right
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨bytes, bytesRead⟩ := readable
      refine ⟨bytes, ?_⟩
      rcases bytesRead with null | ⟨ref, off, array, ptr, get, fit, contents⟩
      · exact Or.inl null
      · exact Or.inr ⟨ref, off, array, ptr, by rw [views]; exact get, fit, contents⟩
    · intro writing
      rcases writable writing with null | ⟨ref, off, array, ptr, get, ro, fit⟩
      · exact Or.inl null
      · exact Or.inr ⟨ref, off, array, ptr, by rw [views]; exact get,
          by rw [readonly]; exact ro, fit⟩
    · intro b root owned
      apply unowned b root
      rw [current.streamOwned_iff] at owned
      rw [before.streamOwned_iff]
      simpa only [InflateOwned, window] using owned

/-- Byte contents may change while their extents and public ownership
exclusion remain valid. This is the output-range invariant after a write. -/
theorem callerRange_capacity {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (before : Good h r zs z s) (current : Good after r zs stream state)
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

/-- Advancing a public caller range keeps its ownership exclusion and
remaining capacity. Empty and shared-allocation ranges stay in scope. -/
theorem callerRange_advance {h : Heap} {r : ZStreamRef} {pointer : BPtr} {size used : Nat} {write : Bool}
    (range : CallerRange h r pointer size write) (bound : used ≤ size) :
    CallerRange h r (inputAdvance pointer used) (size - used) write := by
  rcases range with null | ⟨readable, writable, unowned⟩
  · subst pointer
    exact Or.inl rfl
  · right
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨bytes, bytesRead⟩ := readable
      rcases bytesRead with ⟨null, zero, _⟩ | ⟨ref, off, array, ptr, get, fit, _⟩
      · subst pointer
        exact ⟨[], Or.inl ⟨rfl, by omega, rfl⟩⟩
      · refine ⟨(array.toList.drop (off + used)).take (size - used), Or.inr ?_⟩
        exact ⟨ref, off + used, array, by rw [ptr]; rfl, get, by omega, rfl⟩
    · intro writing
      rcases writable writing with ⟨null, zero⟩ | ⟨ref, off, array, ptr, get, ro, fit⟩
      · subst pointer
        exact Or.inl ⟨rfl, by omega⟩
      · exact Or.inr ⟨ref, off + used, array, by rw [ptr]; rfl, get, ro, by omega⟩
    · intro b root
      apply unowned b
      cases pointer with
      | null => exact root
      | ref ref off => cases ref <;> exact root

theorem separate_swap (input output : BPtr) (size room : Nat)
    (separate : Separate input size output room) : Separate output room input size := by
  rcases separate with empty | empty | separate
  · exact Or.inr (Or.inl empty)
  · exact Or.inl empty
  · right
    right
    cases input with
    | null => cases output <;> trivial
    | ref ref off =>
      cases output with
      | null => trivial
      | ref dest outOffset =>
        rcases separate with different | before | after
        · exact Or.inl different.symm
        · exact Or.inr (Or.inr before)
        · exact Or.inr (Or.inl after)

theorem separate_advance_output (input output : BPtr) (size room used : Nat)
    (bound : used ≤ room) (separate : Separate input size output room) :
    Separate input size (inputAdvance output used) (room - used) := by
  have swap := separate_swap input output size room separate
  have advanced := inputAdvance_separate output input room size used bound swap
  exact separate_swap (inputAdvance output used) input (room - used) size advanced

/-- Turn the public disjoint-range premise into positions for output writes.
No position restriction is inferred from an empty input range. -/
theorem BitInv.output_positions {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    {dest : BRef} {outOffset : Nat} (put : l.put = .ref dest outOffset) (left : l.left ≠ 0)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat) :
    bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + l.left.toNat ≤ i := by
  by_cases empty : bs = []
  · exact Or.inl empty
  · right
    intro i ptr
    have sep := separate
    rw [ptr, put] at sep
    rcases sep with noInput | noOutput | different | before | later
    · have nil : bs = [] := List.length_eq_zero_iff.mp (B.have_eq.symm.trans noInput)
      exact False.elim (empty nil)
    · exact False.elim (left (UInt32.toNat_inj.mp noOutput))
    · exact False.elim (different rfl)
    · exact Or.inl (by rwa [B.have_eq] at before)
    · exact Or.inr later

theorem BitInv.store_byte {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    {dest : BRef} {output : Array UInt8} {outOffset : Nat} (get : Space.get h dest = some output)
    (write : Space.ro h dest = false) (value : UInt8)
    (separate : bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + 1 ≤ i) :
    BitInv (Space.put h dest (output.set! outOffset value)) l bs := by
  have inv := B.match_copy_ranges get write false #[value] 1 0 outOffset separate
  simpa [ZlibF.Math.InflateMatchCopy.copy_succ, ZlibF.Math.InflateMatchCopy.copy_zero, Array.getD] using inv

/-- A proved output write and cursor advance preserve the common dispatch
clause. Its only heap requirements are preserved byte extents, mutability
and the actual private window root. -/
theorem _root_.Zlib.Inflate.Spec.OutputCursorInvariant.emit {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {made : Nat}
    (output : OutputCursorInvariant h r l) (before : Good h r zs z s)
    (current : Good after r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (put : regs.put = inputAdvance l.put made) (left : regs.left.toNat + made = l.left.toNat)
    (total : regs.out_ = l.out_) : OutputCursorInvariant after r regs := by
  have bound : made ≤ l.left.toNat := by omega
  have range := callerRange_capacity before current window sizes readonly output.range
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

/-- Literal/match emission also preserves the input caller-range clause.
The input pointer/count are retained by the actual emission register frame. -/
theorem DispatchBuffers.emit {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    (buffers : DispatchBuffers h r l bs) (before : Good h r zs z s)
    (current : Good after r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (frame : EmitRegFrame l regs) (output : OutputCursorInvariant after r regs)
    (bits : BitInv after regs bs)
    (separate : Separate regs.next regs.have_.toNat regs.put regs.left.toNat) :
    DispatchBuffers after r regs bs := by
  have input := callerRange_capacity before current window sizes readonly buffers.input
  refine ⟨?_, output, separate, bits⟩
  rw [frame]
  exact input

/-- Reading a symbol advances only the input cursor. Private scalar writes
retain the output range, ownership exclusion and public separation. -/
theorem DispatchBuffers.consume {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used : Nat}
    (buffers : DispatchBuffers h r l bs) (before : Good h r zs z s)
    (current : Good after r zs stream state) (window : state.window = s.window)
    (views : ∀ ref : BRef, Space.get after ref = Space.get h ref)
    (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (shape : SymbolRegShape l regs) (cursor : regs.next = inputAdvance l.next used)
    (bound : used ≤ bs.length) (bits : BitInv after regs (bs.drop used)) :
    DispatchBuffers after r regs (bs.drop used) := by
  have sizes : ByteViewSizes h after := by intro ref; rw [views]
  have input := callerRange_transport before current window views readonly buffers.input
  have advanced := callerRange_advance input (by simpa only [buffers.bits.have_eq] using bound)
  have count : regs.have_.toNat = l.have_.toNat - used := by
    rw [bits.have_eq, buffers.bits.have_eq, List.length_drop]
  have output : OutputCursorInvariant after r regs :=
    buffers.output.emit before current window sizes readonly
      (made := 0) (by rw [shape, inputAdvance_zero]) (by rw [shape]; rfl) (by rw [shape])
  refine ⟨?_, output, ?_, bits⟩
  · simpa only [← cursor, ← count] using advanced
  · have separate := buffers.bits.cursor_separate bits bound cursor buffers.separate
    have put : regs.put = l.put := by rw [shape]
    have left : regs.left = l.left := by rw [shape]
    simpa only [put, left] using separate

end Zlib.Inflate.Proofs
