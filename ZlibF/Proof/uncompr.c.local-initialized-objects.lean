import ZlibF.Proof.«uncompr.c.local-loop-objects»

namespace Zlib.Uncompr.Proof.LocalObjects
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

/-- The same actual core run preserves both original scalar cells. The initial
representation and cell ownership are derived from the real successful init. -/
theorem initialized_loop_cells (h after : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (last : UncLoop) (stream : ZStream) (state : InflateState)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (validOutput : dest = .null → capacity = 0)
    (run : C.run (cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
      { err := Z_OK, len := n, left := capacity })
      (Zlib.Uncompr.Proof.Wrapper.coreHeap h source dest capacity) = .ok (last, after))
    (current : LocalStateJ after h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) stream state) :
    CallerRange after (.tab h.nextBlk) sourceLen 8 true ∧ LengthCell after sourceLen n ∧
    CallerRange after (.tab h.nextBlk) destLen 8 true ∧ LengthCell after destLen capacity := by
  let initialHeap := Zlib.Uncompr.Proof.Wrapper.coreHeap h source dest capacity
  let initialStream := Zlib.Uncompr.Proof.Wrapper.coreStream h source dest capacity
  let initialState := Zlib.Uncompr.Proof.Wrapper.initializedState h
  have initial := LocalDefaultEntry.core_state h source dest capacity fresh allocation globals platform
  have allocator := (LocalInitialization.core_local h source dest capacity fresh allocation).2
  have ranges := Zlib.Uncompr.Proof.LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity xs
    initial.good readable writable separate validOutput
  have nonnull : initialStream.next_out ≠ .null :=
    Zlib.Uncompr.Proof.Wrapper.normalizedDest_nonnull h dest capacity validOutput
  have inputRange := Zlib.Uncompr.Proof.LocalWrapperRanges.core_cell_range h fresh source dest sourceLen capacity n initial.good inputCell
  have outputRange := Zlib.Uncompr.Proof.LocalWrapperRanges.core_cell_range h fresh source dest destLen capacity capacity initial.good outputCell
  have input0 := Zlib.Uncompr.Proof.Wrapper.core_cell h fresh source dest sourceLen capacity n inputCell
  have output0 := Zlib.Uncompr.Proof.Wrapper.core_cell h fresh source dest destLen capacity capacity outputCell
  have inputSeparation : Separate sourceLen 8 initialStream.next_out
      (remainingOutput initialStream { err := Z_OK, len := n, left := capacity }) := by
    simpa [initialStream, remainingOutput, Zlib.Uncompr.Proof.Wrapper.coreStream,
      Zlib.Uncompr.Proof.Wrapper.outputStream] using
      Zlib.Uncompr.Proof.WrapperRanges.separate_normalized h sourceLen dest 8 capacity sourceSeparate validOutput
  have outputSeparation : Separate destLen 8 initialStream.next_out
      (remainingOutput initialStream { err := Z_OK, len := n, left := capacity }) := by
    simpa [initialStream, remainingOutput, Zlib.Uncompr.Proof.Wrapper.coreStream,
      Zlib.Uncompr.Proof.Wrapper.outputStream] using
      Zlib.Uncompr.Proof.WrapperRanges.separate_normalized h destLen dest 8 capacity destSeparate validOutput
  obtain ⟨input1, inputCell1⟩ := loop_go_lengthCell C.fuel initialHeap after h.nextBlk h.nextBlk (h.nextBlk + 2)
    initialStream stream initialState state { err := Z_OK, len := n, left := capacity } last sourceLen n
    initial allocator ranges nonnull inputRange input0 inputSeparation run current
  obtain ⟨output1, outputCell1⟩ := loop_go_lengthCell C.fuel initialHeap after h.nextBlk h.nextBlk (h.nextBlk + 2)
    initialStream stream initialState state { err := Z_OK, len := n, left := capacity } last destLen capacity
    initial allocator ranges nonnull outputRange output0 outputSeparation run current
  exact ⟨input1, inputCell1, output1, outputCell1⟩

/-- The actual automatic reserved object remains allocated and byte-for-byte
unchanged through the core, including its NULL+zero output use. -/
theorem initialized_loop_reserved (h after : Heap) (source dest : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (last : UncLoop) (stream : ZStream) (state : InflateState)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (validOutput : dest = .null → capacity = 0)
    (run : C.run (cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
      { err := Z_OK, len := n, left := capacity })
      (Zlib.Uncompr.Proof.Wrapper.coreHeap h source dest capacity) = .ok (last, after))
    (current : LocalStateJ after h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) stream state) :
    CallerRange after (.tab h.nextBlk) (.ref (.blk (h.nextBlk + 1)) 0) 8 true ∧
    Bytes after (.ref (.blk (h.nextBlk + 1)) 0) 8 (Zlib.Uncompr.Proof.Wrapper.junkBytes h).toList := by
  let initialHeap := Zlib.Uncompr.Proof.Wrapper.coreHeap h source dest capacity
  let initialStream := Zlib.Uncompr.Proof.Wrapper.coreStream h source dest capacity
  let initialState := Zlib.Uncompr.Proof.Wrapper.initializedState h
  have initial := LocalDefaultEntry.core_state h source dest capacity fresh allocation globals platform
  have allocator := (LocalInitialization.core_local h source dest capacity fresh allocation).2
  have ranges := Zlib.Uncompr.Proof.LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity xs
    initial.good readable writable separate validOutput
  have nonnull : initialStream.next_out ≠ .null :=
    Zlib.Uncompr.Proof.Wrapper.normalizedDest_nonnull h dest capacity validOutput
  have object := Zlib.Uncompr.Proof.LocalWrapperRanges.core_reserved_range h source dest capacity 8 true initial.good (by omega)
  have bytes : Bytes initialHeap (.ref (.blk (h.nextBlk + 1)) 0) 8
      (Zlib.Uncompr.Proof.Wrapper.junkBytes h).toList := by
    refine Or.inr ⟨.blk (h.nextBlk + 1), 0, Zlib.Uncompr.Proof.Wrapper.junkBytes h, rfl, ?_, ?_, ?_⟩
    · simp [initialHeap, Space.get, Zlib.Uncompr.Proof.Wrapper.coreHeap_eq]
    · simp [Zlib.Uncompr.Proof.Wrapper.junkBytes]
    · simp [Zlib.Uncompr.Proof.Wrapper.junkBytes]
  have separation : Separate (.ref (.blk (h.nextBlk + 1)) 0) 8 initialStream.next_out
      (remainingOutput initialStream { err := Z_OK, len := n, left := capacity }) := by
    obtain ⟨ys, original⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
    have sep := Zlib.Uncompr.Proof.WrapperRanges.reserved_separate_old h fresh dest capacity.toNat ys original
    simpa [initialStream, remainingOutput, Zlib.Uncompr.Proof.Wrapper.coreStream,
      Zlib.Uncompr.Proof.Wrapper.outputStream] using
      Zlib.Uncompr.Proof.WrapperRanges.separate_normalized h (.ref (.blk (h.nextBlk + 1)) 0) dest 8 capacity sep validOutput
  obtain ⟨object1, bytes1, _⟩ := loop_go_object C.fuel initialHeap after h.nextBlk h.nextBlk (h.nextBlk + 2)
    initialStream stream initialState state { err := Z_OK, len := n, left := capacity } last
    (.ref (.blk (h.nextBlk + 1)) 0) 8 (Zlib.Uncompr.Proof.Wrapper.junkBytes h).toList true
    initial allocator ranges nonnull object bytes separation run current
  exact ⟨object1, bytes1⟩


#print axioms initialized_loop_cells
#print axioms initialized_loop_reserved
end Zlib.Uncompr.Proof.LocalObjects
