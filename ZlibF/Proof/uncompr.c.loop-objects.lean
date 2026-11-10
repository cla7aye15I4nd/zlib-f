import ZlibF.Proof.«uncompr.c.wrapper-ranges»

/-!
# Caller objects across the actual uncompress loop

Exact caller bytes, writable ranges and separation survive every real iteration.
The concrete initialized wrapper therefore preserves both length cells and its
reserved automatic object through the same counted core execution. Late memory
errors may follow partial output; no output-empty premise is used. Ordered scalar
writeback, end cleanup and public functional correctness remain separate.
-/

namespace Zlib.Uncompr.Proof.Objects
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges

private theorem read_range {h : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (range : CallerRange h r p n write) : CallerRange h r p n false := by
  rcases range with null | ⟨readable, _, unowned⟩
  · exact Or.inl null
  · exact Or.inr ⟨readable, by simp, unowned⟩

theorem loopBody_object (h after : Heap) (b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop) (p : BPtr) (n : Nat) (xs : List UInt8) (write : Bool)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (object : CallerRange h (.tab b) p n write) (bytes : Bytes h p n xs)
    (separate : Separate p n z.next_out (remainingOutput z l))
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
    CallerRange after (.tab b) p n write ∧ Bytes after p n xs ∧
    Separate p n stream.next_out (remainingOutput stream next) := by
  obtain ⟨rc, final, z', s', used, output, actual, checked, _finalAllocator,
    account, _observed, _codes, frame, _ledger, _sum, _strict⟩ :=
    loop_iteration_from_ranges h b zs z l s invariant allocator ranges.1 ranges.2.1 ranges.2.2
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have streamEq : z' = stream := Option.some.inj (checked.good.live.hz.symm.trans current.live.hz)
  subst z'
  have filled := refilledDefaultStateJ h b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  have decoderRun := (loopBody_inflate_run h b z l _ after invariant.good.live.hz actual).1
  have owned := inflate_default_view_public_owned_old_blocks filled allocator buffers decoderRun current
  have object0 := callerRange_refill h b z l invariant.good.live.hz p n n write object (Nat.le_refl _)
  have bytes0 : Bytes (refilledHeap h b z l) p n xs := by
    simpa only [Bytes, refill_get] using bytes
  obtain ⟨dest, off, array, ptr, get⟩ : ∃ dest off array,
      z.next_out = .ref dest off ∧ Space.get (refilledHeap h b z l) dest = some array := by
    rcases ranges.2.1 with null | ⟨⟨ys, readable⟩, _⟩
    · exact False.elim (nonnull null)
    · rcases readable with null | ⟨dest, off, array, ptr, get, _⟩
      · exact False.elim (nonnull null.1)
      · exact ⟨dest, off, array, ptr, by rw [refill_get]; exact get⟩
  have count : (refilledLocals z l).left.toNat + stream.avail_out.toNat + output.length =
      remainingOutput z l := by
    have refill := refill_output_count z l
    have out := account.2.2.2.1
    unfold remainingOutput
    omega
  have madeBound : output.length ≤ remainingOutput z l := by omega
  have small := separate_prefix p z.next_out n (remainingOutput z l) n output.length
    separate (Nat.le_refl _) madeBound
  have frame' := frame
  rw [ptr] at frame' small
  have object1 := callerRange_after_bufferFrame filled.good current object0 get frame' owned
    (fun {ref off input} _ _ => Zlib.Inflate.BorrowProofs.inflate_borrow_stable _ _ _ _ _ decoderRun ref)
  have bytes1 := caller_input_bytes_preserved filled.good (read_range object0) get bytes0 small frame'
    (fun {ref off input} _ _ => Zlib.Inflate.BorrowProofs.inflate_borrow_stable _ _ _ _ _ decoderRun ref)
  have cursor : stream.next_out = inputAdvance z.next_out output.length := by
    cases pointer : z.next_out <;>
      simpa only [refilledStream, advance, inputAdvance, pointer] using account.2.2.2.2.2.1
  have remain : remainingOutput stream { refilledLocals z l with err := rc } =
      remainingOutput z l - output.length := by
    simp only [remainingOutput] at count ⊢
    omega
  refine ⟨object1, bytes1, ?_⟩
  have kept := separate_advance_output p z.next_out n (remainingOutput z l) output.length madeBound separate
  simpa only [cursor, remain] using kept

theorem loop_go_object (steps : Nat) (h after : Heap) (b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop) (p : BPtr) (n : Nat) (xs : List UInt8) (write : Bool)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (object : CallerRange h (.tab b) p n write) (bytes : Bytes h p n xs)
    (separate : Separate p n z.next_out (remainingOutput z l))
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
    CallerRange after (.tab b) p n write ∧ Bytes after p n xs ∧
    Separate p n stream.next_out (remainingOutput stream next) := by
  induction steps generalizing h after z stream s state l next with
  | zero => simp [C.run, cdoWhile.go] at run
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, good1, allocator1,
      ranges1, nonnull1, _countIn, _countOut, _progress, _code⟩ :=
      loop_iteration_closed h b zs z s l invariant allocator ranges nonnull
    obtain ⟨range1, bytes1, separate1⟩ := loopBody_object h heap1 b zs z stream1 s state1 l _
      p n xs write invariant allocator ranges nonnull object bytes separate body good1.good
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have tailRun : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps
          { refilledLocals z l with err := rc }) heap1 = .ok (next, after) := by
        simpa [C.run, cdoWhile.go, body', loopCondition, ok] using run
      exact ih heap1 after stream1 stream state1 state { refilledLocals z l with err := rc } next
        good1 allocator1 ranges1 nonnull1 range1 bytes1 separate1 tailRun current
    · have expected : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition (steps + 1) l) h =
          .ok ({ refilledLocals z l with err := rc }, heap1) := by
        simp [C.run, cdoWhile.go, body', loopCondition, ok]
      have same := Except.ok.inj (expected.symm.trans run)
      cases same
      have streamEq : stream1 = stream := Option.some.inj (good1.good.live.hz.symm.trans current.live.hz)
      simpa only [streamEq] using And.intro range1 (And.intro bytes1 separate1)

/-- Scalar cells remain exact through every real core iteration, even when a
late allocation failure follows partial output. No output-empty assumption is used. -/
theorem loop_go_lengthCell (steps : Nat) (h after : Heap) (b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop) (p : BPtr) (value : UInt64)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (object : CallerRange h (.tab b) p 8 true) (cell : LengthCell h p value)
    (separate : Separate p 8 z.next_out (remainingOutput z l))
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
    CallerRange after (.tab b) p 8 true ∧ LengthCell after p value := by
  obtain ⟨range, bytes, _⟩ := loop_go_object steps h after b zs z stream s state l next p 8
    (lengthBytes value) true invariant allocator ranges nonnull object cell.1 separate run current
  refine ⟨range, bytes, ?_⟩
  rcases range with null | ⟨_, writable, _⟩
  · exact False.elim (Zlib.Uncompr.Proof.Wrapper.cell_nonnull h p value cell null)
  · exact writable rfl

/-- The same actual core run preserves both original scalar cells. The initial
representation and cell ownership are derived from the real successful init. -/
theorem initialized_loop_cells (h after : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (last : UncLoop) (stream : ZStream) (state : InflateState)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
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
    (current : Good after (.tab h.nextBlk) (h.nextBlk + 2) stream state) :
    CallerRange after (.tab h.nextBlk) sourceLen 8 true ∧ LengthCell after sourceLen n ∧
    CallerRange after (.tab h.nextBlk) destLen 8 true ∧ LengthCell after destLen capacity := by
  let initialHeap := Zlib.Uncompr.Proof.Wrapper.coreHeap h source dest capacity
  let initialStream := Zlib.Uncompr.Proof.Wrapper.coreStream h source dest capacity
  let initialState := Zlib.Uncompr.Proof.Wrapper.initializedState h
  obtain ⟨initial, allocator⟩ := Zlib.Uncompr.Proof.Wrapper.core_boundary h source dest capacity
    fresh uniq globals platform allocation
  have ranges := Zlib.Uncompr.Proof.WrapperRanges.core_remaining_buffers h fresh source dest n capacity xs
    initial.good readable writable separate validOutput
  have nonnull : initialStream.next_out ≠ .null :=
    Zlib.Uncompr.Proof.Wrapper.normalizedDest_nonnull h dest capacity validOutput
  have inputRange := Zlib.Uncompr.Proof.WrapperRanges.core_cell_range h fresh source dest sourceLen capacity n initial.good inputCell
  have outputRange := Zlib.Uncompr.Proof.WrapperRanges.core_cell_range h fresh source dest destLen capacity capacity initial.good outputCell
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
  obtain ⟨input1, inputCell1⟩ := loop_go_lengthCell C.fuel initialHeap after h.nextBlk (h.nextBlk + 2)
    initialStream stream initialState state { err := Z_OK, len := n, left := capacity } last sourceLen n
    initial allocator ranges nonnull inputRange input0 inputSeparation run current
  obtain ⟨output1, outputCell1⟩ := loop_go_lengthCell C.fuel initialHeap after h.nextBlk (h.nextBlk + 2)
    initialStream stream initialState state { err := Z_OK, len := n, left := capacity } last destLen capacity
    initial allocator ranges nonnull outputRange output0 outputSeparation run current
  exact ⟨input1, inputCell1, output1, outputCell1⟩

/-- The actual automatic reserved object remains allocated and byte-for-byte
unchanged through the core, including its NULL+zero output use. -/
theorem initialized_loop_reserved (h after : Heap) (source dest : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (last : UncLoop) (stream : ZStream) (state : InflateState)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (validOutput : dest = .null → capacity = 0)
    (run : C.run (cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
      { err := Z_OK, len := n, left := capacity })
      (Zlib.Uncompr.Proof.Wrapper.coreHeap h source dest capacity) = .ok (last, after))
    (current : Good after (.tab h.nextBlk) (h.nextBlk + 2) stream state) :
    CallerRange after (.tab h.nextBlk) (.ref (.blk (h.nextBlk + 1)) 0) 8 true ∧
    Bytes after (.ref (.blk (h.nextBlk + 1)) 0) 8 (Zlib.Uncompr.Proof.Wrapper.junkBytes h).toList := by
  let initialHeap := Zlib.Uncompr.Proof.Wrapper.coreHeap h source dest capacity
  let initialStream := Zlib.Uncompr.Proof.Wrapper.coreStream h source dest capacity
  let initialState := Zlib.Uncompr.Proof.Wrapper.initializedState h
  obtain ⟨initial, allocator⟩ := Zlib.Uncompr.Proof.Wrapper.core_boundary h source dest capacity
    fresh uniq globals platform allocation
  have ranges := Zlib.Uncompr.Proof.WrapperRanges.core_remaining_buffers h fresh source dest n capacity xs
    initial.good readable writable separate validOutput
  have nonnull : initialStream.next_out ≠ .null :=
    Zlib.Uncompr.Proof.Wrapper.normalizedDest_nonnull h dest capacity validOutput
  have object := Zlib.Uncompr.Proof.WrapperRanges.core_reserved_range h source dest capacity 8 true initial.good (by omega)
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
  obtain ⟨object1, bytes1, _⟩ := loop_go_object C.fuel initialHeap after h.nextBlk (h.nextBlk + 2)
    initialStream stream initialState state { err := Z_OK, len := n, left := capacity } last
    (.ref (.blk (h.nextBlk + 1)) 0) 8 (Zlib.Uncompr.Proof.Wrapper.junkBytes h).toList true
    initial allocator ranges nonnull object bytes separation run current
  exact ⟨object1, bytes1⟩

#print axioms initialized_loop_reserved
#print axioms loop_go_lengthCell
#print axioms initialized_loop_cells
#print axioms loopBody_object
#print axioms loop_go_object
end Zlib.Uncompr.Proof.Objects
