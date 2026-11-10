import ZlibF.Proof.«inflate.c.borrow-stable-run»
import ZlibF.Proof.«uncompr.c.local-loop-safe»
import ZlibF.Proof.«uncompr.c.local-wrapper-ranges»

namespace Zlib.Uncompr.Proof.LocalObjects
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.LocalLoop
set_option autoImplicit false

private theorem read_range {h : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (range : CallerRange h r p n write) : CallerRange h r p n false := by
  rcases range with null | ⟨readable, _, unowned⟩
  · exact Or.inl null
  · exact Or.inr ⟨readable, by simp, unowned⟩

theorem loopBody_object (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop) (p : BPtr) (n : Nat) (xs : List UInt8) (write : Bool)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (object : CallerRange h (.tab b) p n write) (bytes : Bytes h p n xs)
    (separate : Separate p n z.next_out (remainingOutput z l))
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : LocalStateJ after cutoff (.tab b) zs stream state) :
    CallerRange after (.tab b) p n write ∧ Bytes after p n xs ∧
    Separate p n stream.next_out (remainingOutput stream next) := by
  obtain ⟨rc, final, z', s', used, made, actual, checked, _finalAllocator,
    account, _codes, _countIn, _countOut, _progress, _strict⟩ :=
    loop_iteration_accounting h cutoff b zs z l s invariant allocator ranges.1 ranges.2.1 ranges.2.2
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have streamEq : z' = stream := Option.some.inj (checked.good.live.hz.symm.trans current.good.live.hz)
  subst z'
  have filled := refilledLocalStateJ h cutoff b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  have decoderRun := (loopBody_inflate_run h b z l _ after invariant.good.live.hz actual).1
  have frame := inflate_default_view_public_frame_of_run filled allocator buffers decoderRun current.good account
  change BufferFrame (refilledHeap h b z l) after
    (fun x => StreamRoot (.tab b) x ∨ InflateOwned zs s x) [⟨z.next_out, made⟩] at frame
  -- Use the state from this exact actual call, not an unrelated witness.
  have origin' : state.window = s.window ∨
      (s.window = .null ∧ state.window = .ref (.blk ((refilledHeap h b z l).nextBlk + 1)) 0) := by
    obtain ⟨rc2, heap2, z2, s2, actual2, current2, _, _, update, _, _, origin2⟩ :=
      inflate_default_view_public_origins filled allocator buffers Z_NO_FLUSH
    have same2 := Except.ok.inj (actual2.symm.trans decoderRun)
    cases same2
    have sameState : s2 = state := Option.some.inj (current2.good.live.hs.symm.trans current.good.live.hs)
    simpa only [sameState] using origin2
  have owned0 := public_owned_old_iff_of_origin (zs := zs) filled.good.fresh origin'
  have owned (x : Nat) (live : (refilledHeap h b z l).live x)
      (owner : InflateOwned zs state x) : InflateOwned zs s x := (owned0 x live).mp owner
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
  have count : (refilledLocals z l).left.toNat + stream.avail_out.toNat + made =
      remainingOutput z l := by
    have refill := refill_output_count z l
    have out := account.2.2.2.1
    unfold remainingOutput
    omega
  have madeBound : made ≤ remainingOutput z l := by omega
  have small := separate_prefix p z.next_out n (remainingOutput z l) n made
    separate (Nat.le_refl _) madeBound
  have frame' := frame
  rw [ptr] at frame' small
  have object1 := LocalPostRanges.callerRange_after_bufferFrame filled current object0 get frame' owned
    (fun {ref off input} _ _ => Zlib.Inflate.BorrowProofs.inflate_borrow_stable _ _ _ _ _ decoderRun ref)
  have bytes1 := Zlib.Inflate.Local.caller_input_bytes_preserved filled (read_range object0) get bytes0 small frame'
    (fun {ref off input} _ _ => Zlib.Inflate.BorrowProofs.inflate_borrow_stable _ _ _ _ _ decoderRun ref)
  have cursor : stream.next_out = inputAdvance z.next_out made := by
    cases pointer : z.next_out <;>
      simpa only [refilledStream, advance, inputAdvance, pointer] using account.2.2.2.2.2.1
  have remain : remainingOutput stream { refilledLocals z l with err := rc } =
      remainingOutput z l - made := by
    simp only [remainingOutput] at count ⊢
    omega
  refine ⟨object1, bytes1, ?_⟩
  have kept := separate_advance_output p z.next_out n (remainingOutput z l) made madeBound separate
  simpa only [cursor, remain] using kept

theorem loop_go_object (steps : Nat) (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop) (p : BPtr) (n : Nat) (xs : List UInt8) (write : Bool)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (object : CallerRange h (.tab b) p n write) (bytes : Bytes h p n xs)
    (separate : Separate p n z.next_out (remainingOutput z l))
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : LocalStateJ after cutoff (.tab b) zs stream state) :
    CallerRange after (.tab b) p n write ∧ Bytes after p n xs ∧
    Separate p n stream.next_out (remainingOutput stream next) := by
  induction steps generalizing h after z stream s state l next with
  | zero => simp [C.run, cdoWhile.go] at run
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, good1, allocator1,
      ranges1, nonnull1, _countIn, _countOut, _progress, _code⟩ :=
      loop_iteration_closed h cutoff b zs z s l invariant allocator ranges nonnull
    obtain ⟨range1, bytes1, separate1⟩ := loopBody_object h heap1 cutoff b zs z stream1 s state1 l _
      p n xs write invariant allocator ranges nonnull object bytes separate body good1
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
      have streamEq : stream1 = stream := Option.some.inj (good1.good.live.hz.symm.trans current.good.live.hz)
      simpa only [streamEq] using And.intro range1 (And.intro bytes1 separate1)

/-- Scalar cells remain exact through every real core iteration, even when a
late allocation failure follows partial output. No output-empty assumption is used. -/
theorem loop_go_lengthCell (steps : Nat) (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop) (p : BPtr) (value : UInt64)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (object : CallerRange h (.tab b) p 8 true) (cell : LengthCell h p value)
    (separate : Separate p 8 z.next_out (remainingOutput z l))
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : LocalStateJ after cutoff (.tab b) zs stream state) :
    CallerRange after (.tab b) p 8 true ∧ LengthCell after p value := by
  obtain ⟨range, bytes, _⟩ := loop_go_object steps h after cutoff b zs z stream s state l next p 8
    (lengthBytes value) true invariant allocator ranges nonnull object cell.1 separate run current
  refine ⟨range, bytes, ?_⟩
  rcases range with null | ⟨_, writable, _⟩
  · exact False.elim (Zlib.Uncompr.Proof.Wrapper.cell_nonnull h p value cell null)
  · exact writable rfl


#print axioms loopBody_object
#print axioms loop_go_object
#print axioms loop_go_lengthCell
end Zlib.Uncompr.Proof.LocalObjects
