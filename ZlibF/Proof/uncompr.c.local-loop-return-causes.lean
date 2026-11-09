import ZlibF.Proof.«uncompr.c.local-loop-frame»
import ZlibF.Proof.«uncompr.c.local-pause-public»
import ZlibF.Proof.«uncompr.c.local-return-causes-stream»
import ZlibF.Proof.«uncompr.c.local-return-causes-blocking»
import ZlibF.Proof.«uncompr.c.loop-return-causes»

namespace Zlib.Uncompr.Proof.LocalReturnCauses
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.LocalLoop Zlib.Uncompr.Proof.ReturnCauses
open Zlib.Uncompr.Proof.LocalPause Zlib.Uncompr.Proof.LocalCauses
open Zlib.Uncompr.Proof.LocalBufferBlocking Zlib.Uncompr.Proof.LocalBufferCause
set_option autoImplicit false

private theorem chunk_zero (n : UInt64) (zero : chunk n = 0) : n.toNat = 0 := by
  have actual := chunk_toNat n
  rw [zero] at actual
  change 0 = min n.toNat 4294967295 at actual
  omega

private theorem refilled_zero_remainder (available : UInt32) (remainder : UInt64)
    (zero : (if available == 0 then chunk remainder else available) = 0) :
    (if available == 0 then remainder - (chunk remainder).toUInt64 else remainder).toNat = 0 := by
  by_cases empty : available = 0
  · have zeroChunk : chunk remainder = 0 := by simpa [empty] using zero
    have n := chunk_zero remainder zeroChunk
    have value : remainder = 0 := UInt64.toNat_inj.mp n
    simp [empty, value, chunk]
  · simp [empty] at zero

/-- One real wrapper iteration preserves the mode premise only when its
actual inflate returned OK. A MEM result is a real allocation failure, and
BUF has exhausted one complete outer remainder, not only a UInt32 chunk. -/
theorem loopBody_return_causes (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (inputNull : z.next_in = .null → remainingInput z l = 0) (ready : Ready s)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    next.err ≠ Z_STREAM_ERROR ∧
    (next.err = Z_OK → Ready state) ∧
    (stream.next_in = .null → remainingInput stream next = 0) ∧
    (next.err = Z_MEM_ERROR → AllocationFailed h after) ∧
    (next.err = Z_BUF_ERROR → remainingInput stream next = 0 ∨ remainingOutput stream next = 0) ∧
    h.nalloc ≤ after.nalloc ∧ after.allocOk = h.allocOk := by
  have filled := refilledLocalStateJ h cutoff b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  obtain ⟨actual, lenEq, leftEq⟩ := loopBody_inflate_run h b z l next after invariant.good.live.hz run
  obtain ⟨rc, heap, observed, privateState, used, made, body, j, _, account, _⟩ :=
    loop_iteration_accounting h cutoff b zs z l s invariant allocator ranges.1 ranges.2.1 ranges.2.2
  have same := Except.ok.inj (body.symm.trans run)
  have heaps : heap = after := congrArg Prod.snd same
  have locals : { refilledLocals z l with err := rc } = next := congrArg Prod.fst same
  subst heap
  have streams : observed = stream := Option.some.inj (j.good.live.hz.symm.trans current.live.hz)
  subst observed
  have privateEq : privateState = state := Option.some.inj (j.good.live.hs.symm.trans current.live.hs)
  subst privateState
  have valid := refilled_input_valid z l inputNull
  have nextNotStream := inflate_public_not_stream_error filled allocator buffers Z_NO_FLUSH ready.2 nonnull valid actual
  obtain ⟨_, oracle, _, _, allocations, _⟩ :=
    loopBody_frame h after cutoff b zs z stream s state l next invariant allocator ranges run current
  have oracle : after.allocOk = h.allocOk := oracle.symm
  refine ⟨nextNotStream, ?_, ?_, ?_, ?_, allocations, oracle⟩
  · intro ok
    rw [ok] at actual
    obtain ⟨low, _⟩ := inflate_public_ok_pause filled allocator buffers actual current
    constructor
    · intro equal; rw [equal] at low; exact (by decide : ¬ MEM < MEM) low
    · intro equal; rw [equal] at low; exact (by decide : ¬ SYNC < MEM) low
  · intro null
    have beforeNull : z.next_in = .null := by
      have pointer := account.2.2.2.2.1
      cases initial : z.next_in with
      | null => rfl
      | ref r off => simp [refilledStream, initial, advance] at pointer; rw [null] at pointer; cases pointer
    have oldZero := inputNull beforeNull
    have refill := refill_input_count z l
    have consumed := account.2.2.1
    have newZero : (refilledLocals z l).len.toNat + stream.avail_in.toNat = 0 := by
      unfold remainingInput at oldZero
      omega
    unfold remainingInput
    rw [lenEq]
    exact newZero
  · intro memory
    rw [memory] at actual
    have failed := inflate_public_memory_failure filled allocator buffers Z_NO_FLUSH ready.1 actual
    exact failed
  · intro buffer
    rw [buffer] at actual
    obtain ⟨usedZero, madeZero⟩ := inflate_public_buffer_zero filled allocator buffers actual current account
    have exhausted := inflate_public_buffer_blocked filled allocator buffers actual current account
    have inCount := account.2.2.1
    have outCount := account.2.2.2.1
    rcases exhausted with input | output
    · left
      have rest := refilled_zero_remainder z.avail_in l.len input
      unfold remainingInput
      rw [lenEq]
      change (refilledLocals z l).len.toNat + stream.avail_in.toNat = 0
      change (if z.avail_in == 0 then l.len - (chunk l.len).toUInt64 else l.len).toNat = 0 at rest
      rw [input, usedZero] at inCount
      simp only [UInt32.toNat_zero, Nat.add_zero] at inCount
      simp only [refilledLocals, rest, inCount, Nat.add_zero]
    · right
      have rest := refilled_zero_remainder z.avail_out l.left output
      unfold remainingOutput
      rw [leftEq]
      change (refilledLocals z l).left.toNat + stream.avail_out.toNat = 0
      rw [output, madeZero] at outCount
      simp only [UInt32.toNat_zero, Nat.add_zero] at outCount
      simp only [refilledLocals, rest, outCount, Nat.add_zero]

/-- The actual finite core loop propagates its mode and nullable-input
premises across every successful iteration. Final MEM/BUF causes concern
the same final heap and the complete caller remainders. -/
theorem loop_go_return_causes (steps : Nat) (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (inputNull : z.next_in = .null → remainingInput z l = 0) (ready : Ready s)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    next.err ≠ Z_OK ∧ next.err ≠ Z_STREAM_ERROR ∧
    (next.err = Z_MEM_ERROR → AllocationFailed h after) ∧
    (next.err = Z_BUF_ERROR → remainingInput stream next = 0 ∨ remainingOutput stream next = 0) ∧
    h.nalloc ≤ after.nalloc ∧ after.allocOk = h.allocOk := by
  induction steps generalizing h after z stream s state l next with
  | zero => simp [C.run, cdoWhile.go] at run
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, good1, allocator1,
      ranges1, nonnull1, _⟩ := loop_iteration_closed h cutoff b zs z s l invariant allocator ranges nonnull
    obtain ⟨notStream, ready1, nullable1, memory1, buffer1, allocations1, oracle1⟩ :=
      loopBody_return_causes h heap1 cutoff b zs z stream1 s state1 l _ invariant allocator ranges nonnull
        inputNull ready body good1.good
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have tailRun : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps
          { refilledLocals z l with err := rc }) heap1 = .ok (next, after) := by
        simpa [C.run, cdoWhile.go, body', loopCondition, ok] using run
      obtain ⟨stopped, notStream, memory, buffer, allocations, oracle⟩ :=
        ih heap1 after stream1 stream state1 state { refilledLocals z l with err := rc } next
          good1 allocator1 ranges1 nonnull1 nullable1 (ready1 ok) tailRun current
      refine ⟨stopped, notStream, ?_, buffer, Nat.le_trans allocations1 allocations, oracle.trans oracle1⟩
      intro selected
      obtain ⟨i, lower, upper, failed⟩ := memory selected
      exact ⟨i, Nat.le_trans allocations1 lower, upper, by rw [←oracle1]; exact failed⟩
    · have expected : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition (steps + 1) l) h =
          .ok ({ refilledLocals z l with err := rc }, heap1) := by
        simp [C.run, cdoWhile.go, body', loopCondition, ok]
      have same := Except.ok.inj (expected.symm.trans run)
      cases same
      have streamEq : stream1 = stream := Option.some.inj (good1.good.live.hz.symm.trans current.live.hz)
      subst stream
      exact ⟨ok, notStream, memory1, buffer1, allocations1, oracle1⟩

theorem loop_return_causes (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (inputNull : z.next_in = .null → remainingInput z l = 0) (ready : Ready s)
    (run : C.run (cdoWhile (loopBody (some (.tab b))) loopCondition l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    next.err ≠ Z_OK ∧ next.err ≠ Z_STREAM_ERROR ∧
    (next.err = Z_MEM_ERROR → AllocationFailed h after) ∧
    (next.err = Z_BUF_ERROR → remainingInput stream next = 0 ∨ remainingOutput stream next = 0) ∧
    h.nalloc ≤ after.nalloc ∧ after.allocOk = h.allocOk :=
  loop_go_return_causes C.fuel h after cutoff b zs z stream s state l next
    invariant allocator ranges nonnull inputNull ready run current


#print axioms loopBody_return_causes
#print axioms loop_go_return_causes
#print axioms loop_return_causes
end Zlib.Uncompr.Proof.LocalReturnCauses
