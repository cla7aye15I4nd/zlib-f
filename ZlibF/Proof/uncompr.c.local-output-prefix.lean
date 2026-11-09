import ZlibF.Proof.«uncompr.c.output-prefix»
import ZlibF.Proof.«uncompr.c.local-loop-objects»
import ZlibF.Proof.«inflate.c.local-public-resources-leave-view»

namespace Zlib.Uncompr.Proof.LocalOutputPrefix
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.LocalLoop Zlib.Uncompr.Proof.OutputPrefix
set_option autoImplicit false

/-- The actual complete caller iteration writes exactly its produced prefix,
with the same run, counts and returned local state. -/
theorem loopBody_output
    (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream) (s state : InflateState)
    (l next : UncLoop) (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    ∃ made,
      remainingOutput stream next + made = remainingOutput z l ∧
      stream.next_out = inputAdvance z.next_out made ∧
      BufferFrame h after (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root)
        [⟨z.next_out, made⟩] := by
  obtain ⟨rc, final, z', s', used, made, actual, checked, _finalAllocator,
    account, _codes, _countIn, _countOut, _progress, _strict⟩ :=
    loop_iteration_accounting h cutoff b zs z l s invariant allocator ranges.1 ranges.2.1 ranges.2.2
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have streamEq : z' = stream := Option.some.inj (checked.good.live.hz.symm.trans current.live.hz)
  subst z'
  have count : remainingOutput stream { refilledLocals z l with err := rc } + made =
      remainingOutput z l := by
    have refill := refill_output_count z l
    have out := account.2.2.2.1
    change (refilledLocals z l).left.toNat + stream.avail_out.toNat + made =
      l.left.toNat + z.avail_out.toNat
    omega
  have cursor : stream.next_out = inputAdvance z.next_out made := by
    cases pointer : z.next_out <;>
      simpa only [refilledStream, advance, inputAdvance, pointer] using account.2.2.2.2.2.1
  refine ⟨made, count, cursor, ?_⟩
  have filled := refilledLocalStateJ h cutoff b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  have decoderRun := (loopBody_inflate_run h b z l _ after invariant.good.live.hz actual).1
  have frame := inflate_default_view_public_frame_of_run filled allocator buffers decoderRun current account
  have preFrame := refill_record_frame h b zs z l invariant.good.live.hz
  have wholeFrame : Frame h (restoreRegions (refilledHeap h b z l) after [⟨z.next_out, made⟩])
      (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root) := by
    exact frame_trans_live (preFrame.owned_frame s) frame.1
      (fun root live => (preFrame.2.2.1.live root).mpr live)
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, refill_get] using wholeFrame
  · intro region member ref off array pointer get
    exact frame.2 region member ref off array pointer (by rw [refill_get]; exact get)

/-- An exact caller output frame preserves the byte object's read-only flag.
Embedded views retain their fixed mutability rule. -/
theorem output_frame_readonly
    {h after : Heap} {r : ZStreamRef} {cutoff zs : Nat} {z : ZStream} {s : InflateState}
    {dest : BRef} {array : Array UInt8} {off count made : Nat}
    (good : LocalStateJ h cutoff r zs z s) (get : Space.get h dest = some array)
    (range : CallerRange h r (.ref dest off) count true)
    (frame : BufferFrame h after (fun root => StreamRoot r root ∨ InflateOwned zs s root)
      [⟨.ref dest off, made⟩]) : Space.ro after dest = Space.ro h dest := by
  have readRange : CallerRange h r (.ref dest off) count false := by
    rcases range with null | ⟨bytes, _, outside⟩
    · exact Or.inl null
    · exact Or.inr ⟨bytes, by simp, outside⟩
  cases dest with
  | blk root =>
    have outside := caller_byte_root_outside_writing good get readRange
      (show ByteRoot (.ref (.blk root) off) root from rfl)
    have live : h.live root := Or.inl (by simp [show h.bytes root = some array from get])
    have slots := frame.1.2.2.2.2.2 root live outside
    simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get, Space.put, Space.ro] using slots.2.2.2.2.2.2.2
  | str id => rfl
  | dstate_depth id => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

/-- Every returning actual outer loop writes one contiguous prefix of the
original caller output range. Counts and the final cursor refer to that same
run. New decoder windows remain in scope through old-live ownership facts. -/
theorem loop_go_output_prefix
    (steps : Nat) (h after : Heap) (cutoff b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : LocalGood after cutoff (.tab b) zs stream state) :
    ∃ made,
      remainingOutput stream next + made = remainingOutput z l ∧
      stream.next_out = inputAdvance z.next_out made ∧
      BufferFrame h after (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root)
        [⟨z.next_out, made⟩] := by
  induction steps generalizing h after z stream s state l next with
  | zero => simp [C.run, cdoWhile.go] at run
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, good1, allocator1,
      ranges1, nonnull1, _countIn, _countOut, _progress, _code⟩ :=
      loop_iteration_closed h cutoff b zs z s l invariant allocator ranges nonnull
    obtain ⟨firstMade, firstCount, firstCursor, firstFrame⟩ :=
      loopBody_output h heap1 cutoff b zs z stream1 s state1 l _ invariant allocator ranges body good1.good
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have tailRun : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps
          { refilledLocals z l with err := rc }) heap1 = .ok (next, after) := by
        simpa [C.run, cdoWhile.go, body', loopCondition, ok] using run
      obtain ⟨restMade, restCount, restCursor, restFrame⟩ :=
        ih heap1 after stream1 stream state1 state { refilledLocals z l with err := rc } next
          good1 allocator1 ranges1 nonnull1 tailRun current
      obtain ⟨ledger, owners, _⟩ := loopBody_resources h heap1 cutoff b zs z stream1 s state1 l _
        invariant allocator ranges body good1.good
      obtain ⟨dest, off, array, pointer, get, write, room⟩ := output_writable_view ranges nonnull
      have outputRange : CallerRange h (.tab b) (.ref dest off) (remainingOutput z l) true := by
        simpa only [pointer, remainingOutput] using ranges.2.1
      have firstFrame' := firstFrame
      rw [pointer] at firstFrame'
      have secondWrite : Space.ro heap1 dest = false :=
        (output_frame_readonly invariant get outputRange firstFrame').trans write
      have tailPointer : stream1.next_out = .ref dest (off + firstMade) := by
        rw [firstCursor, pointer]
        rfl
      have restFrame' := restFrame
      rw [tailPointer] at restFrame'
      obtain ⟨middle, middleGet, _middleSize, _⟩ :=
        firstFrame'.2 ⟨.ref dest off, firstMade⟩ (by simp) dest off array rfl get
      have tailRange : CallerRange heap1 (.tab b) (.ref dest (off + firstMade))
          (remainingOutput stream1 { refilledLocals z l with err := rc }) true := by
        simpa only [tailPointer, remainingOutput] using ranges1.2.1
      have thirdWrite : Space.ro after dest = false :=
        (output_frame_readonly good1 middleGet tailRange restFrame').trans secondWrite
      have total := output_prefix_trans_old_live firstFrame' restFrame'
        (fun root live => (ledger root).mpr (Or.inl ⟨live, by simp⟩))
        (fun root live allowed => allowed.elim Or.inl (fun owned => Or.inr ((owners root live).mp owned)))
        get secondWrite thirdWrite
      refine ⟨firstMade + restMade, by omega, ?_, ?_⟩
      · rw [restCursor, firstCursor, inputAdvance_add]
      · simpa only [pointer] using total
    · have expected : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition (steps + 1) l) h =
          .ok ({ refilledLocals z l with err := rc }, heap1) := by
        simp [C.run, cdoWhile.go, body', loopCondition, ok]
      have same := Except.ok.inj (expected.symm.trans run)
      cases same
      have streamEq : stream1 = stream := Option.some.inj (good1.good.live.hz.symm.trans current.live.hz)
      exact ⟨firstMade, by simpa only [streamEq] using firstCount,
        by simpa only [streamEq] using firstCursor, firstFrame⟩

#print axioms loop_go_output_prefix
end Zlib.Uncompr.Proof.LocalOutputPrefix
