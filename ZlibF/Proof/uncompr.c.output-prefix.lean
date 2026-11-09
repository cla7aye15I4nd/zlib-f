import ZlibF.Proof.«uncompr.c.loop-resources»
import ZlibF.Proof.«inflate.c.output-frame-live-compose»

namespace Zlib.Uncompr.Proof.OutputPrefix
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.Resources
set_option autoImplicit false

/-- Frames compose across allocation when a later permitted private object
that was already live belongs to the original private footprint. Newly
allocated window objects need not exist in the incoming heap. -/
theorem frame_trans_old_live
    {first second third : Heap} {oldChanged newChanged : Nat → Prop}
    (left : Frame first second oldChanged) (right : Frame second third newChanged)
    (liveNext : ∀ b, first.live b → second.live b)
    (oldPrivate : ∀ b, first.live b → newChanged b → oldChanged b) :
    Frame first third oldChanged := by
  obtain ⟨staticL, allocL, garbageL, nextL, countL, slotsL⟩ := left
  obtain ⟨staticR, allocR, garbageR, nextR, countR, slotsR⟩ := right
  refine ⟨staticL.trans staticR, allocL.trans allocR, garbageL.trans garbageR,
    Nat.le_trans nextL nextR, Nat.le_trans countL countR, ?_⟩
  intro b live outside
  obtain ⟨bL, wL, sL, hL, dL, iL, gL, rL⟩ := slotsL b live outside
  obtain ⟨bR, wR, sR, hR, dR, iR, gR, rR⟩ :=
    slotsR b (liveNext b live) (fun allowed => outside (oldPrivate b live allowed))
  exact ⟨bR.trans bL, wR.trans wL, sR.trans sL, hR.trans hL,
    dR.trans dL, iR.trans iL, gR.trans gL, rR.trans rL⟩

/-- Exact adjacent caller slices compose while the decoder may acquire a
fresh window. The footprint implication is required only on old live objects. -/
theorem output_prefix_trans_old_live
    {first second third : Heap} {oldChanged newChanged : Nat → Prop}
    {dest : BRef} {off a b : Nat} {array : Array UInt8}
    (left : BufferFrame first second oldChanged [⟨.ref dest off, a⟩])
    (right : BufferFrame second third newChanged [⟨.ref dest (off + a), b⟩])
    (liveNext : ∀ root, first.live root → second.live root)
    (oldPrivate : ∀ root, first.live root → newChanged root → oldChanged root)
    (get : Space.get first dest = some array)
    (writeSecond : Space.ro second dest = false) (writeThird : Space.ro third dest = false) :
    BufferFrame first third oldChanged [⟨.ref dest off, a + b⟩] := by
  have firstWide := BufferFrame.singleton_widen left (Nat.le_refl off)
    (by omega : off + a ≤ off + (a + b))
  have secondWide := BufferFrame.singleton_widen right (by omega : off ≤ off + a)
    (by omega : off + a + b ≤ off + (a + b))
  let region : Region := ⟨.ref dest off, a + b⟩
  obtain ⟨middle, middleGet, middleSize, middleOutside⟩ :=
    firstWide.2 region (by simp [region]) dest off array rfl get
  obtain ⟨final, finalGet, finalSize, finalOutside⟩ :=
    secondWide.2 region (by simp [region]) dest off middle rfl middleGet
  have firstFrame : Frame first (Space.put second dest array) oldChanged := by
    simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get] using firstWide.1
  have secondFrame : Frame second (Space.put third dest middle) newChanged := by
    simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, middleGet] using secondWide.1
  have reset := frame_reset_byte_view secondFrame middleGet writeSecond array
  rw [byte_view_put_put finalGet writeThird] at reset
  have resetLive : ∀ root, first.live root → (Space.put second dest array).live root := by
    intro root live
    exact ((byte_view_put_shape middleGet writeSecond array).live root).mpr (liveNext root live)
  have total := frame_trans_old_live firstFrame reset resetLive oldPrivate
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get] using total
  · intro current member ref start old pointer oldGet
    have same : current = region := by simpa only [List.mem_singleton] using member
    subst current
    have ptr : Ptr.ref dest off = Ptr.ref ref start := pointer
    cases ptr
    have oldEq : old = array := Option.some.inj (oldGet.symm.trans get)
    subst old
    refine ⟨final, finalGet, finalSize.trans middleSize, ?_⟩
    intro index bound outside
    exact (finalOutside index (by omega) outside).trans (middleOutside index bound outside)

/-- The real refill changes only the stream record and retains all byte views. -/
theorem refill_record_frame (h : Heap) (b zs : Nat) (z : ZStream) (l : UncLoop)
    (get : h.streams b = some z) :
    RecordFrame (.tab b) (some (.tab zs)) h (refilledHeap h b z l) := by
  have frame := RecordFrame.put_stream (r := .tab b) get (some (.tab zs)) (refilledStream z l)
  simpa only [ZStreamRef.put, refilledHeap, get] using frame

/-- The actual complete caller iteration writes exactly its produced prefix.
The observed count, cursor and memory frame refer to the same real run. -/
theorem loopBody_output
    (h after : Heap) (b zs : Nat) (z stream : ZStream) (s state : InflateState)
    (l next : UncLoop) (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
    ∃ made,
      remainingOutput stream next + made = remainingOutput z l ∧
      stream.next_out = inputAdvance z.next_out made ∧
      BufferFrame h after (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root)
        [⟨z.next_out, made⟩] := by
  obtain ⟨rc, final, z', s', used, output, actual, checked, _finalAllocator,
    account, _observed, _codes, frame, _ledger, _sum, _strict⟩ :=
    loop_iteration_from_ranges h b zs z l s invariant allocator ranges.1 ranges.2.1 ranges.2.2
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have streamEq : z' = stream := Option.some.inj (checked.good.live.hz.symm.trans current.live.hz)
  subst z'
  have count : remainingOutput stream { refilledLocals z l with err := rc } + output.length =
      remainingOutput z l := by
    have refill := refill_output_count z l
    have out := account.2.2.2.1
    change (refilledLocals z l).left.toNat + stream.avail_out.toNat + output.length =
      l.left.toNat + z.avail_out.toNat
    omega
  have cursor : stream.next_out = inputAdvance z.next_out output.length := by
    cases pointer : z.next_out <;>
      simpa only [refilledStream, advance, inputAdvance, pointer] using account.2.2.2.2.2.1
  refine ⟨output.length, count, cursor, ?_⟩
  have preFrame := refill_record_frame h b zs z l invariant.good.live.hz
  have wholeFrame : Frame h (restoreRegions (refilledHeap h b z l) after [⟨z.next_out, output.length⟩])
      (fun root => StreamRoot (.tab b) root ∨ InflateOwned zs s root) := by
    exact frame_trans_live (preFrame.owned_frame s) frame.1
      (fun root live => (preFrame.2.2.1.live root).mpr live)
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, refill_get] using wholeFrame
  · intro region member ref off array pointer get
    exact frame.2 region member ref off array pointer (by rw [refill_get]; exact get)

/-- A nonnull writable remaining output range identifies its current byte
object even when the count is zero. No whole-object shape is required. -/
theorem output_writable_view
    {h : Heap} {b : Nat} {z : ZStream} {l : UncLoop}
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null) :
    ∃ dest off array, z.next_out = .ref dest off ∧ Space.get h dest = some array ∧
      Space.ro h dest = false ∧ off + remainingOutput z l ≤ array.size := by
  rcases ranges.2.1 with null | ⟨_, writable, _⟩
  · exact False.elim (nonnull null)
  · rcases writable rfl with null | ⟨dest, off, array, pointer, get, write, room⟩
    · exact False.elim (nonnull null.1)
    · exact ⟨dest, off, array, pointer, get, write, room⟩

/-- An exact caller output frame preserves the byte object's read-only flag.
Embedded views retain their fixed mutability rule. -/
theorem output_frame_readonly
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {dest : BRef} {array : Array UInt8} {off count made : Nat}
    (good : Good h r zs z s) (get : Space.get h dest = some array)
    (range : CallerRange h r (.ref dest off) count true)
    (frame : BufferFrame h after (fun root => StreamRoot r root ∨ InflateOwned zs s root)
      [⟨.ref dest off, made⟩]) : Space.ro after dest = Space.ro h dest := by
  have readRange : CallerRange h r (.ref dest off) count false := by
    rcases range with null | ⟨bytes, _, outside⟩
    · exact Or.inl null
    · exact Or.inr ⟨bytes, by simp, outside⟩
  cases dest with
  | blk root =>
    have outside := caller_byte_root_outside good get readRange
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
    (steps : Nat) (h after : Heap) (b zs : Nat) (z stream : ZStream)
    (s state : InflateState) (l next : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (run : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after))
    (current : Good after (.tab b) zs stream state) :
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
      loop_iteration_closed h b zs z s l invariant allocator ranges nonnull
    obtain ⟨firstMade, firstCount, firstCursor, firstFrame⟩ :=
      loopBody_output h heap1 b zs z stream1 s state1 l _ invariant allocator ranges body good1.good
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have tailRun : C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps
          { refilledLocals z l with err := rc }) heap1 = .ok (next, after) := by
        simpa [C.run, cdoWhile.go, body', loopCondition, ok] using run
      obtain ⟨restMade, restCount, restCursor, restFrame⟩ :=
        ih heap1 after stream1 stream state1 state { refilledLocals z l with err := rc } next
          good1 allocator1 ranges1 nonnull1 tailRun current
      obtain ⟨ledger, owners⟩ := loopBody_resources h heap1 b zs z stream1 s state1 l _
        invariant allocator ranges body good1.good
      obtain ⟨dest, off, array, pointer, get, write, room⟩ := output_writable_view ranges nonnull
      have outputRange : CallerRange h (.tab b) (.ref dest off) (remainingOutput z l) true := by
        simpa only [pointer, remainingOutput] using ranges.2.1
      have firstFrame' := firstFrame
      rw [pointer] at firstFrame'
      have secondWrite : Space.ro heap1 dest = false :=
        (output_frame_readonly invariant.good get outputRange firstFrame').trans write
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
        (output_frame_readonly good1.good middleGet tailRange restFrame').trans secondWrite
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
end Zlib.Uncompr.Proof.OutputPrefix
