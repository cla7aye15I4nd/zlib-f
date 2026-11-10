import ZlibF.Proof.«inflate.c.borrow-stable-run»
import ZlibF.Proof.«uncompr.c.buffers»
import ZlibF.Proof.«inflate.c.owned-old-blocks»

/-!
# Safety and exact counts of the complete uncompress core loop

The actual decoder theorem preserves caller ranges, including a newly allocated
window. A decreasing natural remainder then closes the source cdoWhile with its
fixed fuel. Initialization, scalar writeback, end cleanup and independent format
correctness remain separate wrapper obligations.
-/

namespace Zlib.Uncompr.Proof.PostRanges
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers

private theorem byteRoot_live {h : Heap} {ref : BRef} {off b : Nat} {a : Array UInt8}
    (get : Space.get h ref = some a) (root : ByteRoot (.ref ref off) b) : h.live b := by
  cases ref with
  | blk i =>
    change b = i at root
    subst b
    exact Or.inl (by simp [show h.bytes i = some a from get])
  | dstate_depth i =>
    change b = i at root
    subst b
    cases hg : h.dstates i with
    | none => simp [Space.get, hg] at get
    | some state => simp [Heap.live, hg]
  | str i => cases root
  | st_dist_code => cases root
  | st_length_code => cases root

private theorem byte_put_heap_ro (h : Heap) (ref : BRef) (a : Array UInt8) :
    (Space.put h ref a).ro = h.ro := by
  cases ref <;> simp [Space.put]
  split <;> rfl

private theorem callerRange_read {h : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (range : CallerRange h r p n write) : CallerRange h r p n false := by
  rcases range with null | ⟨readable, _, unowned⟩
  · exact Or.inl null
  · exact Or.inr ⟨readable, by simp, unowned⟩

/-- An exact output frame preserves every caller object's capacity and writability.
Ownership of old live objects is kept explicit, so allocating a new window is included. -/
theorem callerRange_after_bufferFrame
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {p : BPtr} {n : Nat} {write : Bool}
    {dest : BRef} {outOffset made : Nat} {outArray : Array UInt8}
    (good : Good h r zs z s) (current : Good after r zs stream state)
    (range : CallerRange h r p n write) (outputGet : Space.get h dest = some outArray)
    (frame : BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest outOffset, made⟩])
    (oldOwned : ∀ b, h.live b → InflateOwned zs state b → InflateOwned zs s b)
    (stable : ∀ {ref off input}, p = .ref ref off →
      Space.get h ref = some input → C.LibcBorrow.BorrowStable h after ref) :
    CallerRange after r p n write := by
  rcases range with null | ⟨⟨xs, readable⟩, writable, unowned⟩
  · exact Or.inl null
  · rcases readable with null | ⟨source, off, array, pointer, get, room, values⟩
    · exact Or.inl null.1
    · subst p
      have oldRange : CallerRange h r (.ref source off) n false :=
        Or.inr ⟨⟨xs, Or.inr ⟨source, off, array, rfl, get, room, values⟩⟩, by simp, unowned⟩
      have outside := fun b root => caller_byte_root_outside good get oldRange (b := b) root
      obtain ⟨newArray, newGet, sameSize⟩ : ∃ a', Space.get after source = some a' ∧ a'.size = array.size := by
        by_cases shared : source = dest
        · subst source
          obtain ⟨a', hget, hsize, _⟩ := frame.2 ⟨.ref dest outOffset, made⟩ (by simp) dest outOffset array rfl get
          exact ⟨a', hget, hsize⟩
        · exact ⟨array, BufferFrame.other_view_get frame get outputGet outside shared (stable rfl get), rfl⟩
      have roKept : Space.ro after source = Space.ro h source := by
        cases source with
        | blk b =>
          have live := byteRoot_live get (show ByteRoot (.ref (.blk b) off) b from rfl)
          have slot := frame.1.2.2.2.2.2 b live (outside b rfl)
          have restoreRo : (restoreRegions h after [⟨.ref dest outOffset, made⟩]).ro = after.ro := by
            simpa [restoreRegions, outputGet] using byte_put_heap_ro after dest outArray
          change after.ro b = h.ro b
          rw [← restoreRo]
          exact slot.2.2.2.2.2.2.2
        | str i => rfl
        | dstate_depth i => rfl
        | st_dist_code => rfl
        | st_length_code => rfl
      refine Or.inr ⟨⟨(newArray.toList.drop off).take n,
        Or.inr ⟨source, off, newArray, rfl, newGet, by omega, rfl⟩⟩, ?_, ?_⟩
      · intro writing
        rcases writable writing with null | ⟨ref, offset, a, ptr, getA, ro, _⟩
        · cases null.1
        · cases ptr
          exact Or.inr ⟨source, off, newArray, rfl, newGet, roKept.trans ro, by omega⟩
      · intro b root owned
        apply unowned b root
        rw [good.streamOwned_iff]
        exact oldOwned b (byteRoot_live get root) ((current.streamOwned_iff b).mp owned)

/-- Recover the actual decoder call from the exact wrapper-body run. -/
theorem loopBody_inflate_run (h : Heap) (b : Nat) (z : ZStream) (l next : UncLoop)
    (after : Heap) (hz : h.streams b = some z)
    (run : C.run (loopBody (some (.tab b)) l) h = .ok (next, after)) :
    C.run (Zlib.Inflate.inflate (some (.tab b)) Z_NO_FLUSH) (refilledHeap h b z l) =
      .ok (next.err, after) ∧
    next.len = (refilledLocals z l).len ∧ next.left = (refilledLocals z l).left := by
  have he := loopBody_run h b z l hz
  rw [run] at he
  cases hr : Zlib.Inflate.inflate (some (.tab b)) Z_NO_FLUSH
    { h with streams := upd h.streams b (some (refilledStream z l)) } with
  | error fault => simp [hr] at he
  | ok pair =>
      rcases pair with ⟨rc, final⟩
      rw [hr] at he
      cases Except.ok.inj he
      exact ⟨hr, rfl, rfl⟩

def RemainingBuffers (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop) : Prop :=
  CallerRange h (.tab b) z.next_in (l.len.toNat + z.avail_in.toNat) false ∧
  CallerRange h (.tab b) z.next_out (l.left.toNat + z.avail_out.toNat) true ∧
  Separate z.next_in (l.len.toNat + z.avail_in.toNat)
    z.next_out (l.left.toNat + z.avail_out.toNat)

/-- One real iteration preserves all premises needed by its next iteration,
including caller capacities after the decoder allocates its window. -/
theorem loop_iteration_closed (h : Heap) (b zs : Nat) (z : ZStream) (s : InflateState) (l : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null) :
    ∃ rc after stream state used made,
      C.run (loopBody (some (.tab b)) l) h = .ok ({ refilledLocals z l with err := rc }, after) ∧
      DefaultStateJ after (.tab b) zs stream state ∧ DefAlloc stream ∧
      RemainingBuffers after b stream { refilledLocals z l with err := rc } ∧
      stream.next_out ≠ .null ∧
      ((refilledLocals z l).len.toNat + stream.avail_in.toNat) + used =
        l.len.toNat + z.avail_in.toNat ∧
      ((refilledLocals z l).left.toNat + stream.avail_out.toNat) + made =
        l.left.toNat + z.avail_out.toNat ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧ PublicInflateCode rc := by
  obtain ⟨input, output, separate⟩ := ranges
  have filledJ := refilledDefaultStateJ h b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz input output separate
  obtain ⟨rc, after, stream, state, used, bytes, run, current, finalAllocator,
    account, _observed, codes, frame, _ledger, _sum, strict⟩ :=
    loop_iteration_from_ranges h b zs z l s invariant allocator input output separate
  have actual := (loopBody_inflate_run h b z l _ after invariant.good.live.hz run).1
  have owned := inflate_default_view_public_owned_old_blocks filledJ allocator buffers actual current.good
  have input0 := callerRange_refill h b z l invariant.good.live.hz z.next_in
    (l.len.toNat + z.avail_in.toNat) (l.len.toNat + z.avail_in.toNat) false input (Nat.le_refl _)
  have output0 := callerRange_refill h b z l invariant.good.live.hz z.next_out
    (l.left.toNat + z.avail_out.toNat) (l.left.toNat + z.avail_out.toNat) true output (Nat.le_refl _)
  obtain ⟨dest, off, array, ptr, get⟩ : ∃ dest off array,
      z.next_out = .ref dest off ∧ Space.get (refilledHeap h b z l) dest = some array := by
    rcases output with null | ⟨⟨xs, readable⟩, _⟩
    · exact False.elim (nonnull null)
    · rcases readable with null | ⟨dest, off, array, ptr, get, _⟩
      · exact False.elim (nonnull null.1)
      · exact ⟨dest, off, array, ptr, by rw [refill_get]; exact get⟩
  have frame' := frame
  rw [ptr] at frame'
  have inputAfter := callerRange_after_bufferFrame filledJ.good current.good input0 get frame' owned
    (fun {ref off input} _ _ => Zlib.Inflate.BorrowProofs.inflate_borrow_stable _ _ _ _ _ actual ref)
  have outputAfter := callerRange_after_bufferFrame filledJ.good current.good output0 get frame' owned
    (fun {ref off input} _ _ => Zlib.Inflate.BorrowProofs.inflate_borrow_stable _ _ _ _ _ actual ref)
  have inCount : (refilledLocals z l).len.toNat + stream.avail_in.toNat + used =
      l.len.toNat + z.avail_in.toNat := by
    have refill := refill_input_count z l
    have count := account.2.2.1
    omega
  have outCount : (refilledLocals z l).left.toNat + stream.avail_out.toNat + bytes.length =
      l.left.toNat + z.avail_out.toNat := by
    have refill := refill_output_count z l
    have count := account.2.2.2.1
    omega
  have usedBound : used ≤ l.len.toNat + z.avail_in.toNat := by omega
  have madeBound : bytes.length ≤ l.left.toNat + z.avail_out.toNat := by omega
  have inCursor : stream.next_in = inputAdvance z.next_in used := by
    cases pointer : z.next_in <;>
      simpa only [refilledStream, advance, inputAdvance, pointer] using account.2.2.2.2.1
  have outCursor : stream.next_out = inputAdvance z.next_out bytes.length := by
    cases pointer : z.next_out <;>
      simpa only [refilledStream, advance, inputAdvance, pointer] using account.2.2.2.2.2.1
  have inRemain : (refilledLocals z l).len.toNat + stream.avail_in.toNat =
      (l.len.toNat + z.avail_in.toNat) - used := by omega
  have outRemain : (refilledLocals z l).left.toNat + stream.avail_out.toNat =
      (l.left.toNat + z.avail_out.toNat) - bytes.length := by omega
  have remaining : RemainingBuffers after b stream { refilledLocals z l with err := rc } := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [inCursor, inRemain] using callerRange_advance inputAfter usedBound
    · simpa only [outCursor, outRemain] using callerRange_advance outputAfter madeBound
    · have first := inputAdvance_separate z.next_in z.next_out _ _ used usedBound separate
      have second := separate_advance_output (inputAdvance z.next_in used) z.next_out _ _ bytes.length madeBound first
      simpa only [inCursor, outCursor, inRemain, outRemain] using second
  have finalNonnull : stream.next_out ≠ .null := by
    rw [outCursor]
    cases ptr : z.next_out <;> simp [inputAdvance] at nonnull ⊢
    exact False.elim (nonnull ptr)
  refine ⟨rc, after, stream, state, used, bytes.length, run, current, finalAllocator,
    remaining, finalNonnull, inCount, outCount, ?_, codes⟩
  intro ok
  have decreased := strict ok
  omega

def remainingInput (z : ZStream) (l : UncLoop) : Nat := l.len.toNat + z.avail_in.toNat
def remainingOutput (z : ZStream) (l : UncLoop) : Nat := l.left.toNat + z.avail_out.toNat
def remainingBudget (z : ZStream) (l : UncLoop) : Nat := remainingInput z l + remainingOutput z l

/-- The whole actual fueled loop is safe and exits with a non-OK decoder code.
Its input/output counts are exact natural differences. The fuel bound is on
remaining caller bytes, independent of the compressed data's format. -/
theorem loop_go_safe (steps : Nat) (h : Heap) (b zs : Nat) (z : ZStream) (s : InflateState) (l : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (budget : remainingBudget z l < steps) :
    ∃ next after stream state used made,
      C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition steps l) h = .ok (next, after) ∧
      DefaultStateJ after (.tab b) zs stream state ∧ DefAlloc stream ∧
      RemainingBuffers after b stream next ∧ stream.next_out ≠ .null ∧
      next.err ≠ Z_OK ∧ PublicInflateCode next.err ∧
      remainingInput stream next + used = remainingInput z l ∧
      remainingOutput stream next + made = remainingOutput z l := by
  induction steps generalizing h z s l with
  | zero => omega
  | succ steps ih =>
    obtain ⟨rc, heap1, stream1, state1, used, made, body, current, allocator1,
      ranges1, nonnull1, countIn, countOut, progress, code⟩ :=
      loop_iteration_closed h b zs z s l invariant allocator ranges nonnull
    let next := { refilledLocals z l with err := rc }
    have body' := body
    simp only [C.run] at body'
    by_cases ok : rc = Z_OK
    · have strict := progress ok
      have smaller : remainingBudget stream1 next < steps := by
        dsimp only [remainingBudget, remainingInput, remainingOutput, next] at *
        omega
      obtain ⟨final, after, stream, state, consumed, produced, run, finalJ,
        finalAllocator, finalRanges, finalNonnull, stopped, codes, inputs, outputs⟩ :=
        ih heap1 stream1 state1 next current allocator1 ranges1 nonnull1 smaller
      refine ⟨final, after, stream, state, used + consumed, made + produced,
        ?_, finalJ, finalAllocator, finalRanges, finalNonnull, stopped, codes, ?_, ?_⟩
      · have run' := run
        simp only [C.run] at run'
        simpa [C.run, cdoWhile.go, body', loopCondition, next, ok] using run'
      · dsimp only [remainingInput, next] at inputs ⊢
        omega
      · dsimp only [remainingOutput, next] at outputs ⊢
        omega
    · refine ⟨next, heap1, stream1, state1, used, made, ?_, current,
        allocator1, ranges1, nonnull1, ok, code, countIn, countOut⟩
      simp [C.run, cdoWhile.go, body', loopCondition, next, ok]

private theorem callerRange_fits {h : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (range : CallerRange h r p n write)
    (nonnull : p ≠ .null) : n < 2 ^ 63 := by
  rcases range with null | ⟨⟨xs, readable⟩, _⟩
  · exact False.elim (nonnull null)
  · rcases readable with null | ⟨ref, off, array, ptr, get, room, _⟩
    · exact False.elim (nonnull null.1)
    · have bound := platform ref array get
      unfold ZlibF.PlatformMemory.byteObjectLimit at bound
      omega

/-- The actual remaining ranges fit the outer loop's fixed fuel. The null input
binding denotes zero remaining input, as ensured by the wrapper's argument checks. -/
theorem remainingBudget_lt_fuel (h : Heap) (b zs : Nat) (z : ZStream) (s : InflateState) (l : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (ranges : RemainingBuffers h b z l)
    (nonnull : z.next_out ≠ .null) (inputNull : z.next_in = .null → remainingInput z l = 0) :
    remainingBudget z l < C.fuel := by
  have input : remainingInput z l < 2 ^ 63 := by
    by_cases null : z.next_in = .null
    · rw [inputNull null]
      decide
    · exact callerRange_fits invariant.platform ranges.1 null
  have output : remainingOutput z l < 2 ^ 63 :=
    callerRange_fits invariant.platform ranges.2.1 nonnull
  have budget := two_object_loop_budget (remainingInput z l) (remainingOutput z l) input output
  unfold remainingBudget
  omega

/-- The exact source core cdoWhile terminates without a fault on the actual platform
and leaves exact consumed/produced counts, the initialized representation and caller
ranges on one returned heap. This does not assert stream-format correctness. -/
theorem loop_safe (h : Heap) (b zs : Nat) (z : ZStream) (s : InflateState) (l : UncLoop)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null)
    (inputNull : z.next_in = .null → remainingInput z l = 0) :
    ∃ next after stream state used made,
      C.run (cdoWhile (loopBody (some (.tab b))) loopCondition l) h = .ok (next, after) ∧
      DefaultStateJ after (.tab b) zs stream state ∧ DefAlloc stream ∧
      RemainingBuffers after b stream next ∧ stream.next_out ≠ .null ∧
      next.err ≠ Z_OK ∧ PublicInflateCode next.err ∧
      remainingInput stream next + used = remainingInput z l ∧
      remainingOutput stream next + made = remainingOutput z l := by
  exact loop_go_safe C.fuel h b zs z s l invariant allocator ranges nonnull
    (remainingBudget_lt_fuel h b zs z s l invariant ranges nonnull inputNull)

#print axioms loop_iteration_closed
#print axioms loop_go_safe
#print axioms loop_safe

end Zlib.Uncompr.Proof.PostRanges
