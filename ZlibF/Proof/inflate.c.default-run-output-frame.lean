import ZlibF.Proof.«inflate.c.default-loop-output-frame»
import ZlibF.Proof.«inflate.c.default-view-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- TYPE normalization, LOAD and the complete actual default loop preserve
one exact cumulative output frame. This is the real inflate_run body,
before public leave, window update and temporary-storage cleanup. -/
theorem inflate_run_default_view_exact_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s)) (facts : CallFrameFacts c h r zs z s) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      HeaderLocal c after r state regs ∧ regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat ∧
      FastMemoryMetaFrame r h after ∧ state.head = s.head ∧
      BufferFrame h after (CallChanged c r zs s.head) (⟨z.next_out, made⟩ :: HeaderRegions h s.head) := by
  obtain ⟨heap0, state0, bs, entryRun, currentJ, currentEnv, packet, bits, sizes, entryFrame, heapEq,
    stateEq⟩ := inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant currentJ sizes entryFrame heapEq stateEq local_
  have headEq : state0.head = s.head := by rw [entryFrame]
  have regionsEq : HeaderRegions heap0 s.head = HeaderRegions h s.head := by
    rw [heapEq]
    exact HeaderRegions.of_headers _ rfl
  have entryViews : RegionViews (CallChanged c r zs state0.head)
      (⟨(dispatchRegs z state0).put, 0⟩ :: HeaderRegions heap0 state0.head) := by
    rw [headEq, regionsEq]
    exact facts.views
  obtain ⟨exit, regs, after, stream, state, used, made, bound, run, final, finalPacket, finalLocal,
    finalBits, finalSizes, next, count, put, left, loopMetadata, finalHead, frame⟩ :=
    inflate_default_view_frame_loop currentEnv currentJ packet entryLocal bits entryViews
  have actual := entryRun.trans run
  have metadata := fastMemoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs after actual
  rw [headEq, regionsEq] at frame
  have preFrame : BufferFrame h heap0 (CallChanged c r zs s.head) (⟨z.next_out, made⟩ :: HeaderRegions h s.head) := by
    have written := (fastWriteback_heap_frame E.hz E.hs z state0 (⟨z.next_out, made⟩ :: HeaderRegions h s.head)).1
    rw [ZStreamRef.put_self E.hz] at written
    rw [heapEq]
    exact BufferFrame.mono_changed written fun _ view => CallChanged.of_view view
  have liveEntry : ∀ x, h.live x → heap0.live x := by
    intro x alive
    rw [heapEq]
    exact (shape_setI E.hs state0).live x |>.mpr alive
  refine ⟨bs, exit, regs, after, stream, state, used, made, bound, actual,
    final, finalPacket, finalLocal, finalBits, sizes.trans finalSizes, next, count, put, left, metadata,
    finalHead.trans headEq, ?_⟩
  exact BufferFrame.trans_within preFrame frame (RegionsWithin.refl _) facts.views.head_length liveEntry

#print axioms inflate_run_default_view_exact_frame
end Zlib.Inflate.Proofs
