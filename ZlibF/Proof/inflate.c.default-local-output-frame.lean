import ZlibF.Proof.«inflate.c.low-output»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»
import ZlibF.Proof.«inflate.c.default-view-complete-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A real direct return synchronizes the public remaining output count
with the loop register. NEED_DICT performs RESTORE; terminal direct returns
come from their actual initialized entry. -/
theorem inflate_run_direct_output_left {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {regs : IL} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error (.ret rc), regs), after))
    (get : r.get after = some stream) : stream.avail_out = regs.left := by
  have allowed := inflate_run_direct_codes run
  have sync : StreamRegsSync r regs after := by
    rcases allowed with needed | memory | refused
    · exact inflate_run_need_dict_sync E.strm E.st (by simpa only [needed] using run)
    · obtain ⟨original, bindings, _⟩ :=
        inflate_run_terminal_direct E invariant buffers nonnull inputValid local_ run (Or.inl memory)
      exact ⟨z, original, bindings.1.symm, bindings.2.1.symm,
        bindings.2.2.1.symm, bindings.2.2.2.symm⟩
    · obtain ⟨original, bindings, _⟩ :=
        inflate_run_terminal_direct E invariant buffers nonnull inputValid local_ run (Or.inr refused)
      exact ⟨z, original, bindings.1.symm, bindings.2.1.symm,
        bindings.2.2.1.symm, bindings.2.2.2.symm⟩
  obtain ⟨candidate, candidateGet, _, _, _, left⟩ := sync
  have same : candidate = stream := Option.some.inj (candidateGet.symm.trans get)
  simpa only [same] using left

/-- The actual complete returning body, including direct returns, window
allocation failure and checksum suffix, changes only the produced output
prefix, the header record's caller buffers, the call's blocks and the
original private footprint. Public temporary cleanup is outside this source
boundary. -/
theorem inflate_default_view_local_exact_frame
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {rc : Int32} {used made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s)) (facts : CallFrameFacts c h r zs z s)
    (run : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (get : r.get after = some stream) (account : StreamAccounting z stream used made) :
    BufferFrame h after (fun b => CallChanged c r zs s.head b ∨ InflateOwned zs s b)
      (⟨z.next_out, made⟩ :: HeaderRegions h s.head) := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, _used0, made0, _bound, loop, current,
    ⟨_, _, packet⟩, _, bits, _sizes, _next, _inputCount, put, left, metadata, _head, outputFrame⟩ :=
    inflate_run_default_view_exact_frame E invariant buffers nonnull inputValid local_ facts
  have publicCount := account.2.2.2.1
  have baseFrame : BufferFrame h loopHeap (fun b => CallChanged c r zs s.head b ∨ InflateOwned zs s b)
      (⟨z.next_out, made0⟩ :: HeaderRegions h s.head) :=
    BufferFrame.mono_changed outputFrame fun _ inside => Or.inl inside
  rw [bind_app, loop] at run
  cases exit with
  | ret value =>
    change Except.ok (value, loopHeap) = Except.ok (rc, after) at run
    cases run
    have outputLeft := inflate_run_direct_output_left E invariant buffers nonnull inputValid local_ loop get
    rw [outputLeft] at publicCount
    have same : made0 = made := by omega
    simpa only [same] using baseFrame
  | leave =>
    change inflate_leave c regs loopHeap = .ok (rc, after) at run
    have env0 : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have fixed := streamFrameX_inflate_run r c E.strm IL.init h (.error .leave) regs loopHeap loop
    have allocator0 := fixed.allocator E.hz current.good.live.hz allocator
    obtain ⟨rc2, after2, stream2, _state2, leaveRun, finalJ, _, _, _, _, outputLeft, _⟩ :=
      inflate_leave_default_public_accounting env0 current allocator0 packet bits
        (inflate_run_default_low_out E invariant buffers nonnull inputValid local_ loop current.good.live.hs)
    have sameRun := Except.ok.inj (leaveRun.symm.trans run)
    cases sameRun
    have sameStream : stream2 = stream := Option.some.inj (finalJ.good.live.hz.symm.trans get)
    rw [sameStream] at outputLeft
    rw [outputLeft] at publicCount
    have sameMade : made0 = made := by omega
    have leaveFrame := inflate_leave_frame_public env0 current allocator0 packet bits run
    have window := inflate_run_window_unchanged E.strm E.hs current.good.live.hs loop
    have oldLeaveFrame : Frame loopHeap after (fun b => StreamRoot r b ∨ InflateOwned zs s b) := by
      simpa only [InflateOwned, window] using leaveFrame
    have rightFrame : BufferFrame loopHeap after (fun b => CallChanged c r zs s.head b ∨ InflateOwned zs s b) [] := by
      refine ⟨?_, fun _ member => by cases member⟩
      change Frame loopHeap after _
      exact inflate_frame_mono oldLeaveFrame fun _ inside =>
        inside.elim (fun root => Or.inl (Or.inl root)) Or.inr
    have liveEq : loopHeap.live = h.live := congrArg (fun x => x.2.2.2.2.2.2) metadata
    have complete := BufferFrame.trans_within baseFrame rightFrame (RegionsWithin.nil _)
      facts.views.head_length (fun b live => by rw [liveEq]; exact live)
    simpa only [sameMade] using complete

#print axioms inflate_default_view_local_exact_frame
end Zlib.Inflate.Proofs
