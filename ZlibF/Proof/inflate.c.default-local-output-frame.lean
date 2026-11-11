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
prefix and its original private footprint. Public temporary cleanup is
outside this source boundary. -/
theorem inflate_default_view_local_exact_frame
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {rc : Int32} {used made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (get : r.get after = some stream) (account : StreamAccounting z stream used made) :
    BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) [⟨z.next_out, made⟩] := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, _used0, made0, _bound, loop, current,
    packet, bits, _sizes, _next, _inputCount, put, left, metadata, outputFrame⟩ :=
    inflate_run_default_view_exact_frame E invariant buffers nonnull inputValid
  have publicCount := account.2.2.2.1
  have baseFrame : BufferFrame h loopHeap (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨z.next_out, made0⟩] := inflate_buffer_frame_mono outputFrame
        (fun _ allowed => allowed.elim Or.inl (fun same => Or.inr (Or.inl same)))
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
    have range : CallerRange h r z.next_out z.avail_out.toNat true := by
      obtain ⟨candidate, candidateGet, _, output, _⟩ := buffers
      have same : candidate = z := Option.some.inj (candidateGet.symm.trans E.hz)
      simpa only [same] using output
    have writable : Writable h z.next_out z.avail_out.toNat := by
      rcases range with null | ⟨_, writable, _⟩
      · exact False.elim (nonnull null)
      · exact writable rfl
    rcases writable with null | ⟨dest, off, array, pointer, originalGet, originalWrite, _room⟩
    · exact False.elim (nonnull null.1)
    obtain ⟨middle, middleGet, _size, _outside⟩ :=
      baseFrame.2 ⟨z.next_out, made0⟩ (by simp) dest off array pointer originalGet
    have put0 : regs.put = .ref dest (off + made0) := by rw [put, pointer]; rfl
    obtain ⟨leaveFrame, finalGet, finalRo⟩ :=
      inflate_leave_output_view_unchanged env0 current allocator0 packet bits run put0 middleGet
    have window := inflate_run_window_unchanged E.strm E.hs current.good.live.hs loop
    have oldLeaveFrame : Frame loopHeap after (fun b => StreamRoot r b ∨ InflateOwned zs s b) := by
      simpa only [InflateOwned, window] using leaveFrame
    have rightFrame := frame_unchanged_view_buffer oldLeaveFrame middleGet finalGet off made0
    have writeMiddle : Space.ro loopHeap dest = false := by
      rw [byte_view_ro_of_ro_eq (congrArg Prod.fst metadata) dest]
      exact originalWrite
    have writeAfter : Space.ro after dest = false := finalRo.trans writeMiddle
    have liveEq : loopHeap.live = h.live := congrArg (fun x => x.2.2.2.2.2.2) metadata
    rw [pointer] at baseFrame
    have complete := BufferFrame.singleton_trans_live baseFrame rightFrame
      (fun b live => by rw [liveEq]; exact live) originalGet writeMiddle writeAfter
    simpa only [pointer, sameMade] using complete

#print axioms inflate_default_view_local_exact_frame
end Zlib.Inflate.Proofs
