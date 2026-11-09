import ZlibF.Proof.«inflate.c.origin-fields-run»
import ZlibF.Proof.«inflate.c.leave-default-boundary»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete post-window suffix retains the full default state
relation and default allocator, on the same checked returning execution. -/
theorem leaveFinalize_default_origin {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (invariant : DefaultOriginState h r zs current s) (allocator : DefAlloc current)
    (output : LeaveOutputView h l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream := by
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨rc, after, stream, state, run, good, frame, views, ret, codes, static⟩ :=
    leaveFinalize_all_wrappers_safe E invariant.good output statics cursor count
  have sizes : ByteViewSizes h after := by
    intro ref
    rw [views ref]
  have finalJ := invariant.toDefaultStateJ.leave_metadata good frame codes (sizes.platform invariant.platform) static
  have final := invariant.of_fields finalJ (by rw [frame]) (by rw [frame]) (by rw [frame])
  have fixed := streamFrameM_leaveFinalize r c l z E.strm h rc after run
  exact ⟨rc, after, stream, state, run, final,
    fixed.allocator invariant.good.live.hz good.live.hz allocator⟩

/-- The real window continuation preserves the stronger origins on success and on genuine
allocation failure. Requested configuration, construction fields and the
allocator remain available for the next public operation. -/
theorem leaveWithWindow_default_origin {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (output : OutputCursorInvariant h r l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream := by
  obtain ⟨ref, bytes, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output invariant.good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  have separate : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
      (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null | ⟨w, a, win, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, win, unowned w win]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) invariant.good allocator.1 get start bound unowned
  obtain ⟨platform, static⟩ := updatewindow_platform_public invariant.good invariant.platform
    allocator.1 get start bound separate windowRun
  have currentJ := invariant.toDefaultStateJ.window_update good1 windowFrame codeViews platform static
  have current := invariant.window_update currentJ windowFrame
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    obtain ⟨rc, after, stream, state, finish, final, finalAllocator⟩ :=
      leaveFinalize_default_origin (z := z) env1 current allocator view cursor count
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact finish
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have good : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have finalJ := current.toDefaultStateJ.mem_update good (platform.with_istates _) rfl
    have final := current.of_fields finalJ rfl rfl rfl
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, final, allocator⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl

/-- The complete actual inf_leave boundary preserves the full default
relation and allocator. No extra mode, wrapper, checksum or allocation
success restriction is imposed at return. -/
theorem inflate_leave_default_origin {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have currentJ := invariant.toDefaultStateJ.restore E buffers bits
  have current := invariant.of_fields currentJ rfl rfl rfl
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport invariant.good current.good rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, final, finalAllocator⟩ :=
      leaveWithWindow_default_origin env0 current allocator output0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, final, finalAllocator⟩ :=
      leaveFinalize_default_origin (z := stream0) env0 current allocator
        (leaveOutputView_of_cursor current.good output0) rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact run

#print axioms inflate_leave_default_origin
end Zlib.Inflate.Proofs
