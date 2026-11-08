import ZlibF.Proof.«inflate.c.leave-result-observer»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Updating an existing window cannot take its allocation-failure return.
The real final suffix also cannot manufacture MEM_ERROR from a public ret. -/
theorem leaveWithWindow_existing_not_memory
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (output : OutputCursorInvariant h r l) (window : s.window ≠ .null)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left) (ret : PublicLeaveRet l)
    (run : leaveWithWindow c l z h = .ok (Z_MEM_ERROR, after)) : False := by
  obtain ⟨ref, array, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ array.size := by omega
  obtain ⟨wr, heap1, state1, windowRun, _, _, _, _, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  rcases outcome with success | failure
  · subst wr
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    have ordinary := leaveFinalize_result c l z ret heap1 Z_MEM_ERROR after run
    exact ordinary.not_memory rfl
  · exact window failure.2.1

/-- If CHECK has rebased the output base to left, a missing window skips
updatewindow. An existing window cannot fail allocation. Thus the actual
leave cannot return MEM_ERROR from that zero-sized suffix segment. -/
theorem inflate_leave_zero_output_not_memory
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (pending : DataPendingInvariant s) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) (ret : PublicLeaveRet l) (zero : l.out_ = l.left)
    (run : inflate_leave c l h = .ok (Z_MEM_ERROR, after)) : False := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨good0, _, _, _⟩ := leave_restore_invariant E good pending buffers.bits bits
  have env0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport good good0 rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  rw [inflate_leave_restore_cut E] at run
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · have window : s.window ≠ .null := by
      intro missing
      have size := good.inv.win.nullws missing
      simp [size, zero] at update
    rw [leaveAfterRestore_window env0 update] at run
    exact leaveWithWindow_existing_not_memory env0 good0 allocator output0 window rfl rfl ret run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases value : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [leaveAfterRestore_no_window env0 skip] at run
    have ordinary := leaveFinalize_result c l stream0 ret heap0 Z_MEM_ERROR after run
    exact ordinary.not_memory rfl

#print axioms inflate_leave_zero_output_not_memory
end Zlib.Inflate.Proofs
