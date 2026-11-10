import ZlibF.Proof.«inflate.c.leave-zero-output-memory»
import ZlibF.Proof.«inflate.c.leave-default-public-accounting»
import ZlibF.Spec.Public.Sequences

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real allocation oracle rules out the only memory-failure branch
of window update. The proof includes first allocation of a lazy window. -/
theorem leaveWithWindow_no_allocation_failure_not_memory
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (output : OutputCursorInvariant h r l)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (ret : PublicLeaveRet l) (noFailure : NoAllocationFailure h)
    (run : leaveWithWindow c l z h = .ok (Z_MEM_ERROR, after)) : False := by
  obtain ⟨ref, array, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ array.size := by omega
  have separate : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
      (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases good.inv.win.block with missing | ⟨w, a, window, _, _, _⟩
    · simp [Separate, missing]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, _, outcome⟩ :=
    updatewindow_safe_public (copy := l.out_ - z.avail_out) good allocator get start bound separate
  rcases outcome with success | failure
  · have zero := success.1
    subst wr
    change updatewindow (some r) (.ref ref off) (l.out_ - z.avail_out) h = .ok (0, heap1) at windowRun
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    exact (leaveFinalize_result c l z ret heap1 Z_MEM_ERROR after run).not_memory rfl
  · exact failure.2.2.1 (noFailure h.nalloc)

/-- RESTORE keeps the allocation oracle unchanged. Thus a fault-free
ordinary decoder exit cannot turn into a window-allocation error when
the caller's original no-failure premise holds. -/
theorem inflate_leave_no_allocation_failure_not_memory
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (pending : DataPendingInvariant s) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) (ret : PublicLeaveRet l)
    (noFailure : NoAllocationFailure h)
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
  have noFailure0 : NoAllocationFailure heap0 := by
    intro n
    simpa only [heap0, setI, ZStreamRef.put_allocOk] using noFailure n
  rw [inflate_leave_restore_cut E] at run
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [leaveAfterRestore_window env0 update] at run
    exact leaveWithWindow_no_allocation_failure_not_memory env0 good0 allocator output0 rfl rfl ret noFailure0 run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases value : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [leaveAfterRestore_no_window env0 skip] at run
    exact (leaveFinalize_result c l stream0 ret heap0 Z_MEM_ERROR after run).not_memory rfl

/-- Under the original completion goal's allocation premise, the actual
whole leave takes its ordinary accounting branch. No successful window
allocation or callee return is assumed. -/
theorem inflate_leave_default_no_allocation_failure_accounting
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (current : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) (ret : PublicLeaveRet l)
    (noFailure : NoAllocationFailure h) :
    ∃ rc after stream state,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧
      stream.next_out = l.put ∧ stream.avail_out = l.left ∧
      rc ≠ Z_MEM_ERROR ∧
      rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
      stream = { leaveCountStream (leaveStream z l) (leaveStream z l) l with
          adler := stream.adler, data_type := stream.data_type } ∧ state.mode = s.mode := by
  obtain ⟨rc, after, stream, state, actual, final, finalAllocator,
    next, haveField, put, left, outcome⟩ :=
    inflate_leave_default_public_accounting E current allocator buffers bits
  have notMemory : rc ≠ Z_MEM_ERROR := by
    intro same
    subst rc
    exact inflate_leave_no_allocation_failure_not_memory E current.good allocator.1
      current.pending buffers bits ret noFailure actual
  rcases outcome with ordinary | memory
  · exact ⟨rc, after, stream, state, actual, final, finalAllocator, next, haveField, put, left,
      notMemory, ordinary⟩
  · exact False.elim (notMemory memory.1)

#print axioms leaveWithWindow_no_allocation_failure_not_memory
#print axioms inflate_leave_no_allocation_failure_not_memory
#print axioms inflate_leave_default_no_allocation_failure_accounting
end Zlib.Inflate.Proofs
