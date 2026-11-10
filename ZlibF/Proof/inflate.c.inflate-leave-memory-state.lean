import ZlibF.Proof.«inflate.c.inflate-leave-code-views»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- MEM can only arise from the actual lazy-window allocation failure.
It writes only mode, before any checksum/final accounting continuation. -/
theorem leaveWithWindow_memory_state_of_run
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (ret : PublicLeaveRet l)
    (actual : leaveWithWindow c l z h = .ok (Z_MEM_ERROR, after)) :
    after.istates zs = some {s with mode := MEM} := by
  obtain ⟨ref, bytes, off, put, get, _, _room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  obtain ⟨wr, heap1, state1, windowRun, good1, _windowFrame, _sourceView, _codeViews, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  rcases outcome with success | failure
  · subst wr
    unfold leaveWithWindow at actual
    rw [bind_app, E.strm, cursor, put, windowRun] at actual
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at actual
    exact ((leaveFinalize_result c l z ret heap1 Z_MEM_ERROR after actual).not_memory rfl).elim
  · obtain ⟨_, _missing, stateEq, _heapEq⟩ := failure
    subst wr
    subst state1
    have failedRun : leaveWithWindow c l z h =
        .ok (Z_MEM_ERROR, setI heap1 zs {s with mode := MEM}) := by
      unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
        setMode_tab good1.live.hs, pure_app]
    have pair := Except.ok.inj (actual.symm.trans failedRun)
    have sameHeap : after = setI heap1 zs {s with mode := MEM} := congrArg Prod.snd pair
    rw [sameHeap, setI_istates_same]

/-- The complete real memory-error return retains the restored source
snapshot exactly, except for its actual mode := MEM assignment. -/
theorem inflate_leave_memory_state_of_run
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (current : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) (ret : PublicLeaveRet l)
    (actual : inflate_leave c l h = .ok (Z_MEM_ERROR, after)) :
    after.istates zs = some {leaveState s l with mode := MEM} := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have current0 := current.restore E buffers bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current0.good.live.hz, current0.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport current.good current0.good rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  rw [inflate_leave_restore_cut E] at actual
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [leaveAfterRestore_window env0 update] at actual
    exact leaveWithWindow_memory_state_of_run env0 current0.good allocator.1 output0 rfl rfl ret actual
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases value : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [leaveAfterRestore_no_window env0 skip] at actual
    exact ((leaveFinalize_result c l stream0 ret heap0 Z_MEM_ERROR after actual).not_memory rfl).elim

#print axioms leaveWithWindow_memory_state_of_run
#print axioms inflate_leave_memory_state_of_run
end Zlib.Inflate.Proofs
