import ZlibF.Proof.«inflate.c.functional-trailer»
import ZlibF.Proof.«inflate.c.no-allocation-failure-leave»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Observe the actual ordinary window continuation without erasing the
non-window decoder fields retained by its two source stages. -/
theorem leaveWithWindow_causal_frame_of_run
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (actual : leaveWithWindow c l z h = .ok (rc, after))
    (notMemory : rc ≠ Z_MEM_ERROR) (stored : after.istates zs = some state) :
    state = { s with
      window := state.window, wsize := state.wsize, whave := state.whave,
      wnext := state.wnext, total := state.total, check := state.check } := by
  obtain ⟨ref, bytes, off, put, get, _, _room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, _codeViews, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    have separate : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
        (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
      rcases good.inv.win.block with missing | ⟨w, a, win, _, _, _⟩
      · simp [Separate, missing]
      · simp [Separate, win, unowned w win]
    have endpoint : off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat = off :=
      Nat.sub_add_cancel start
    have publicFrame := updatewindow_frame_public (copy := l.out_ - z.avail_out)
      (off := off - (l.out_ - z.avail_out).toNat) good allocator get (by omega) separate
      (by simpa only [C.run, endpoint] using windowRun)
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, publicFrame.1.symm] using statics
    obtain ⟨result, finalHeap, stream, finalState, finish, finalGood, finalFrame,
      _views, _ret, _codes, _static, _streamFields⟩ :=
      leaveFinalize_public_fields (z := z) env1 good1 view statics1 cursor count
    have sameRun : leaveWithWindow c l z h = .ok (result, finalHeap) := by
      unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    have pair := Except.ok.inj (actual.symm.trans sameRun)
    have sameHeap : after = finalHeap := congrArg Prod.snd pair
    subst finalHeap
    have sameState : state = finalState := Option.some.inj (stored.symm.trans finalGood.live.hs)
    subst finalState
    rw [finalFrame, windowFrame]
  · obtain ⟨_, _missing, stateEq, _heapEq⟩ := failure
    subst wr
    subst state1
    have failedRun : leaveWithWindow c l z h =
        .ok (Z_MEM_ERROR, setI heap1 zs { s with mode := MEM }) := by
      unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
        setMode_tab good1.live.hs, pure_app]
    have pair := Except.ok.inj (actual.symm.trans failedRun)
    exact False.elim (notMemory (congrArg Prod.fst pair))

/-- The complete real leave only changes window and accounting fields
after restoring its actual local hold/bits. The conclusion retains all
other decoder fields, including table pointers and pending registers. -/
theorem inflate_leave_causal_frame_of_run
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (current : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39)
    (actual : inflate_leave c l h = .ok (rc, after))
    (notMemory : rc ≠ Z_MEM_ERROR) (stored : after.istates zs = some state) :
    state = { leaveState s l with
      window := state.window, wsize := state.wsize, whave := state.whave,
      wnext := state.wnext, total := state.total, check := state.check } := by
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
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [current0.globals]
    exact ⟨rfl, rfl⟩
  rw [inflate_leave_restore_cut E] at actual
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [leaveAfterRestore_window env0 update] at actual
    exact leaveWithWindow_causal_frame_of_run env0 current0.good allocator.1 output0 statics0
      rfl rfl actual notMemory stored
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases value : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [leaveAfterRestore_no_window env0 skip] at actual
    obtain ⟨result, finalHeap, stream, finalState, finish, finalGood, finalFrame,
      _views, _ret, _codes, _static, _streamFields⟩ :=
      leaveFinalize_public_fields (z := stream0) env0 current0.good
        (leaveOutputView_of_cursor current0.good output0) statics0 rfl rfl
    have pair := Except.ok.inj (actual.symm.trans finish)
    have sameHeap : after = finalHeap := congrArg Prod.snd pair
    subst finalHeap
    have sameState : state = finalState := Option.some.inj (stored.symm.trans finalGood.live.hs)
    subst finalState
    rw [finalFrame]

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs.FunctionalTrailer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

/-- An ordinary complete leave jointly preserves the exact held source
and decoder fields and credits all physically observed output. The actual
allocation oracle excludes lazy-window failure; no successful allocation
or desired callee execution is assumed. -/
theorem leave_from_output_history_no_failure_causal
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (ledger : OutputCredit h z s l prior emitted credited)
    (ret : PublicLeaveRet l) (noFailure : NoAllocationFailure h) :
    ∃ rc after stream state,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      AdlerCredit stream state (prior ++ emitted) ∧ rc ≠ Z_MEM_ERROR ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧
      stream.next_out = l.put ∧ stream.avail_out = l.left ∧
      rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
      state = { leaveState s l with
        window := state.window, wsize := state.wsize, whave := state.whave,
        wnext := state.wnext, total := state.total, check := state.check } := by
  obtain ⟨rc, after, stream, state, actual, current, finalAllocator,
    next, haveField, put, left, notMemory, returnCode, _streamFields, _mode⟩ :=
    inflate_leave_default_no_allocation_failure_accounting E origin.toDefaultStateJ
      allocator packet bits ret noFailure
  have frame := inflate_leave_causal_frame_of_run E origin.toDefaultStateJ allocator
    packet bits actual notMemory current.good.live.hs
  obtain ⟨otherRc, otherHeap, otherStream, otherState, otherRun, otherCurrent,
    _otherAlloc, _otherPut, _otherLeft, credit⟩ :=
    leave_from_output_history E origin allocator packet bits ledger
  have pair := Except.ok.inj (actual.symm.trans otherRun)
  cases pair
  have sameStream : otherStream = stream :=
    Option.some.inj (otherCurrent.good.live.hz.symm.trans current.good.live.hz)
  have sameState : otherState = state :=
    Option.some.inj (otherCurrent.good.live.hs.symm.trans current.good.live.hs)
  subst otherStream otherState
  have fullCredit : AdlerCredit stream state (prior ++ emitted) := by
    rcases credit with ordinary | memory
    · exact ordinary
    · exact False.elim (notMemory memory.1)
  exact ⟨rc, after, stream, state, actual, current, finalAllocator, fullCredit,
    notMemory, next, haveField, put, left, returnCode, frame⟩

#print axioms Zlib.Inflate.Proofs.leaveWithWindow_causal_frame_of_run
#print axioms Zlib.Inflate.Proofs.inflate_leave_causal_frame_of_run
#print axioms leave_from_output_history_no_failure_causal
end Zlib.Inflate.Proofs.FunctionalTrailer
