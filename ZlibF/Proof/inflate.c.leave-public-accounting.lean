import ZlibF.Proof.«inflate.c.leave-all-wrappers»
import ZlibF.Proof.«inflate.c.leave-public-fields»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Execute window update and expose the exact stream record on both
branches. Failure returns before the suffix counter writes. -/
theorem leaveWithWindow_public_accounting {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (output : OutputCursorInvariant h r l) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (hold : s.hold.toNat < 2 ^ s.bits.toNat)
    (statics : Zlib.Crc32.Proofs.StaticsOK h) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧
      ((rc = (if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
        stream = { leaveCountStream z z l with adler := stream.adler, data_type := stream.data_type } ∧
        state.mode = s.mode) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = z)) ∧ after.static = h.static ∧
      state.bits = s.bits := by
  obtain ⟨ref, array, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ array.size := by omega
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  have pending1 := windowFrame.pending pending
  have tables1 := windowFrame.tables codeViews tables
  have hold1 : state1.hold.toNat < 2 ^ state1.bits.toNat := by rw [windowFrame]; exact hold
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, array, put, sourceView, by rw [count] at start; exact start, bound⟩
    have sep : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
        (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
      rcases good.inv.win.block with null | ⟨w, a, win, _, _, _⟩
      · simp [Separate, null]
      · simp [Separate, win, unowned w win]
    have endpoint : off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat = off :=
      Nat.sub_add_cancel start
    have publicFrame := updatewindow_frame_public (copy := l.out_ - z.avail_out)
      (off := off - (l.out_ - z.avail_out).toNat) good allocator get (by omega) sep
      (by simpa only [C.run, endpoint] using windowRun)
    have static1 : heap1.static = h.static := publicFrame.1.symm
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, static1] using statics
    obtain ⟨rc, after, stream, state, finish, finalGood, finalFrame, _, ret, finalCodes, finalStatic, streamFields⟩ :=
      leaveFinalize_public_fields (z := z) env1 good1 view statics1 cursor count
    refine ⟨rc, after, stream, state, ?_, finalGood, finalFrame.tables finalCodes tables1,
      finalFrame.pending pending1, ?_, Or.inl ⟨ret, streamFields, ?_⟩, finalStatic.trans static1, ?_⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    · rw [finalFrame]
      exact hold1
    · rw [finalFrame, windowFrame]
    · rw [finalFrame, windowFrame]
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have finalGood : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have finalPending : DataPendingInvariant state :=
      dataPendingInvariant_idle pending.sane (by change MEM ≠ LENEXT ∧ MEM ≠ DIST ∧ MEM ≠ DISTEXT ∧ MEM ≠ MATCH; decide)
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, finalGood,
      (by intro active; exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode MEM) active)), finalPending, hold, Or.inr ⟨rfl, rfl, rfl⟩, ?_, rfl⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
        setMode_tab good1.live.hs, pure_app]
      rfl
    · rw [heapEq]
      rfl


/-- The actual complete inf_leave exposes restored public cursors and exact
counter writes, or its genuine early window failure with no suffix credit.
The input stream may already contain CHECK output credit. -/
theorem inflate_leave_public_accounting {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧
      ((rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
        stream = { leaveCountStream (leaveStream z l) (leaveStream z l) l with
          adler := stream.adler, data_type := stream.data_type } ∧ state.mode = s.mode) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = leaveStream z l)) ∧ after.static = h.static ∧
      state.bits = l.bits := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨good0, pending0, hold0, _⟩ := leave_restore_invariant E good pending buffers.bits bits
  have env0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport good good0 rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  have tables0 := leave_restore_tables (r := r) (z := z) l E.hs tables
  have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by simpa only [Zlib.Crc32.Proofs.StaticsOK, static0] using statics
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, nextGood, nextTables, nextPending, nextHold, ret, static, bitsEq⟩ :=
      leaveWithWindow_public_accounting env0 good0 allocator output0 tables0 pending0 hold0 statics0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, nextGood, nextTables, nextPending, nextHold, ret, static.trans static0, bitsEq⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, nextGood, frame, _, ret, codeViews, static, streamFields⟩ :=
      leaveFinalize_public_fields (z := stream0) env0 good0 (leaveOutputView_of_cursor good0 output0) statics0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, nextGood, frame.tables codeViews tables0,
      frame.pending pending0, ?_, Or.inl ⟨ret, streamFields, ?_⟩, static.trans static0, ?_⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
      exact run
    · rw [frame]
      exact hold0
    · rw [frame]
      rfl
    · rw [frame]
      rfl

#print axioms leaveWithWindow_public_accounting
#print axioms inflate_leave_public_accounting
end Zlib.Inflate.Proofs
