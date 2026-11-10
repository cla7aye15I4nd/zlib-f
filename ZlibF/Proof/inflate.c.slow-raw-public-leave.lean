import ZlibF.Proof.«inflate.c.slow-output-public-source»
import ZlibF.Proof.«inflate.c.slow-public-output-preservation»

namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The real window-update and finalization suffix preserves the complete
persistent fields and held prefix. Its allocation failure remains explicit. -/
theorem leaveWithWindow_fields_raw {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (output : OutputCursorInvariant h r l) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      ((PendingFieldsFrame s state ∧ state.hold = s.hold ∧ state.bits = s.bits ∧
        stream.next_in = z.next_in ∧ stream.avail_in = z.avail_in) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
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
    have endpoint : off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat = off := Nat.sub_add_cancel start
    have publicFrame := updatewindow_frame_public (copy := l.out_ - z.avail_out)
      (off := off - (l.out_ - z.avail_out).toNat) good allocator get (by omega) sep
      (by simpa only [C.run, endpoint] using windowRun)
    have static1 : heap1.static = h.static := publicFrame.1.symm
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, static1] using statics
    obtain ⟨rc, after, stream, state, finish, finalGood, finalFrame, _, _ret, finalCodes, _static, streamFields⟩ :=
      leaveFinalize_public_fields (z := z) env1 good1 view statics1 cursor count
    refine ⟨rc, after, stream, state, ?_, finalGood, finalFrame.tables finalCodes tables1,
      finalFrame.pending pending1, Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    · rw [finalFrame, windowFrame]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [finalFrame, windowFrame]
    · rw [finalFrame, windowFrame]
    · rw [streamFields]
      rfl
    · rw [streamFields]
      rfl
  · obtain ⟨eqrc, _, stateEq, _heapEq⟩ := failure
    subst wr
    subst state1
    let state := {s with mode := MEM}
    have finalGood : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update rfl (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have finalPending : DataPendingInvariant state :=
      dataPendingInvariant_idle pending.sane (by change MEM ≠ LENEXT ∧ MEM ≠ DIST ∧ MEM ≠ DISTEXT ∧ MEM ≠ MATCH; decide)
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, finalGood,
      (by intro active; exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode MEM) active)),
      finalPending, Or.inr ⟨rfl, rfl⟩⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl

/-- Any payload phase crosses the complete public leave path with its
persistent fields and independent unread semantic source, or the real
window allocation reports MEM. No token-specific ghost is required. -/
theorem inflate_leave_source_raw {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {bs : List UInt8} {future residual : List Bool} (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39)
    (source : FutureSource l bs future residual) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      ((PendingFieldsFrame s state ∧
        (natBits state.bits.toNat state.hold.toNat ++ bytesBits bs) ++ future = residual ∧
        stream.next_in = l.next ∧ stream.avail_in = l.have_) ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨good0, pending0, _hold0, _⟩ := leave_restore_invariant E good pending buffers.bits bits
  have env0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have saved : (natBits l.bits.toNat l.hold.toNat ++ bytesBits bs) ++ future = residual := source
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport good good0 rfl views0 (by intro ref; rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  have tables0 := leave_restore_tables (r := r) (z := z) l E.hs tables
  have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by simpa only [Zlib.Crc32.Proofs.StaticsOK, static0] using statics
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, nextGood, nextTables, nextPending, result⟩ :=
      leaveWithWindow_fields_raw env0 good0 allocator output0 tables0 pending0 statics0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, nextGood, nextTables, nextPending, ?_⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
      exact run
    · rcases result with normal | failure
      · obtain ⟨fields, hold, bits, cursor, count⟩ := normal
        exact Or.inl ⟨fields, by rw [hold, bits]; exact saved, cursor, count⟩
      · exact Or.inr failure
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, nextGood, frame, _, _ret, codeViews, _static, streamFields⟩ :=
      leaveFinalize_public_fields (z := stream0) env0 good0 (leaveOutputView_of_cursor good0 output0) statics0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, nextGood, frame.tables codeViews tables0,
      frame.pending pending0, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
      exact run
    · rw [frame]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [frame]
      exact saved
    · rw [streamFields]
      rfl
    · rw [streamFields]
      rfl

/-- The raw full public return also exposes all four caller cursors,
including the actual allocation-failure branch. -/
theorem inflate_leave_source_public {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {future residual : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39)
    (source : FutureSource l bs future residual) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧
      stream.next_out = l.put ∧ stream.avail_out = l.left ∧
      ((PendingFieldsFrame s state ∧
        (natBits state.bits.toNat state.hold.toNat ++ bytesBits bs) ++ future = residual) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  obtain ⟨rc, after, stream, state, actual, current, currentTables, currentPending, outcome⟩ :=
    inflate_leave_source_raw E good allocator statics buffers tables pending bits source
  obtain ⟨next, inputCount, put, left⟩ := inflate_leave_cursors E good pending allocator statics buffers tables bits
    actual current.live.hz
  refine ⟨rc, after, stream, state, actual, current, currentTables, currentPending,
    next, inputCount, put, left, ?_⟩
  rcases outcome with normal | failure
  · exact Or.inl ⟨normal.1, normal.2.1⟩
  · exact Or.inr failure

/-- Every payload phase retains its produced caller output array across
the actual complete leave, with exact source, scalars and caller cursors.
The literal and EOB paths use the same endpoint as copy tokens. -/
theorem inflate_leave_source_array {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {future residual : List Bool}
    {dest : BRef} {off : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39)
    (source : FutureSource l bs future residual)
    (put : l.put = .ref dest off) (get : Space.get h dest = some array) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      Space.get after dest = some array ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧
      stream.next_out = l.put ∧ stream.avail_out = l.left ∧
      ((PendingFieldsFrame s state ∧
        (natBits state.bits.toNat state.hold.toNat ++ bytesBits bs) ++ future = residual) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  obtain ⟨rc, after, stream, state, actual, current, currentTables, currentPending,
    next, inputCount, finalPut, left, outcome⟩ :=
    inflate_leave_source_public E good allocator statics buffers tables pending bits source
  exact ⟨rc, after, stream, state, actual, current, currentTables, currentPending,
    inflate_leave_output_array E good pending allocator buffers bits put get actual,
    next, inputCount, finalPut, left, outcome⟩

#print axioms leaveWithWindow_fields_raw
#print axioms inflate_leave_source_raw
#print axioms inflate_leave_source_public
#print axioms inflate_leave_source_array
end Zlib.Inflate.Proofs.SlowInputFragment
