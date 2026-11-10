import ZlibF.Proof.«inflate.c.leave-window»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Before a wrapper header is accepted, flags can still be -1. No
checksum callee is invoked when this call has produced no output. -/
theorem leaveChecksum_zero_output {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (zero : l.out_ = z.avail_out) : leaveChecksum c l z h = .ok ((), h) := by
  unfold leaveChecksum
  rw [E.st]
  simp only [bind_app, ldI_eq, E.hs, zero, UInt32.sub_self, bne_self_eq_false,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_app]

/-- The actual complete post-window suffix with zero output needs no
wrapper-flag premise. This covers partial-header exits as well as refused
and empty-output data calls. -/
theorem leaveFinalize_zero_output_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (good : Good h r zs current s) (zero : l.out_ = z.avail_out) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ LeaveMetadataFrame s state ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) ∧
      rc = (if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) := by
  let stream1 := leaveCountStream current z l
  let state1 := leaveCountState s z l
  let heap1 := setI (r.put h stream1) zs state1
  have good1 : Good heap1 r zs stream1 state1 := good.setZI rfl good.live.zalloc good.live.zfree
    rfl good.live.mode (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have env1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
  have checksum := leaveChecksum_zero_output env1 zero
  obtain ⟨dt, _, finish⟩ := leaveReturn_run (l := l) (z := z) env1 good1.inv.bits
  let stream2 := { stream1 with data_type := dt }
  have same : setI (r.put heap1 stream2) zs state1 = r.put heap1 stream2 :=
    tcSetI_same (by simpa using good1.live.hs)
  have finalGood : Good (r.put heap1 stream2) r zs stream2 state1 := by
    have result := good1.setZI (z' := stream2) (st' := state1) rfl good1.live.zalloc good1.live.zfree
      rfl good1.live.mode good1.inv
    rwa [same] at result
  refine ⟨_, r.put heap1 stream2, stream2, state1, ?_, finalGood, by rfl, ?_, rfl, ?_⟩
  · rw [leaveFinalize_split, bind_app, leaveCounters_run E]
    simp only []
    rw [bind_app, checksum]
    exact finish
  · intro ref
    rw [byte_view_get_stream_put, byte_view_get_setI, byte_view_get_stream_put]
  · intro ref
    rw [code_views_put_stream]
    exact leave_metadata_code_views E.hs stream1 (by rfl) ref

/-- Window allocation/copy and the complete suffix with no produced bytes.
No value of the wrapper flags is excluded. -/
theorem leaveWithWindow_zero_output_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (output : OutputCursorInvariant h r l) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (hold : s.hold.toNat < 2 ^ s.bits.toNat)
    (zero : l.out_ = l.left) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧
      (rc = (if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = z)) := by
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
    obtain ⟨rc, after, stream, state, finish, finalGood, finalFrame, _, ret, finalCodes⟩ :=
      leaveFinalize_zero_output_safe (z := z) env1 good1 (zero.trans count.symm)
    refine ⟨rc, after, stream, state, ?_, finalGood, finalFrame.tables finalCodes tables1,
      finalFrame.pending pending1, ?_, Or.inl ret⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    · rw [finalFrame]
      exact hold1
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have finalGood : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have finalPending : DataPendingInvariant state :=
      dataPendingInvariant_idle pending.sane (by change MEM ≠ LENEXT ∧ MEM ≠ DIST ∧ MEM ≠ DISTEXT ∧ MEM ≠ MATCH; decide)
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, finalGood,
      (by intro active; exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode MEM) active)), finalPending, hold, Or.inr ⟨rfl, rfl, rfl⟩⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl


/-- The complete actual return path when no output was produced. In
particular, initial and partial zlib headers may still carry flags = -1.
Both existing-window updates and allocation failure remain covered. -/
theorem inflate_leave_zero_output_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39) (zero : l.out_ = l.left) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧
      (rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = leaveStream z l)) := by
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
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, nextGood, nextTables, nextPending, nextHold, ret⟩ :=
      leaveWithWindow_zero_output_safe env0 good0 allocator output0 tables0 pending0 hold0 zero rfl rfl
    refine ⟨rc, after, stream, state, ?_, nextGood, nextTables, nextPending, nextHold, ret⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, nextGood, frame, _, ret, codeViews⟩ :=
      leaveFinalize_zero_output_safe (z := stream0) env0 good0 zero
    refine ⟨rc, after, stream, state, ?_, nextGood, frame.tables codeViews tables0,
      frame.pending pending0, ?_, Or.inl ret⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
      exact run
    · rw [frame]
      exact hold0

/-- The two default-wrapper return cases share the same boundary relation.
The dispatch relation must establish the flags-or-zero-output clause. -/
theorem inflate_leave_default_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39) (wrapper : s.flags = 0 ∨ l.out_ = l.left) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧
      (rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = leaveStream z l)) := by
  rcases wrapper with flags | zero
  · exact inflate_leave_zlib_boundary E good allocator buffers tables pending bits flags
  · exact inflate_leave_zero_output_boundary E good allocator buffers tables pending bits zero

end Zlib.Inflate.Proofs
