import ZlibF.Proof.«inflate.c.window-state-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual source continuation when inf_leave requests a window update. -/
def leaveWithWindow (c : Ctx) (l : IL) (z : ZStream) : M Int32 := do
  if (← updatewindow c.strm z.next_out (l.out_ - z.avail_out)) != 0 then
    setMode c.st MEM
    return Z_MEM_ERROR
  else
    leaveFinalize c l z

/-- Expose the actual callee and both its return branches. -/
theorem leaveAfterRestore_window {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (update : (s.wsize != 0 || (l.out_ != z.avail_out && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true) :
    leaveAfterRestore c l h = leaveWithWindow c l z h := by
  unfold leaveAfterRestore leaveWithWindow leaveFinalize
  rw [E.strm, E.st]
  simp only [bind_app, ldZ_eq, E.hz, ldI_eq, E.hs, update, ↓reduceIte]

/-- The window-state frame also retains the guarded table clause when its
actual table contents have been retained on the returned heap. -/
theorem WindowStateFrame.tables {h after : Heap} {s state : InflateState}
    (frame : WindowStateFrame s state)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (tables : DataTableInvariant h s) : DataTableInvariant after state := by
  intro active
  have oldActive : DataTableMode s.mode := by rw [frame] at active; exact active
  have safe := tables oldActive
  constructor
  · obtain ⟨ref, off, array, ptr, get, safe⟩ := safe.lengthTable
    exact ⟨ref, off, array, by rw [frame]; exact ptr, by rw [views]; exact get,
      by rw [frame]; exact safe⟩
  · obtain ⟨ref, off, array, ptr, get, safe⟩ := safe.distanceTable
    exact ⟨ref, off, array, by rw [frame]; exact ptr, by rw [views]; exact get,
      by rw [frame]; exact safe⟩

/-- The window branch calls the proved callee, then the proved final suffix.
Allocation failure takes MEM before any public totals are updated. -/
theorem leaveWithWindow_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (output : OutputCursorInvariant h r l) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (hold : s.hold.toNat < 2 ^ s.bits.toNat)
    (flags : s.flags = 0) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
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
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, array, put, sourceView, by rw [count] at start; exact start, bound⟩
    have flags1 : state1.flags = 0 := by rw [windowFrame]; exact flags
    obtain ⟨rc, after, stream, state, finish, finalGood, finalFrame, _, ret, finalCodes, _⟩ :=
      leaveFinalize_view_safe (z := z) env1 good1 view flags1 cursor count
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

/-- The complete actual inf_leave boundary once zlib-wrapper flags = 0 is
established. RESTORE,
window allocation/copy/failure, counters, Adler output, data_type and return
all execute. This retains representation, guarded data tables, pending
symbols and the private bit-buffer bound. Whole-call accounting and frames
remain separate obligations of the enclosing inflate theorem. -/
theorem inflate_leave_zlib_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39) (flags : s.flags = 0) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧
      (rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = leaveStream z l)) := by
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · let stream0 := leaveStream z l
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
    obtain ⟨rc, after, stream, state, run, nextGood, nextTables, nextPending, nextHold, ret⟩ :=
      leaveWithWindow_safe env0 good0 allocator output0 tables0 pending0 hold0 flags rfl rfl
    refine ⟨rc, after, stream, state, ?_, nextGood, nextTables, nextPending, nextHold, ret⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, nextGood, nextTables, nextPending, nextHold, _, ret⟩ :=
      inflate_leave_no_window E good buffers tables pending bits flags skip
    exact ⟨rc, after, stream, state, run, nextGood, nextTables, nextPending, nextHold, Or.inl ret⟩

end Zlib.Inflate.Proofs
