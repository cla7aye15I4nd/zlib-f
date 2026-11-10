import ZlibF.Proof.«inflate.c.leave-default-boundary»
import ZlibF.Proof.«inflate.c.stream-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact public cursor/counter fields across the actual window operation
and its two return branches. Genuine allocation failure bypasses counters. -/
theorem leaveWithWindow_stream_fields {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (output : OutputCursorInvariant h r l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧
      ((stream = { leaveCountStream z z l with adler := stream.adler, data_type := stream.data_type } ∧
        state.mode = s.mode ∧ rc = (if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 ||
          c.flush == Z_FINISH) && l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = z)) := by
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
  have current := invariant.window_update good1 windowFrame codeViews platform static
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    have statics : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [current.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rc, after, stream, state, finish, final, finalFrame, fields, ret, mode⟩ :=
      leaveFinalize_stream_fields (z := z) env1 current.good view statics cursor count
    have modeEq : state.mode = s.mode := by rw [mode, windowFrame]
    refine ⟨rc, after, stream, state, ?_, final, Or.inl ⟨fields, modeEq, ret⟩⟩
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
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, good, Or.inr ⟨rfl, rfl, rfl⟩⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl


/-- The complete actual RESTORE/window/metadata boundary writes precisely
the loop cursors. Successful suffixes charge the source counts. A failed
window allocation returns the uncharged restored stream in MEM mode. -/
theorem inflate_leave_stream_fields {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧
      ((stream = { leaveCountStream (leaveStream z l) (leaveStream z l) l with
          adler := stream.adler, data_type := stream.data_type } ∧
        state.mode = s.mode ∧ rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 ||
          c.flush == Z_FINISH) && l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = leaveStream z l)) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have current := invariant.restore E buffers bits
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
  · obtain ⟨rc, after, stream, state, run, good, fields⟩ :=
      leaveWithWindow_stream_fields env0 current allocator output0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, good, fields⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    have statics : Zlib.Crc32.Proofs.StaticsOK heap0 := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [current.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rc, after, stream, state, run, good, frame, fields, ret, mode⟩ :=
      leaveFinalize_stream_fields (z := stream0) env0 current.good
        (leaveOutputView_of_cursor current.good output0) statics rfl rfl
    refine ⟨rc, after, stream, state, ?_, good, Or.inl ⟨fields, mode, ret⟩⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact run

/-- The real complete leave boundary satisfies public cursor/count
accounting relative to the original caller. The incoming cursor equations
are established by the actual mode loop, not by a callee contract. -/
theorem inflate_leave_accounting {c : Ctx} {l : IL} {h source : Heap} {r : ZStreamRef} {zs : Nat}
    {before z : ZStream} {s : InflateState} {bs : List UInt8} {used made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (frame : StreamRootFrame r source h) (beforeGet : r.get source = some before)
    (next : l.next = inputAdvance before.next_in used)
    (input : l.have_.toNat + used = before.avail_in.toNat)
    (put : l.put = inputAdvance before.next_out made)
    (output : l.left.toNat + made = before.avail_out.toNat) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      StreamAccounting before stream used made ∧
      ((stream.total_in = z.total_in + (l.in_ - l.have_).toUInt64 ∧
        stream.total_out = z.total_out + (l.out_ - l.left).toUInt64 ∧
        state.mode = s.mode ∧ rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 ||
          c.flush == Z_FINISH) && l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream.total_in = z.total_in ∧ stream.total_out = z.total_out)) := by
  obtain ⟨rc, after, stream, state, run, good, fields⟩ :=
    inflate_leave_stream_fields E invariant allocator buffers bits
  obtain ⟨rc2, heap2, stream2, state2, run2, final, finalAllocator⟩ :=
    inflate_leave_default_state E invariant allocator buffers bits
  have heaps : after = heap2 := congrArg Prod.snd (Except.ok.inj (run.symm.trans run2))
  subst heap2
  have streams : stream = stream2 := Option.some.inj (good.live.hz.symm.trans final.good.live.hz)
  have states : state = state2 := Option.some.inj (good.live.hs.symm.trans final.good.live.hs)
  subst stream2
  subst state2
  have restored := leaveStream_accounting frame beforeGet invariant.good.live.hz next input put output
  refine ⟨rc, after, stream, state, run, final, finalAllocator, ?_, ?_⟩
  · rcases fields with ⟨fields, mode, ret⟩ | ⟨ret, mode, fields⟩
    · rw [fields]
      exact restored
    · rw [fields]
      exact restored
  · rcases fields with ⟨fields, mode, ret⟩ | ⟨ret, mode, fields⟩
    · refine Or.inl ⟨?_, ?_, mode, ret⟩ <;> rw [fields] <;> rfl
    · refine Or.inr ⟨ret, mode, ?_, ?_⟩ <;> rw [fields] <;> rfl

end Zlib.Inflate.Proofs
