import ZlibF.Proof.«inflate.c.leave-causal-frame»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual lazy-window continuation retains every code-array view,
including allocation failure and its real MEM state write. -/
theorem leaveWithWindow_code_views_of_run
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (actual : leaveWithWindow c l z h = .ok (rc, after)) :
    ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref := by
  obtain ⟨ref, bytes, off, put, get, _, _room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  obtain ⟨wr, heap1, state1, windowRun, good1, _windowFrame, sourceView, codeViews, outcome⟩ :=
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
    obtain ⟨result, finalHeap, stream, finalState, finish, _finalGood, _finalFrame,
      _views, _ret, finalCodes, _static, _streamFields⟩ :=
      leaveFinalize_public_fields (z := z) env1 good1 view statics1 cursor count
    have sameRun : leaveWithWindow c l z h = .ok (result, finalHeap) := by
      unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    have pair := Except.ok.inj (actual.symm.trans sameRun)
    have sameHeap : after = finalHeap := congrArg Prod.snd pair
    subst finalHeap
    intro ref
    exact (finalCodes ref).trans (codeViews ref)
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
    have sameHeap : after = setI heap1 zs {s with mode := MEM} := congrArg Prod.snd pair
    intro ref
    rw [sameHeap, decode_code_views good1.live.hs (show DecodeStateFrame s {s with mode := MEM} from rfl)]
    exact codeViews ref

/-- RESTORE, optional lazy window update, MEM write and final metadata
all retain every actual code-array view. There is no return-code or
allocation-success premise. -/
theorem inflate_leave_code_views_of_run
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (current : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39)
    (actual : inflate_leave c l h = .ok (rc, after)) :
    ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref := by
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
  have codes0 : ∀ ref : CodeRef, (Space.get heap0 ref : Option (Array Code)) = Space.get h ref := by
    intro ref
    change (Space.get (setI (r.put h stream0) zs {s with hold := l.hold, bits := l.bits}) ref : Option (Array Code)) = Space.get h ref
    rw [code_views_set_bits (by simpa only [ZStreamRef.put_istates] using E.hs), code_views_put_stream]
  rw [inflate_leave_restore_cut E] at actual
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [leaveAfterRestore_window env0 update] at actual
    have kept := leaveWithWindow_code_views_of_run env0 current0.good allocator.1 output0 statics0 rfl rfl actual
    intro ref
    exact (kept ref).trans (codes0 ref)
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases value : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [leaveAfterRestore_no_window env0 skip] at actual
    obtain ⟨result, finalHeap, stream, finalState, finish, _finalGood, _finalFrame,
      _views, _ret, finalCodes, _static, _streamFields⟩ :=
      leaveFinalize_public_fields (z := stream0) env0 current0.good
        (leaveOutputView_of_cursor current0.good output0) statics0 rfl rfl
    have pair := Except.ok.inj (actual.symm.trans finish)
    have sameHeap : after = finalHeap := congrArg Prod.snd pair
    subst finalHeap
    intro ref
    exact (finalCodes ref).trans (codes0 ref)

#print axioms leaveWithWindow_code_views_of_run
#print axioms inflate_leave_code_views_of_run
end Zlib.Inflate.Proofs
