import ZlibF.Proof.«inflate.c.leave-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem leave_selector_not_memory {rc ret : Int32} {test : Prop} [Decidable test]
    (notMem : ret ≠ Z_MEM_ERROR) (selected : rc = if test then Z_BUF_ERROR else ret) :
    rc ≠ Z_MEM_ERROR := by
  split at selected
  · rw [selected]
    decide
  · rw [selected]
    exact notMem

/-- A genuine memory-error return from the actual window continuation
requires a missing window. The final suffix cannot introduce MEM_ERROR. -/
theorem leaveWithWindow_memory_requires_null
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (notMem : l.ret ≠ Z_MEM_ERROR)
    (executed : leaveWithWindow c l z h = .ok (Z_MEM_ERROR, after)) : s.window = .null := by
  obtain ⟨ref, bytes, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    have separate : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
        (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
      rcases good.inv.win.block with null | ⟨w, a, win, _, _, _⟩
      · simp [Separate, null]
      · simp [Separate, win, unowned w win]
    have endpoint : off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat = off :=
      Nat.sub_add_cancel start
    have publicFrame := updatewindow_frame_public (copy := l.out_ - z.avail_out)
      (off := off - (l.out_ - z.avail_out).toNat) good allocator get (by omega) separate
      (by simpa only [C.run, endpoint] using windowRun)
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, ← publicFrame.1] using statics
    obtain ⟨rc, heap2, stream, state, finish, _, _, _, selected, _, _⟩ :=
      leaveFinalize_all_wrappers_safe (z := z) env1 good1 view statics1 cursor count
    have source : leaveWithWindow c l z h = .ok (rc, heap2) := by
      unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    have codeEq : rc = Z_MEM_ERROR := congrArg Prod.fst (Except.ok.inj (source.symm.trans executed))
    exact False.elim (leave_selector_not_memory notMem selected codeEq)
  · exact failure.2.1

/-- With an ordinary leave register, a genuine late memory failure needs
a nonempty current output segment. An empty segment with no window skips
the allocator; an existing window cannot take its allocation-failure path. -/
theorem inflate_leave_memory_nonempty
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (notMem : l.ret ≠ Z_MEM_ERROR)
    (executed : inflate_leave c l h = .ok (Z_MEM_ERROR, after)) : l.out_ ≠ l.left := by
  intro empty
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
  have statics : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [current.globals]
    exact ⟨rfl, rfl⟩
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update] at executed
    have window : state0.window = .null :=
      leaveWithWindow_memory_requires_null env0 current.good allocator.1 output0 statics rfl rfl notMem executed
    have zero := current.good.inv.win.nullws window
    change s.wsize = 0 at zero
    simp only [zero, empty, bne_self_eq_false, Bool.false_and, Bool.false_or, Bool.false_eq_true] at update
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip] at executed
    obtain ⟨rc, heap1, stream, state, source, _, _, _, selected, _, _⟩ :=
      leaveFinalize_all_wrappers_safe (z := stream0) env0 current.good
        (leaveOutputView_of_cursor current.good output0) statics rfl rfl
    have codeEq : rc = Z_MEM_ERROR := congrArg Prod.fst (Except.ok.inj (source.symm.trans executed))
    exact leave_selector_not_memory notMem selected codeEq

end Zlib.Inflate.Proofs
