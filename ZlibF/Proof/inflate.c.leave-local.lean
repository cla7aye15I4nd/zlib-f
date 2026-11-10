import ZlibF.Proof.«inflate.c.default-local»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual counter/checksum/return suffix does not allocate or change
read-only flags. Its checksum callees have closed source proofs. -/
theorem memoryMetaFrameM_leaveFinalize (r : ZStreamRef) (c : Ctx) (l : IL) (z : ZStream)
    (root : c.strm = some r) : MemoryMetaFrameM r (leaveFinalize c l z) := by
  unfold leaveFinalize
  rw [root]
  repeat' first
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible exact memoryMetaFrameM_ldS r _
    | with_reducible exact memoryMetaFrameM_wrS_any r _ _
    | with_reducible exact memoryMetaFrameM_UPDATE_CHECK r _ _ _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_chkI32 r _
    | with_reducible refine memoryMetaFrameM_wrZ r _ (fun _ => ?_)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible refine memoryMetaFrameM_bind ?_ (fun _ => ?_)
    | rfl

/-- Actual window update and the final suffix preserve an existing byte
object outside the stream and its private state/window. Allocation failure
is included. The returned window-bit field remains exact. -/
theorem leaveWithWindow_local_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (tables : DataTableInvariant h s) (pending : DataPendingInvariant s)
    (hold : s.hold.toNat < 2 ^ s.bits.toNat) (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (localGet : h.bytes block = some array)
    (outside : ¬ (StreamRoot r block ∨ InflateOwned zs s block)) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧ after.bytes block = some array ∧
      after.ro block = h.ro block ∧ state.wbits = s.wbits := by
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
    have live : h.live block := Or.inl (by rw [localGet]; intro impossible; cases impossible)
    have localFrame := publicFrame.2.2.2.2.2 block live outside
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, ← publicFrame.1] using statics
    obtain ⟨rc, after, stream, state, finish, finalGood, finalFrame, views, ret, finalCodes, static⟩ :=
      leaveFinalize_all_wrappers_safe (z := z) env1 good1 view statics1 cursor count
    have metadata :=  memoryMetaFrameM_leaveFinalize r c l z E.strm heap1 rc after finish
    have roEq : after.ro = heap1.ro := congrArg Prod.fst metadata
    refine ⟨rc, after, stream, state, ?_, finalGood,
      finalFrame.tables finalCodes (windowFrame.tables codeViews tables),
      finalFrame.pending (windowFrame.pending pending), ?_, ?_, ?_, ?_⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    · rw [finalFrame, windowFrame]
      exact hold
    · change (Space.get after (BRef.blk block) : Option (Array UInt8)) = some array
      rw [views]
      exact localFrame.1.trans localGet
    · rw [roEq]
      exact localFrame.2.2.2.2.2.2.2
    · rw [finalFrame, windowFrame]
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have finalGood : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, finalGood, ?_,
      dataPendingInvariant_idle pending.sane (by
        change MEM ≠ LENEXT ∧ MEM ≠ DIST ∧ MEM ≠ DISTEXT ∧ MEM ≠ MATCH
        decide), hold, ?_, ?_, rfl⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
        setMode_tab good1.live.hs, pure_app]
      rfl
    · intro active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode MEM) active)
    · rw [setI_bytes, heapEq]
      exact localGet
    · rw [setI_ro, heapEq]
      rfl

/-- RESTORE and every actual inf_leave branch preserve a live byte object
outside the stream's owned footprint, including its read-only flag. -/
theorem inflate_leave_local_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (statics : Zlib.Crc32.Proofs.StaticsOK h) (buffers : DispatchBuffers h r l bs)
    (tables : DataTableInvariant h s) (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39)
    (localGet : h.bytes block = some array)
    (outside : ¬ (StreamRoot r block ∨ InflateOwned zs s block)) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧ after.bytes block = some array ∧
      after.ro block = h.ro block ∧ state.wbits = s.wbits := by
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
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    simpa only [Zlib.Crc32.Proofs.StaticsOK, static0] using statics
  have localGet0 : heap0.bytes block = some array := (views0 (.blk block)).trans localGet
  have ro0 : heap0.ro = h.ro := by simp only [heap0, setI_ro, ZStreamRef.put_ro]
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, finalGood, finalTables, finalPending,
      held, localFinal, localRo, windowBits⟩ :=
      leaveWithWindow_local_safe env0 good0 allocator output0 tables0 pending0 hold0 statics0 rfl rfl
        localGet0 outside
    refine ⟨rc, after, stream, state, ?_, finalGood, finalTables, finalPending,
      held, localFinal, ?_, windowBits⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
      exact run
    · rw [localRo, ro0]
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, finalGood, frame, views, ret, codeViews, static⟩ :=
      leaveFinalize_all_wrappers_safe (z := stream0) env0 good0
        (leaveOutputView_of_cursor good0 output0) statics0 rfl rfl
    have metadata := memoryMetaFrameM_leaveFinalize r c l stream0 E.strm heap0 rc after run
    have roEq : after.ro = heap0.ro := congrArg Prod.fst metadata
    refine ⟨rc, after, stream, state, ?_, finalGood, frame.tables codeViews tables0,
      frame.pending pending0, ?_, ?_, ?_, ?_⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
      exact run
    · rw [frame]
      exact hold0
    · exact (views (BRef.blk block)).trans localGet0
    · rw [roEq, ro0]
    · rw [frame]
      rfl

end Zlib.Inflate.Proofs
