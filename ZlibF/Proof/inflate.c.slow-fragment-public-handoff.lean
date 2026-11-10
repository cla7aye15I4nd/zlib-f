import ZlibF.Proof.«inflate.c.slow-lookup-fragment»
import ZlibF.Proof.«inflate.c.leave-public-accounting»
import ZlibF.Proof.«inflate.c.table-rebuffer»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The real window-update and finalization suffix preserves the complete
pending syntax and held prefix. Its allocation failure remains explicit. -/
theorem leaveWithWindow_pending_syntax {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {L D : List Nat} {p : CopySyntax L D} {residual : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (output : OutputCursorInvariant h r l) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (phase : PendingSyntax p s residual) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      ((PendingSyntax p state residual ∧ state.hold = s.hold ∧ state.bits = s.bits ∧
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
      finalFrame.pending pending1, Or.inl ⟨pending_metadata (pending_window phase windowFrame) finalFrame,
        ?_, ?_, ?_, ?_⟩⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
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

/-- A genuine input wait can cross the complete public leave path. The
next call resumes the same phase and semantic source, or the real window
allocation reports MEM. No assumption about a successful leave is needed. -/
theorem inflate_leave_pending_input {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {L D : List Nat} {p : CopySyntax L D}
    {future residual : List Bool} (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (buffers : DispatchBuffers h r l []) (tables : DataTableInvariant h s)
    (pending : DataPendingInvariant s) (bits : l.bits.toNat ≤ 39)
    (phase : PendingSyntax p s residual) (source : FutureSource l [] future residual) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      ((PendingSyntax p state residual ∧ natBits state.bits.toNat state.hold.toNat ++ future = residual ∧
        stream.next_in = l.next ∧ stream.avail_in = 0) ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨good0, pending0, _hold0, _⟩ := leave_restore_invariant E good pending buffers.bits bits
  have env0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have phase0 := pending_restore phase l
  have saved : natBits l.bits.toNat l.hold.toNat ++ future = residual := by
    simpa only [FutureSource, stream, bytesBits, List.flatMap_nil, List.append_nil] using source
  have empty : l.have_ = 0 := UInt32.toNat_inj.mp (by simpa using buffers.bits.have_eq)
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
      leaveWithWindow_pending_syntax env0 good0 allocator output0 tables0 pending0 statics0 rfl rfl phase0
    refine ⟨rc, after, stream, state, ?_, nextGood, nextTables, nextPending, ?_⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
      exact run
    · rcases result with normal | failure
      · obtain ⟨finalPhase, hold, bits, cursor, count⟩ := normal
        exact Or.inl ⟨finalPhase, by rw [hold, bits]; exact saved, cursor, count.trans empty⟩
      · exact Or.inr failure
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, nextGood, frame, _, _ret, codeViews, _static, streamFields⟩ :=
      leaveFinalize_public_fields (z := stream0) env0 good0 (leaveOutputView_of_cursor good0 output0) statics0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, nextGood, frame.tables codeViews tables0,
      frame.pending pending0, Or.inl ⟨pending_metadata phase0 frame, ?_, ?_, ?_⟩⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
      exact run
    · rw [frame]
      exact saved
    · rw [streamFields]
      rfl
    · rw [streamFields]
      exact empty

/-- The actual public Rebuffer frame retains the exact saved state. A
newly observed chunk is spliced into the independent future, including
an empty chunk, and directly produces the next LOAD bit invariant. -/
theorem rebuffer_pending_input {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z next : ZStream} {s : InflateState} {L D : List Nat} {p : CopySyntax L D}
    {chunk : List UInt8} {later residual : List Bool}
    (good : Good before r zs z s) (rebuffer : Rebuffer before after r)
    (tables : DataTableInvariant before s) (phase : PendingSyntax p s residual)
    (held : s.hold.toNat < 2 ^ s.bits.toNat)
    (observed : Bytes after next.next_in next.avail_in.toNat chunk)
    (saved : natBits s.bits.toNat s.hold.toNat ++ (bytesBits chunk ++ later) = residual) :
    after.istates zs = some s ∧ DataTableInvariant after s ∧ PendingSyntax p s residual ∧
      BitInv after (dispatchRegs next s) chunk ∧ FutureSource (dispatchRegs next s) chunk later residual := by
  obtain ⟨state, finalTables⟩ := rebuffer_dataTableInvariant good rebuffer tables
  exact ⟨state, finalTables, phase, header_input_view_of_bytes observed held, refill_future saved⟩

#print axioms leaveWithWindow_pending_syntax
#print axioms inflate_leave_pending_input
#print axioms rebuffer_pending_input
end Zlib.Inflate.Proofs.SlowInputFragment
