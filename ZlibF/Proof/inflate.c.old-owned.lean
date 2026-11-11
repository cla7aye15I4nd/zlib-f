import ZlibF.Proof.«inflate.c.entry-header»
import ZlibF.Proof.«inflate.c.low-output»
import ZlibF.Proof.«inflate.c.origin-fields-memory-contract»
import ZlibF.Proof.«inflate.c.window-pointer-run»
import ZlibF.Proof.«inflate.c.default-view-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An update of an existing window retains its actual pointer. The
translated public update is compared with its proved existing-window run. -/
theorem updatewindow_old_window_actual
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s state : InflateState} {source : BRef} {bytes : Array UInt8} {off : Nat} {copy : UInt32} {rc : Int32}
    (good : Good h r zs z s) (get : Space.get h source = some bytes)
    (start : copy.toNat ≤ off) (bound : off ≤ bytes.size)
    (unowned : ∀ w, s.window = .ref (.blk w) 0 → source ≠ .blk w)
    (run : updatewindow (some r) (.ref source off) copy h = .ok (rc, after))
    (stateGet : after.istates zs = some state) :
    s.window ≠ .null → state.window = s.window := by
  intro nonnull
  rcases good.inv.win.block with null | ⟨w, a, pointer, windowGet, writable, size⟩
  · exact (nonnull null).elim
  · have separate : Separate (.ref source (off - copy.toNat)) copy.toNat s.window (2 ^ s.wbits.toNat) := by
      simp [Separate, pointer, unowned w pointer]
    obtain ⟨computed, computedState, actual, _, _, current, window, _⟩ :=
      uw_post_public good pointer windowGet writable size get start bound separate
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have stateEq : state = computedState := Option.some.inj (stateGet.symm.trans current.live.hs)
    subst state
    exact window

theorem leaveFinalize_default_state_old_window {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (invariant : DefaultStateJ h r zs current s) (allocator : DefAlloc current)
    (output : LeaveOutputView h l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ state.window = s.window := by
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨rc, after, stream, state, run, good, frame, views, ret, codes, static⟩ :=
    leaveFinalize_all_wrappers_safe E invariant.good output statics cursor count
  have sizes : ByteViewSizes h after := by
    intro ref
    rw [views ref]
  have final := invariant.leave_metadata good frame codes (sizes.platform invariant.platform) static
  have fixed := streamFrameM_leaveFinalize r c l z E.strm h rc after run
  exact ⟨rc, after, stream, state, run, final,
    fixed.allocator invariant.good.live.hz good.live.hz allocator, by rw [frame]⟩



theorem leaveWithWindow_default_state_old_window {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (output : OutputCursorInvariant h r l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (set : s.wbits ≠ 0) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ (s.window ≠ .null → state.window = s.window) := by
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
  have current := invariant.window_update good1 windowFrame codeViews platform static set
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    obtain ⟨rc, after, stream, state, finish, final, finalAllocator, finalWindow⟩ :=
      leaveFinalize_default_state_old_window (z := z) env1 current allocator view cursor count
    have windowSame := updatewindow_old_window_actual invariant.good get start bound unowned windowRun good1.live.hs
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, fun nonnull => finalWindow.trans (windowSame nonnull)⟩
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
    have final := current.mem_update good (platform.with_istates _) rfl
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, final, allocator, fun _ => rfl⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl



theorem inflate_leave_default_state_old_window {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (lowOut : s.mode ≤ DICT → l.out_ = l.left) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ (s.window ≠ .null → state.window = s.window) := by
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
  · obtain ⟨rc, after, stream, state, run, final, finalAllocator, finalWindow⟩ :=
      leaveWithWindow_default_state_old_window env0 current allocator output0 rfl rfl
        (invariant.width_of_update lowOut update)
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, finalWindow⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, final, finalAllocator, finalWindow⟩ :=
      leaveFinalize_default_state_old_window (z := stream0) env0 current allocator
        (leaveOutputView_of_cursor current.good output0) rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator, fun _ => finalWindow⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact run


#print axioms updatewindow_old_window_actual

#print axioms leaveFinalize_default_state_old_window

#print axioms leaveWithWindow_default_state_old_window

#print axioms inflate_leave_default_state_old_window


theorem inflate_default_view_local_state_return_old_window
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧ (s.window ≠ .null → state.window = s.window) := by
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used, made, bound, run, current,
    ⟨_, _, packet⟩, _, bits, sizes, next, count, put, left, fixed, currentAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid local_
  obtain ⟨bytes, byteGet, byteSize⟩ := sizes.view (ref := .blk block) localGet
  have byteSize4 : bytes.size = 4 := byteSize.trans localSize
  have metadata := memoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs heap0 run
  have roEq : heap0.ro = h.ro := congrArg Prod.fst metadata
  have ro0 : heap0.ro block = false := by rw [roEq]; exact localRo
  have loopWindow := inflate_run_window_unchanged E.strm E.hs current.good.live.hs run
  cases exit with
  | ret value =>
    refine ⟨value, heap0, stream0, state0, bytes, ?_, current,
      currentAllocator, byteGet, byteSize4, ro0, fun _ => loopWindow⟩
    rw [bind_app, run]
    rfl
  | leave =>
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have statics : Zlib.Crc32.Proofs.StaticsOK heap0 := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [current.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨rc, after, stream, state, leaveRun, final, finalAllocator, finalWindow⟩ :=
      inflate_leave_default_state_old_window currentEnv current currentAllocator packet bits
        (inflate_run_default_low_out E invariant buffers nonnull inputValid local_ run current.good.live.hs)
    obtain ⟨localRc, localHeap, localZ, localS, localRun, localGood, localTables,
      localPending, held, localFinal, finalRo, windowBits⟩ :=
      inflate_leave_local_boundary currentEnv current.good currentAllocator.1 statics
        packet current.tables current.pending bits byteGet
        (default_local_outside current.good byteGet byteSize4 current.local_width)
    have same : (rc, after) = (localRc, localHeap) :=
      Except.ok.inj (leaveRun.symm.trans localRun)
    cases same
    refine ⟨rc, after, stream, state, bytes, ?_, final,
      finalAllocator, localFinal, byteSize4, finalRo.trans ro0, fun nonnull => (finalWindow (by rwa [loopWindow])).trans loopWindow⟩
    rw [bind_app, run]
    exact leaveRun

#print axioms inflate_default_view_local_state_return_old_window

theorem inflate_default_view_state_safe_old_window
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z) (flush : Int32) :
    ∃ rc after stream state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧ (s.window ≠ .null → state.window = s.window) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have local_ : HeaderLocal c (syncAlloc h) r s (dispatchRegs z s) := entry_header_local invariant.good.fresh entry flush
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s,
      ?_, final, allocator, ?_, fun _ => rfl⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    · simp only [syncBuf, freeWin, upd_same]
  · have accepted : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by
      intro null
      apply rejected
      simp [null]
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    obtain ⟨rc, heap1, stream, state, bytes, bodyRun, current, finalAllocator,
      localGet, localSize, localRo, finalWindow⟩ :=
      inflate_default_view_local_state_return_old_window env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid local_
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, ?_, final, finalAllocator, ?_, finalWindow⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
      rw [bind_app] at bodyRun
      unfold runX at bodyRun
      dsimp only [c] at bodyRun
      erw [bodyRun]
      simp only []
      change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
      rw [bind_app]
      dsimp only [syncBuf]
      rw [freeBuf_run localGet localRo]
      rfl
    · simp only [syncBuf, freeWin, upd_same]

#print axioms inflate_default_view_state_safe_old_window
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete initialized public inflate retains every incoming
owned object in its returned ownership graph. Its exact allocation ledger
therefore also has the original sequence-safety removed-owned predicate.
All execution and representation facts are produced on the same run. -/
theorem inflate_default_origin_old_owned_resources
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z) (flush : Int32) :
    ∃ rc after stream state used output,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      StreamAccounting z stream used output.length ∧ Bytes after z.next_out output.length output ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) [⟨z.next_out, output.length⟩] ∧
      (s.window ≠ .null → state.window = s.window) ∧
      (∀ b, StreamOwned h r b → StreamOwned after r b) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨rc, after, stream, state, used, output, run, current, finalAllocator, _local,
    accounting, bytes, _totals, _progress, _codes, _memoryTotals, _modes, frame, ledger⟩ :=
    inflate_default_origin_public_memory_contract invariant allocator buffers entry flush
  obtain ⟨rc2, after2, stream2, state2, actual, next, _, _, window⟩ :=
    inflate_default_view_state_safe_old_window invariant.toDefaultStateJ allocator buffers entry flush
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have stateEq : state2 = state := Option.some.inj (next.good.live.hs.symm.trans current.good.live.hs)
  subst state2
  have retain : ∀ b, StreamOwned h r b → StreamOwned after r b := by
    intro b owned
    rw [invariant.good.streamOwned_iff] at owned
    rw [current.good.streamOwned_iff]
    rcases owned with stateRoot | oldWindow
    · exact Or.inl stateRoot
    · right
      have nonnull : s.window ≠ .null := by rw [oldWindow]; intro impossible; cases impossible
      rw [window nonnull]
      exact oldWindow
  have exactLedger : LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
    intro b
    have removed : ¬ (StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
      rintro ⟨old, absent⟩
      exact absent (retain b old)
    have actualLedger := ledger b
    simp only [removed, not_false_eq_true, and_true]
    simpa only [current.good.streamOwned_iff, not_false_eq_true, and_true] using actualLedger
  exact ⟨rc, after, stream, state, used, output, run, current, finalAllocator,
    accounting, bytes, frame, window, retain, exactLedger⟩

#print axioms inflate_default_origin_old_owned_resources
end Zlib.Inflate.Proofs
