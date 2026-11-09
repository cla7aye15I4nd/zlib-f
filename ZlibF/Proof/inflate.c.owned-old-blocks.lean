import ZlibF.Proof.«inflate.c.default-public-memory-contract»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A real window update cannot adopt a previously live caller object.
A new window is the allocator's fresh block; failure retains the old pointer. -/
theorem updatewindow_owned_old_blocks
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s state : InflateState} {eo : Nat} {source : BRef} {bytes : Array UInt8}
    {copy : UInt32} {rc : Int32}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (get : Space.get h source = some bytes) (count : copy.toNat ≤ eo) (bound : eo ≤ bytes.size)
    (unowned : ∀ w, s.window = .ref (.blk w) 0 → source ≠ .blk w)
    (run : updatewindow (some r) (.ref source eo) copy h = .ok (rc, after))
    (stateGet : after.istates zs = some state) :
    ∀ b, h.live b → InflateOwned zs state b → InflateOwned zs s b := by
  have sep : Separate (.ref source (eo - copy.toNat)) copy.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases good.inv.win.block with null | ⟨w, a, win, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, win, unowned w win]
  rcases good.inv.win.block with null | ⟨w, a, win, array, ro, size⟩
  · by_cases alloc : h.allocOk h.nalloc = true
    · obtain ⟨result, next, actual, current, window, _⟩ :=
        uw_null_ok_public good allocator null alloc get count bound
      have same := Except.ok.inj (actual.symm.trans run)
      cases same
      have states : state = next := Option.some.inj (stateGet.symm.trans current.live.hs)
      subst state
      intro b live owned
      rcases owned with decoder | windowOwned
      · exact Or.inl decoder
      · rw [window] at windowOwned
        cases windowOwned
        exact False.elim (good.fresh h.nextBlk (Nat.le_refl _) live)
    · have actual := uw_alloc_fail good.live allocator good.inv.win.wbits null alloc (.ref source eo) copy
      rw [run] at actual
      cases actual
      have same : setI { h with nalloc := h.nalloc + 1 } zs s = { h with nalloc := h.nalloc + 1 } :=
        tcSetI_same good.live.hs
      rw [same] at stateGet
      have states : state = s := Option.some.inj (stateGet.symm.trans good.live.hs)
      subst state
      exact fun _ _ owned => owned
  · obtain ⟨result, next, actual, _, _, current, window, _⟩ :=
      uw_post_public good win array ro size get count bound sep
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have states : state = next := Option.some.inj (stateGet.symm.trans current.live.hs)
    subst state
    simpa only [InflateOwned, window] using (fun b (_ : h.live b) (owned : InflateOwned zs s b) => owned)

/-- The actual optional-window continuation retains ownership of old live
objects in their incoming owner. This includes allocation failure and MEM. -/
theorem leaveWithWindow_owned_old_blocks
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (run : leaveWithWindow c l z h = .ok (rc, after)) (final : Good after r zs stream state) :
    ∀ b, h.live b → InflateOwned zs state b → InflateOwned zs s b := by
  obtain ⟨ref, bytes, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  obtain ⟨wr, heap1, state1, windowRun, good1, _, sourceView, _, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  have owned := updatewindow_owned_old_blocks good allocator get start bound unowned windowRun good1.live.hs
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
    have endpoint := Nat.sub_add_cancel start
    have frame := updatewindow_frame_public good allocator get (by omega) sep
      (by simpa only [C.run, endpoint] using windowRun)
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, ← frame.1] using statics
    obtain ⟨rc2, after2, stream2, state2, finish, good2, fields, _⟩ :=
      leaveFinalize_all_wrappers_safe (z := z) env1 good1 view statics1 cursor count
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    have same := Except.ok.inj (finish.symm.trans run)
    cases same
    have states : state = state2 := Option.some.inj (final.live.hs.symm.trans good2.live.hs)
    subst state2
    have window : state.window = state1.window := by rw [fields]
    simpa only [InflateOwned, window] using owned
  · obtain ⟨eqrc, _, stateEq, _⟩ := failure
    subst wr
    subst state1
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app] at run
    cases run
    have states : state = { s with mode := MEM } := Option.some.inj
      (final.live.hs.symm.trans (by simp))
    subst state
    exact fun _ _ owner => owner

/-- RESTORE and the complete actual leave retain old-object ownership. -/
theorem inflate_leave_owned_old_blocks
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) (final : Good after r zs stream state) :
    ∀ b, h.live b → InflateOwned zs state b → InflateOwned zs s b := by
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
  have shape : Shape h heap0 :=
    (shape_put invariant.good.live.hz stream0).trans
      (shape_setI (by simpa only [ZStreamRef.put_istates] using invariant.good.live.hs) state0)
  have live0 : heap0.live = h.live := fastMemoryMeta_live_eq_of_shape shape
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [current.globals]
    exact ⟨rfl, rfl⟩
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update] at run
    have owned := leaveWithWindow_owned_old_blocks env0 current.good allocator.1 output0
      statics0 rfl rfl run final
    simpa only [live0, InflateOwned, state0, leaveState] using owned
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip] at run
    obtain ⟨rc2, after2, stream2, state2, finish, good2, fields, _⟩ :=
      leaveFinalize_all_wrappers_safe (z := stream0) env0 current.good
        (leaveOutputView_of_cursor current.good output0) statics0 rfl rfl
    have same := Except.ok.inj (finish.symm.trans run)
    cases same
    have states : state = state2 := Option.some.inj (final.live.hs.symm.trans good2.live.hs)
    subst state2
    have window : state.window = s.window := by rw [fields]; rfl
    simpa only [InflateOwned, window] using
      (fun b (_ : h.live b) (owned : InflateOwned zs s b) => owned)

/-- The actual mode loop cannot change the window pointer. The optional
leave can only allocate a fresh window, including its MEM-error path. -/
theorem inflate_default_view_local_owned_old_blocks
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (final : Good after r zs stream state) :
    ∀ b, h.live b → InflateOwned zs state b → InflateOwned zs s b := by
  obtain ⟨bs, exit, regs, heap0, stream0, state0, _, _, _, loop, current,
    packet, bits, _, _, _, _, _, _, currentAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  have live0 : heap0.live = h.live := congrArg (fun x => x.2.2.2.2.2.2)
    (fastMemoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs heap0 loop)
  have window := inflate_run_window_unchanged E.strm E.hs current.good.live.hs loop
  rw [bind_app, loop] at run
  cases exit with
  | ret value =>
    change Except.ok (value, heap0) = Except.ok (rc, after) at run
    cases run
    have states : state = state0 := Option.some.inj (final.live.hs.symm.trans current.good.live.hs)
    subst state
    simpa only [InflateOwned, window] using
      (fun b (_ : h.live b) (owned : InflateOwned zs s b) => owned)
  | leave =>
    change inflate_leave c regs heap0 = .ok (rc, after) at run
    have env0 : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have owned := inflate_leave_owned_old_blocks env0 current currentAllocator packet bits run final
    simpa only [live0, InflateOwned, window] using owned

/-- The complete actual public call keeps every previously live owned
object within the incoming decoder ownership. Temporary cleanup is included. -/
theorem inflate_default_view_public_owned_return
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧
      (∀ b, h.live b → InflateOwned zs state b → InflateOwned zs s b) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s,
      ?_, final, fun _ _ owned => owned⟩
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h invariant.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
    dsimp only [syncBuf]
    rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
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
    obtain ⟨rc, heap1, stream, state, bytes, bodyRun, current, _,
      localGet, localSize, localRo⟩ :=
      inflate_default_view_local_state_return env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have owned := inflate_default_view_local_owned_old_blocks env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid bodyRun current.good
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, ?_, final, ?_⟩
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
    · intro b live owner
      exact owned b ((live_syncAlloc b).mpr (Or.inl live)) owner

/-- `int inflate(z_streamp strm, int flush)`.
For the same actual run used by the public memory contract, no old live
caller allocation becomes decoder-owned. All default public return paths,
including entry refusal and allocation failure, remain covered. -/
theorem inflate_default_view_public_owned_old_blocks
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {rc flush : Int32}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) flush) h = .ok (rc, after))
    (current : Good after r zs stream state) :
    ∀ block, h.live block → InflateOwned zs state block → InflateOwned zs s block := by
  obtain ⟨rc2, after2, stream2, state2, actual, final, owned⟩ :=
    inflate_default_view_public_owned_return invariant allocator buffers flush
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have states : state2 = state := Option.some.inj (final.good.live.hs.symm.trans current.live.hs)
  simpa only [states] using owned

#print axioms inflate_default_view_public_owned_old_blocks
end Zlib.Inflate.Proofs
