import ZlibF.Proof.«inflate.c.flag-loop»
import ZlibF.Proof.«inflate.c.leave-default-boundary»
import ZlibF.Proof.«inflate.c.stream-frame-run»
import ZlibF.Proof.«inflate.c.default-public-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- RESTORE changes only the held bits and public cursors. -/
theorem DefaultFlagJ.restore
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL}
    {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) :
    DefaultFlagJ
      (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      r zs (leaveStream z l) (leaveState s l) := by
  have current := invariant.toDefaultStateJ.restore E buffers bits
  have search : (leaveState s l).mode = SYNC →
      (leaveState s l).«have».toNat ≤ 4 := by
    intro synced
    exact invariant.searchBound
      (by simpa [leaveState] using synced)
  have flags : (leaveState s l).flags = -1 ∨
      (leaveState s l).flags = 0 := by
    simpa [leaveState] using invariant.defaultFlags
  exact ⟨⟨current, search⟩, flags⟩

/-- Window updates retain mode, search count and header flags. -/
theorem DefaultFlagJ.window_update
    {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (invariant : DefaultFlagJ h r zs z s)
    (good : Good after r zs stream state)
    (frame : WindowStateFrame s state)
    (codeViews : ∀ ref : CodeRef,
      (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after)
    (static : after.static = h.static) :
    DefaultFlagJ after r zs stream state := by
  have current := invariant.toDefaultStateJ.window_update good
    frame codeViews platform static
  have search : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    rw [frame]
    exact invariant.searchBound
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    rw [frame]
    exact invariant.defaultFlags
  exact ⟨⟨current, search⟩, flags⟩

/-- Checksum and total-counter writes retain the same two history fields. -/
theorem DefaultFlagJ.leave_metadata
    {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (invariant : DefaultFlagJ h r zs z s)
    (good : Good after r zs stream state)
    (frame : LeaveMetadataFrame s state)
    (codeViews : ∀ ref : CodeRef,
      (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after)
    (static : after.static = h.static) :
    DefaultFlagJ after r zs stream state := by
  have current := invariant.toDefaultStateJ.leave_metadata good
    frame codeViews platform static
  have search : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    rw [frame]
    exact invariant.searchBound
  have flags : state.flags = -1 ∨ state.flags = 0 := by
    rw [frame]
    exact invariant.defaultFlags
  exact ⟨⟨current, search⟩, flags⟩

/-- The four-byte automatic object is disjoint from the live stream and
does not change any decoder field. -/
theorem DefaultFlagJ.syncAlloc
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (invariant : DefaultFlagJ h r zs z s) :
    DefaultFlagJ (syncAlloc h) r zs z s := by
  have current := default_state_syncAlloc invariant.toDefaultStateJ
  exact ⟨⟨current, invariant.searchBound⟩,
    invariant.defaultFlags⟩

/-- Freeing the four-byte automatic object retains the complete default
history relation. -/
theorem DefaultFlagJ.free_local
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {block : Nat} {array : Array UInt8}
    (invariant : DefaultFlagJ h r zs z s)
    (localGet : h.bytes block = some array)
    (localSize : array.size = 4) :
    DefaultFlagJ (freeWin h (.ref (.blk block) 0))
      r zs z s := by
  have current := invariant.toDefaultStateJ.free_local
    localGet localSize
  exact ⟨⟨current, invariant.searchBound⟩,
    invariant.defaultFlags⟩

/-- The actual checksum and counter suffix preserves the complete default
flag relation and default allocator. -/
theorem leaveFinalize_default_flag
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState}
    (E : Env c h r zs current s)
    (invariant : DefaultFlagJ h r zs current s)
    (allocator : DefAlloc current)
    (output : LeaveOutputView h l)
    (cursor : z.next_out = l.put)
    (count : z.avail_out = l.left) :
    ∃ rc after stream state,
      leaveFinalize c l z h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      DefAlloc stream := by
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨rc, after, stream, state, run, good, frame,
    views, ret, codes, static⟩ :=
    leaveFinalize_all_wrappers_safe E invariant.good output statics
      cursor count
  have sizes : ByteViewSizes h after := by
    intro ref
    rw [views ref]
  have final := invariant.leave_metadata good frame codes
    (sizes.platform invariant.platform) static
  have fixed := streamFrameM_leaveFinalize r c l z E.strm
    h rc after run
  exact ⟨rc, after, stream, state, run, final,
    fixed.allocator invariant.good.live.hz good.live.hz allocator⟩

/-- The actual window continuation retains the flag on both allocation
success and the genuine MEM failure path. -/
theorem leaveWithWindow_default_flag
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (allocator : DefAlloc z)
    (output : OutputCursorInvariant h r l)
    (cursor : z.next_out = l.put)
    (count : z.avail_out = l.left) :
    ∃ rc after stream state,
      leaveWithWindow c l z h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      DefAlloc stream := by
  obtain ⟨ref, bytes, off, put, get, _, room, leftCount,
    produced, unowned⟩ :=
    callerRange_slow_output invariant.good l output.range
      output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat =
      l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by
    rw [amount]
    exact produced
  have bound : off ≤ bytes.size := by omega
  have separate : Separate
      (.ref ref (off - (l.out_ - z.avail_out).toNat))
      (l.out_ - z.avail_out).toNat s.window
      (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null |
      ⟨w, a, win, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, win, unowned w win]
  obtain ⟨wr, heap1, state1, windowRun, good1,
    windowFrame, sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary
      (copy := l.out_ - z.avail_out) invariant.good
      allocator.1 get start bound unowned
  obtain ⟨platform, static⟩ :=
    updatewindow_platform_public invariant.good invariant.platform
      allocator.1 get start bound separate windowRun
  have current := invariant.window_update good1 windowFrame
    codeViews platform static
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 :=
      ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView,
        by rw [count] at start; exact start, bound⟩
    obtain ⟨rc, after, stream, state, finish, final,
      finalAllocator⟩ :=
      leaveFinalize_default_flag (z := z) env1 current allocator
        view cursor count
    refine ⟨rc, after, stream, state, ?_, final,
      finalAllocator⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact finish
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have good : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl)
        (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have final := current.mem_update good
      (platform.with_istates _) rfl
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state,
      ?_, final, allocator⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl,
      ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl

/-- The complete real `inf_leave` suffix preserves the full default flag
relation and allocator on every returning path. -/
theorem inflate_leave_default_flag
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      DefAlloc stream := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have current := invariant.restore E buffers bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef,
      (Space.get heap0 ref : Option (Array UInt8)) =
        Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport invariant.good current.good rfl
      views0 (by
        intro ref
        rw [byte_view_ro_setI, byte_view_ro_stream_put])
      buffers.output.range,
      buffers.output.nonnull, buffers.output.count,
      buffers.output.produced⟩
  by_cases update : (s.wsize != 0 ||
      (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, final,
      finalAllocator⟩ :=
      leaveWithWindow_default_flag env0 current allocator
        output0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, final,
      finalAllocator⟩
    rw [inflate_leave_restore_cut E,
      leaveAfterRestore_window env0 update]
    exact run

  · have skip : (s.wsize != 0 ||
      (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 ||
        (l.out_ != l.left && s.mode < BAD &&
          (s.mode < CHECK || c.flush != Z_FINISH))) <;>
        simp_all
    obtain ⟨rc, after, stream, state, run, final,
      finalAllocator⟩ :=
      leaveFinalize_default_flag (z := stream0) env0 current
        allocator (leaveOutputView_of_cursor current.good output0)
        rfl rfl
    refine ⟨rc, after, stream, state, ?_, final,
      finalAllocator⟩
    rw [inflate_leave_restore_cut E,
      leaveAfterRestore_no_window env0 skip]
    exact run

/-- The actual default body preserves the full flag relation and default
allocator through both direct returns and the real inf_leave suffix. -/
theorem inflate_body_default_flag
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s)) :
    ∃ rc after stream state,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      DefAlloc stream := by
  obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw
  have nonnull : z.next_out ≠ .null := by
    change z.next_out = .ref (.blk ob) oo at output
    rw [output]
    simp
  have inputValid : z.next_in = .null → z.avail_in = 0 := by
    change z.next_in = .ref (.blk ib) io at input
    rw [input]
    intro impossible
    cases impossible
  have raw : RawFastIO (dispatchRegs z s) :=
    ⟨ib, io, ob, oo, input, output, different⟩
  obtain ⟨bs, exit, regs, heap0, stream0, state0, used,
    made, bound, run, current, packet, currentRaw, bits,
    sizes, next, count, put, left, fixed,
    currentAllocator⟩ :=
    inflate_run_default_raw_framed E invariant.toDefaultStateJ
      allocator buffers nonnull inputValid raw
  obtain ⟨otherBs, otherExit, otherRegs, otherHeap,
    otherStream, otherState, otherUsed, otherMade,
    otherBound, otherRun, flagJ, otherPacket,
    otherRaw, otherBits, otherSizes, otherNext,
    otherCount, otherPut, otherLeft⟩ :=
    inflate_run_default_raw_default_flag E invariant buffers
      nonnull inputValid raw
  rw [run] at otherRun
  cases otherRun
  have sameState : otherState = state0 :=
    Option.some.inj
      (flagJ.good.live.hs.symm.trans current.good.live.hs)
  have sameStream : otherStream = stream0 :=
    Option.some.inj
      (flagJ.good.live.hz.symm.trans current.good.live.hz)
  subst otherState otherStream
  cases exit with
  | ret value =>
    refine ⟨value, heap0, stream0, state0, ?_, flagJ,
      currentAllocator⟩
    rw [bind_app, run]
    rfl
  | leave =>
    have currentEnv : Env c heap0 r zs stream0 state0 :=
      ⟨E.strm, E.st, current.good.live.hz,
        current.good.live.hs⟩
    obtain ⟨rc, after, stream, state, leaveRun, final,
      finalAllocator⟩ :=
      inflate_leave_default_flag currentEnv flagJ
        currentAllocator packet bits
    refine ⟨rc, after, stream, state, ?_, final,
      finalAllocator⟩
    rw [bind_app, run]
    exact leaveRun

/-- The stronger flag result and the live four-byte local refer to the
same actual returning execution. -/
theorem inflate_default_local_flag_return
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s)
    (invariant : DefaultFlagJ h r zs z s)
    (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s))
    (localGet : h.bytes block = some array)
    (localSize : array.size = 4)
    (localRo : h.ro block = false) :
    ∃ rc after stream state bytes,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      DefAlloc stream ∧
      after.bytes block = some bytes ∧
      bytes.size = 4 ∧ after.ro block = false := by
  obtain ⟨rc, after, stream, state, bytes, run, current,
    currentAllocator, localFinal, size, ro⟩ :=
    inflate_default_local_state_return E
      invariant.toDefaultStateJ allocator buffers raw
      localGet localSize localRo
  obtain ⟨otherRc, otherHeap, otherStream, otherState,
    otherRun, finalFlag, finalAllocator⟩ :=
    inflate_body_default_flag E invariant allocator buffers raw
  have heaps : after = otherHeap :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans otherRun))
  subst otherHeap
  have sameState : otherState = state :=
    Option.some.inj
      (finalFlag.good.live.hs.symm.trans current.good.live.hs)
  have sameStream : otherStream = stream :=
    Option.some.inj
      (finalFlag.good.live.hz.symm.trans current.good.live.hz)
  subst otherState otherStream
  exact ⟨rc, after, stream, state, bytes, run, finalFlag,
    finalAllocator, localFinal, size, ro⟩

/-- `int inflate(z_streamp strm, int flush)` for a default initialized
stream with distinct raw caller byte blocks. The actual public C-model
call preserves the full default flag relation and allocator for every
signed flush and every returning result. -/
theorem inflate_default_raw_flag_safe
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (invariant : DefaultFlagJ h r zs z s)
    (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (raw : RawFastIO (dispatchRegs z s))
    (flush : Int32) :
    ∃ rc after stream state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      DefAlloc stream ∧ after.bytes h.nextBlk = none := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := invariant.syncAlloc
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz,
      allocated.good.live.hs⟩
  obtain ⟨rc, heap1, stream, state, bytes, bodyRun,
    current, finalAllocator, localGet, localSize,
    localRo⟩ :=
    inflate_default_local_flag_return env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers)
      raw (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
      (syncAlloc_ro_buf h)
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream, state,
    ?_, final, finalAllocator, ?_⟩
  · obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw
    have outBool : (z.next_out == .null) = false := by
      change z.next_out = .ref (.blk ob) oo at output
      rw [output]
      rfl
    have inBool : (z.next_in == .null) = false := by
      change z.next_in = .ref (.blk ib) io at input
      rw [input]
      rfl
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h invariant.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app,
      stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, outBool,
      inBool, Bool.false_and, Bool.false_or,
      allocated.good.live.zst, castI]
    rw [bind_app] at bodyRun
    unfold runX at bodyRun
    dsimp only [c] at bodyRun
    erw [bodyRun]
    simp only []
    change (do freeB (syncBuf h); pure rc) heap1 =
      .ok (rc, freeWin heap1 (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  · simp only [syncBuf, freeWin, upd_same]

/-- A real default `inflate` step with distinct raw caller buffers extends
the public history while retaining the full default flag relation. -/
theorem inflate_default_raw_flag_history
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (reachable : StreamReachable .inflate h r)
    (invariant : DefaultFlagJ h r zs z s)
    (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (header : ActiveHeader h r)
    (raw : RawFastIO (dispatchRegs z s))
    (flush : Int32) :
    ∃ rc after stream state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultFlagJ after r zs stream state ∧
      DefAlloc stream ∧ StreamReachable .inflate after r := by
  obtain ⟨rc, after, stream, state, run, current,
    finalAllocator, freed⟩ :=
    inflate_default_raw_flag_safe invariant allocator buffers
      raw flush
  have operation : StreamOperation .inflate r
      (.inflate (some r) flush) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r
      (.inflate (some r) flush) := ⟨buffers, header⟩
  have executed : (Call.inflate (some r) flush).execute default h =
      .ok ((rc, default), after) := by
    change inflate (some r) flush h = _ at run
    simp only [Call.execute, heapCall, run]
  exact ⟨rc, after, stream, state, run, current,
    finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

/-- The public `inflate` entry rejects either invalid caller buffer binding
before entering the decoder. The four-byte automatic object is still freed. -/
theorem inflate_default_invalid_buffer_flag
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (invariant : DefaultFlagJ h r zs z s)
    (invalid : z.next_out = .null ∨
      (z.next_in = .null ∧ z.avail_in ≠ 0))
    (flush : Int32) :
    C.run (inflate (some r) flush) h =
      .ok (Z_STREAM_ERROR, tmpFreed h) ∧
    DefaultFlagJ (tmpFreed h) r zs z s := by
  have allocated := invariant.syncAlloc
  have rejected :
      (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) = true := by
    rcases invalid with output | ⟨input, count⟩
    · simp [output]
    · simp [input, count]
  have localGet := syncAlloc_bytes_buf h
  have localRo := syncAlloc_ro_buf h
  have localSize : (syncJunk h).size = 4 := by
    simp [syncJunk]
  have final := allocated.free_local localGet localSize
  constructor
  · show inflate (some r) flush h = _
    unfold inflate
    rw [bind_app, allocLocalB_run h invariant.good.fresh]
    simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, rejected,
      ite_true]
    simp [pure_app, freeBuf_run localGet localRo,
      tmpFreed, syncBuf]
  · exact final

end Zlib.Inflate.Proofs
