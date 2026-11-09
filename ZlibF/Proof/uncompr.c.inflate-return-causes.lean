import ZlibF.Proof.«inflate.c.leave-zero-output-memory»
import ZlibF.Proof.«inflate.c.live-frame-leave»
import ZlibF.Proof.«inflate.c.direct-terminal-loop»

namespace Zlib.Uncompr.Proof.InflateCauses
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual window suffix can return a new memory error only after a
rejected allocation in that same execution. Existing terminal MEM is not
part of this suffix. -/
theorem leaveWithWindow_memory_failure
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (output : OutputCursorInvariant h r l)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (ret : PublicLeaveRet l)
    (run : leaveWithWindow c l z h = .ok (Z_MEM_ERROR, after)) :
    AllocationFailed h after := by
  obtain ⟨ref, array, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ array.size := by omega
  have separate : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
      (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases good.inv.win.block with null | ⟨w, a, window, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, outcome⟩ :=
    updatewindow_safe_public (copy := l.out_ - z.avail_out) good allocator get start bound separate
  change updatewindow (some r) (.ref ref off) (l.out_ - z.avail_out) h = .ok (wr, heap1) at windowRun
  rcases outcome with success | failure
  · obtain ⟨success, _, _⟩ := success
    subst wr
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    exact False.elim ((leaveFinalize_result c l z ret heap1 Z_MEM_ERROR after run).not_memory rfl)
  · obtain ⟨eqrc, _, rejected, heapEq, stateEq⟩ := failure
    have refused : h.allocOk h.nalloc = false := by
      cases value : h.allocOk h.nalloc <;> simp_all
    subst wr
    subst state1
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app] at run
    cases run
    refine ⟨h.nalloc, Nat.le_refl _, ?_, refused⟩
    rw [heapEq]
    change h.nalloc < h.nalloc + 1
    omega

/-- The actual RESTORE prefix cannot hide the allocation failure. -/
theorem inflate_leave_memory_failure
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) (ret : PublicLeaveRet l)
    (run : inflate_leave c l h = .ok (Z_MEM_ERROR, after)) :
    AllocationFailed h after := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have current := invariant.restore E buffers bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport invariant.good current.good rfl
      (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
      (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  rw [inflate_leave_restore_cut E] at run
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [leaveAfterRestore_window env0 update] at run
    have failed := leaveWithWindow_memory_failure env0 current.good allocator.1 output0 rfl rfl ret run
    simpa only [AllocationFailed, heap0, stream0, state0, setI, ZStreamRef.put_nalloc,
      ZStreamRef.put_allocOk] using failed
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [leaveAfterRestore_no_window env0 skip] at run
    exact False.elim ((leaveFinalize_result c l stream0 ret heap0 Z_MEM_ERROR after run).not_memory rfl)

/-- Actual entry with the source's exact TYPE normalization retained. -/
private theorem normalized_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      DefaultStateJ after r zs z state ∧ DispatchBuffers after r (dispatchRegs z state) bs ∧
      (dispatchRegs z state).bits.toNat ≤ 39 ∧
      state = (if s.mode = TYPE then { s with mode := TYPEDO } else s) := by
  obtain ⟨after, state, run, good, env, output, sizes, frame, heapEq, stateEq⟩ :=
    inflate_run_output_entry_frame_state E invariant.good buffers nonnull
  have currentBuffers : StreamBuffers after r := by
    obtain ⟨stream, get, input, out, separate⟩ := buffers
    have same : stream = z := Option.some.inj (get.symm.trans invariant.good.live.hz)
    subst stream
    refine ⟨z, good.live.hz, ?_, ?_, separate⟩
    · apply callerRange_transport invariant.good good (by rw [frame]) _ _ input
      · intro ref; rw [heapEq, byte_view_get_setI]
      · intro ref; rw [heapEq, byte_view_ro_setI]
    · apply callerRange_transport invariant.good good (by rw [frame]) _ _ out
      · intro ref; rw [heapEq, byte_view_get_setI]
      · intro ref; rw [heapEq, byte_view_ro_setI]
  obtain ⟨bs, bits, separate⟩ := dispatchRegs_input (s := state) good.live.hz currentBuffers inputValid
    (by rw [frame]; exact invariant.held)
  have finalJ : DefaultStateJ after r zs z state := by
    by_cases type : s.mode = TYPE
    · have tables : DataTableInvariant after state := by
        intro active
        rw [stateEq, if_pos type] at active
        change DataTableMode TYPEDO at active
        rcases active with eq | eq | eq | eq | eq | eq | eq <;> contradiction
      have pending : DataPendingInvariant state := by
        apply dataPendingInvariant_idle (by rw [frame]; exact invariant.pending.sane)
        rw [stateEq, if_pos type]
        change TYPEDO ≠ LENEXT ∧ TYPEDO ≠ DIST ∧ TYPEDO ≠ DISTEXT ∧ TYPEDO ≠ MATCH
        decide
      have blockFrame : BlockHeaderFrame s state := by rw [stateEq, if_pos type]; rfl
      have modes : BlockControlMode state.mode := by
        rw [stateEq, if_pos type]
        exact Or.inr (Or.inl rfl)
      have format := invariant.block_format (Or.inl type)
      have base := invariant.toDefaultDecodeJ.block_update good tables pending blockFrame modes format sizes
        (by rw [heapEq]; rfl)
      exact invariant.config_update base frame.default_config format
    · have sameState : state = s := by rw [stateEq, if_neg type]
      have sameHeap : after = h := by
        rw [heapEq, sameState]; simp [setI, upd_self _ _ _ invariant.good.live.hs]
      rwa [sameHeap, sameState]
  have input' : CallerRange after r z.next_in z.avail_in.toNat false := by
    obtain ⟨stream, get, input, _, _⟩ := currentBuffers
    have same : stream = z := Option.some.inj (get.symm.trans good.live.hz)
    subst stream
    exact input
  exact ⟨after, state, bs, run, finalJ, ⟨input', output, separate, bits⟩, good.inv.bits, stateEq⟩

private def ExcludesTerminal (r : ZStreamRef) (zs : Nat) (terminal : UInt32) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ DispatchBuffers h r l bs ∧
    l.bits.toNat ≤ 39 ∧ s.mode ≠ terminal

/-- MEM and SYNC direct returns can only come from the incoming terminal,
not from a new terminal manufactured by an ordinary mode iteration. -/
theorem inflate_run_direct_terminal_excluded
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {terminal : UInt32}
    {z : ZStream} {s : InflateState} {regs : IL} {code : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (kind : (terminal = MEM ∧ code = Z_MEM_ERROR) ∨
      (terminal = SYNC ∧ code = Z_STREAM_ERROR)) (initial : s.mode ≠ terminal)
    (run : runX (inflate_run c) IL.init h = .ok ((.error (.ret code), regs), after)) : False := by
  obtain ⟨entryHeap, entryState, bs, cut, current, packet, bits, stateEq⟩ :=
    normalized_entry E invariant buffers nonnull inputValid
  have notType : TYPEDO ≠ terminal := by rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have entryMode : entryState.mode ≠ terminal := by
    rw [stateEq]
    split
    · exact notType
    · exact initial
  have start : ExcludesTerminal r zs terminal (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits, entryMode⟩
  have step : ∀ before heap outcome finalRegs finalHeap, ExcludesTerminal r zs terminal before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => ExcludesTerminal r zs terminal finalRegs finalHeap
      | .error exit => exit ≠ .ret code := by
    intro before heap outcome finalRegs finalHeap valid source
    obtain ⟨stream, state, remaining, j, buffers, incoming, excluded⟩ := valid
    have env : Env c heap r zs stream state := ⟨E.strm, E.st, j.good.live.hz, j.good.live.hs⟩
    cases outcome with
    | ok value =>
      cases value
      obtain ⟨_, _, _, nextZ, nextS, used, _, _, actual, final, nextBuffers,
        _, _, _, _, _, nextBits, _⟩ :=
        inflate_dispatch_default_view_state_rank env j buffers incoming
      have same := Except.ok.inj (actual.symm.trans source)
      cases same
      have low := inflate_dispatch_normal_low env j buffers incoming source final.good.live.hs
      refine ⟨nextZ, nextS, remaining.drop used, final, nextBuffers, nextBits, ?_⟩
      intro equal
      rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rw [equal] at low
      · exact (by decide : ¬ MEM < MEM) low
      · exact (by decide : ¬ SYNC < MEM) low
    | error exit =>
      intro selected
      subst exit
      have wanted : code = Z_MEM_ERROR ∨ code = Z_STREAM_ERROR := by
        rcases kind with ⟨_, same⟩ | ⟨_, same⟩
        · exact Or.inl same
        · exact Or.inr same
      obtain ⟨selected, _, _⟩ := inflate_dispatch_direct_terminal env j buffers incoming source wanted
      apply excluded
      rcases kind with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact selected.resolve_right (fun other => (by decide : Z_MEM_ERROR ≠ Z_STREAM_ERROR) other.2) |>.1
      · exact selected.resolve_left (fun other => (by decide : Z_STREAM_ERROR ≠ Z_MEM_ERROR) other.2) |>.1
  rw [cut] at run
  exact xwhile_success_control_post _ _ step start run rfl

/-- A new MEM result of the complete real body comes from the real
window allocation, with its original allocation index preserved. -/
theorem inflate_body_memory_failure
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (initial : s.mode ≠ MEM)
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (Z_MEM_ERROR, after)) :
    AllocationFailed h after := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, used, made, _, run, current,
    packet, bits, _, _, _, _, _, _, loopAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  rw [bind_app, run] at body
  cases exit with
  | ret code =>
    change (Except.ok (code, loopHeap) : Except Fault (Int32 × Heap)) = .ok (Z_MEM_ERROR, after) at body
    have codes : code = Z_MEM_ERROR := congrArg Prod.fst (Except.ok.inj body)
    subst code
    exact False.elim (inflate_run_direct_terminal_excluded E invariant buffers nonnull inputValid
      (Or.inl ⟨rfl, rfl⟩) initial run)
  | leave =>
    change inflate_leave c regs loopHeap = .ok (Z_MEM_ERROR, after) at body
    have env : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    have ret := inflate_run_leave_ret_codes E invariant buffers nonnull inputValid run
    obtain ⟨i, lower, upper, rejected⟩ :=
      inflate_leave_memory_failure env current loopAllocator packet bits ret body
    have metadata := fastMemoryMetaFrameX_inflate_run r c E.strm IL.init h (.error Ex.leave) regs loopHeap run
    have allocations : loopHeap.nalloc = h.nalloc := congrArg (fun m => m.2.2.1) metadata
    have oracle : loopHeap.allocOk = h.allocOk := congrArg (fun m => m.2.2.2.2.1) metadata
    exact ⟨i, by simpa only [allocations] using lower, upper, by simpa only [oracle] using rejected⟩

/-- `int inflate(z_streamp strm, int flush)`.
For a default initialized state that was not already MEM, a real public
MEM result has a rejected allocator request in this same call. Caller
entry refusals and the real temporary allocation/free are included. -/
theorem inflate_public_memory_failure
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) (initial : s.mode ≠ MEM)
    (run : C.run (inflate (some r) flush) h = .ok (Z_MEM_ERROR, after)) :
    AllocationFailed h after := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true
  · unfold C.run inflate at run
    rw [bind_app, allocLocalB_run h invariant.good.fresh] at run
    simp only [] at run
    rw [bind_app] at run
    simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app] at run
    dsimp only [syncBuf] at run
    rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)] at run
    have impossible := congrArg Prod.fst (Except.ok.inj run)
    exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_MEM_ERROR) impossible)
  · have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by intro null; exact rejected (by simp [null])
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    have localBuffers := streamBuffers_syncAlloc invariant.good.fresh buffers
    obtain ⟨rc, heap1, stream, state, bytes, bodyRun, current, finalAllocator,
      get, size, ro⟩ :=
      inflate_default_view_local_state_return env allocated allocator localBuffers nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have actual : C.run (inflate (some r) flush) h = .ok (rc, freeWin heap1 (syncBuf h)) := by
      unfold C.run inflate
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
      rw [freeBuf_run get ro]
      rfl
    have same := Except.ok.inj (actual.symm.trans run)
    have code : rc = Z_MEM_ERROR := congrArg Prod.fst same
    have heapEq : freeWin heap1 (syncBuf h) = after := congrArg Prod.snd same
    rw [code] at bodyRun
    obtain ⟨i, lower, upper, failed⟩ :=
      inflate_body_memory_failure env allocated allocator localBuffers nonnull inputValid initial bodyRun
    refine ⟨i, lower, ?_, failed⟩
    rw [←heapEq]
    exact upper

#print axioms inflate_public_memory_failure
#print axioms inflate_body_memory_failure
#print axioms inflate_run_direct_terminal_excluded
#print axioms leaveWithWindow_memory_failure
#print axioms inflate_leave_memory_failure
end Zlib.Uncompr.Proof.InflateCauses
