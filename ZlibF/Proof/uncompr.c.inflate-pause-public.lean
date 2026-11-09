import ZlibF.Proof.«uncompr.c.inflate-pause-stored»
import ZlibF.Proof.«uncompr.c.inflate-pause-construction»
import ZlibF.Proof.«inflate.c.default-view-return-modes»

namespace Zlib.Uncompr.Proof.InflatePause
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem dispatch_leave_pause
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) (get : after.istates zs = some returned) : PauseGood returned := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal
  · exact head_leave_pause E invariant buffers head ((inflate_dispatch_HEAD E l head).symm.trans run) get
  · rcases dictionary with id | dictionary
    · exact dictid_leave_pause E invariant buffers id flush ((inflate_dispatch_DICTID E l id).symm.trans run) get
    · exact dict_leave_pause E invariant buffers dictionary flush ((inflate_dispatch_DICT E l dictionary).symm.trans run) get
  · exact type_leave_pause E buffers type flush run get
  · exact stored_dispatch_leave_pause E invariant buffers stored flush run get
  · exact construction_leave_pause E invariant buffers construction run get
  · exact data_dispatch_leave_pause E invariant buffers data run get
  · rcases trailer with check | length
    · exact check_leave_pause E invariant buffers check ((inflate_dispatch_CHECK E l check).symm.trans run) ret get
    · obtain ⟨source, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
      have ended : regs.ret = Z_STREAM_END := by
        rw [←xrun_regs_eq ((inflate_dispatch_LENGTH E l length).trans source) run]
      exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) (ret.symm.trans ended))
  · have source := inflate_dispatch_terminal_run E l terminal
    have selected := xrun_outcome_eq source run
    have returnedRet := congrArg IL.ret (xrun_regs_eq source run)
    rcases terminal with mode | mode | mode | mode
    · have ended : regs.ret = Z_STREAM_END := by
        rw [mode] at returnedRet
        simpa only [terminalRegs, ↓reduceIte] using returnedRet.symm
      exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) (ret.symm.trans ended))
    · have error : regs.ret = Z_DATA_ERROR := by
        rw [mode] at returnedRet
        simpa only [terminalRegs, show BAD ≠ DONE from by decide, ↓reduceIte] using returnedRet.symm
      exact False.elim ((by decide : Z_OK ≠ Z_DATA_ERROR) (ret.symm.trans error))
    · rw [mode] at selected
      simp [terminalExit, MEM, DONE, BAD] at selected
    · rw [mode] at selected
      simp [terminalExit, SYNC, MEM, DONE, BAD] at selected

private def PauseInv (r : ZStreamRef) (zs : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39

/-- Every actual loop iteration is included. An ordinary ret=OK leave
retains the mode in the exact final decoder object of that execution. -/
theorem inflate_run_leave_pause
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {regs : IL}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) (get : after.istates zs = some returned) : PauseGood returned := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : PauseInv r zs (dispatchRegs z entryState) entryHeap := ⟨z, entryState, bs, current, packet, bits⟩
  let Q := fun (exit : Ex) (regs : IL) (heap : Heap) =>
    exit = Ex.leave → regs.ret = Z_OK → ∀ state, heap.istates zs = some state → PauseGood state
  have step : ∀ l heap outcome regs finalHeap, PauseInv r zs l heap →
      runX (inflate_dispatch c) l heap = .ok ((outcome, regs), finalHeap) →
      match outcome with
      | .ok () => PauseInv r zs regs finalHeap
      | .error exit => Q exit regs finalHeap := by
    intro l heap outcome regs finalHeap valid actual
    obtain ⟨z, s, bs, j, buffers, bits⟩ := valid
    have env : Env c heap r zs z s := ⟨E.strm, E.st, j.good.live.hz, j.good.live.hs⟩
    cases outcome with
    | ok value =>
      cases value
      obtain ⟨_, _, _, stream, state, used, _, _, source, final, packet, _, _, _, _, _, bound, _⟩ :=
        inflate_dispatch_default_view_state_rank env j buffers bits
      have same := Except.ok.inj (source.symm.trans actual)
      cases same
      exact ⟨stream, state, bs.drop used, final, packet, bound⟩
    | error exit =>
      intro selected ret state get
      subst exit
      exact dispatch_leave_pause env j buffers bits flush actual ret get
  rw [cut] at run
  exact xwhile_success_control_post _ _ step start run rfl ret returned get

/-- A real successful returning body preserves resumability. The window
failure branch cannot have OK, and ordinary leave keeps the loop's mode. -/
theorem inflate_body_ok_pause
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (flush : c.flush = Z_NO_FLUSH)
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (Z_OK, after))
    (good : Good after r zs stream state) : PauseGood state := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, used, made, _, run, current,
    packet, bits, _, _, _, _, _, _, loopAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  rw [bind_app, run] at body
  cases exit with
  | ret code =>
    change (Except.ok (code, loopHeap) : Except Fault (Int32 × Heap)) = .ok (Z_OK, after) at body
    have selected : code = Z_OK := congrArg Prod.fst (Except.ok.inj body)
    have codes := inflate_run_direct_codes run
    rw [selected] at codes
    exact False.elim (by rcases codes with codes | codes | codes <;> revert codes <;> decide)
  | leave =>
    change inflate_leave c regs loopHeap = .ok (Z_OK, after) at body
    have env : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨rc, heap1, returned, privateState, actual, final, _, _, _, _, _, outcome⟩ :=
      inflate_leave_default_public_accounting env current loopAllocator packet bits
    have same := Except.ok.inj (actual.symm.trans body)
    have selected : rc = Z_OK := congrArg Prod.fst same
    have heaps : heap1 = after := congrArg Prod.snd same
    subst heap1
    have states : privateState = state := Option.some.inj (final.good.live.hs.symm.trans good.live.hs)
    subst privateState
    rcases outcome with ordinary | memory
    · rw [selected] at ordinary
      have ret : regs.ret = Z_OK :=
        (leave_return_original_ret ordinary.1 (by decide : Z_OK ≠ Z_BUF_ERROR)).symm
      have paused := inflate_run_leave_pause E invariant buffers nonnull inputValid flush run ret current.good.live.hs
      unfold PauseGood at *
      rw [ordinary.2.2]
      exact paused
    · exact False.elim ((by decide : Z_OK ≠ Z_MEM_ERROR) (selected.symm.trans memory.1))

/-- `int inflate(z_streamp strm, int flush)`.
A real default NO_FLUSH OK result retains a resumable private mode on the
same actual public heap after cleanup. No history or callee result is assumed. -/
theorem inflate_public_ok_pause
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (Z_OK, after))
    (good : Good after r zs stream state) : PauseGood state := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, Z_NO_FLUSH⟩
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
    exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_OK) impossible)
  · have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by intro null; exact rejected (by simp [null])
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    have localBuffers := streamBuffers_syncAlloc invariant.good.fresh buffers
    obtain ⟨rc, heap1, bodyStream, bodyState, bytes, bodyRun, current, finalAllocator,
      get, size, ro⟩ :=
      inflate_default_view_local_state_return env allocated allocator localBuffers nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have actual : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (rc, freeWin heap1 (syncBuf h)) := by
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
    have code : rc = Z_OK := congrArg Prod.fst same
    have heapEq : freeWin heap1 (syncBuf h) = after := congrArg Prod.snd same
    rw [code] at bodyRun
    have final := current.free_local get size
    have finalGet : r.get (freeWin heap1 (syncBuf h)) = some stream := by
      rw [heapEq]
      exact good.live.hz
    have sameStream : bodyStream = stream := Option.some.inj (final.good.live.hz.symm.trans finalGet)
    have finalStateGet : (freeWin heap1 (syncBuf h)).istates zs = some state := by
      rw [heapEq]
      exact good.live.hs
    have sameState : bodyState = state := Option.some.inj (final.good.live.hs.symm.trans finalStateGet)
    have paused := inflate_body_ok_pause env allocated allocator localBuffers nonnull inputValid rfl bodyRun current.good
    rw [sameState] at paused
    exact paused

/-- The original six-interface mode conclusion, with the stronger fact
that no successful ordinary pause remains in DICT at all. -/
theorem inflate_public_ok_normal_modes
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (Z_OK, after))
    (good : Good after r zs stream state) :
    state.mode ≠ SYNC ∧ state.mode ≠ MEM ∧ state.mode ≠ BAD ∧
      (state.mode = DICT → state.havedict ≠ 0) := by
  obtain ⟨low, bad, dictionary⟩ := inflate_public_ok_pause invariant allocator buffers run good
  refine ⟨?_, ?_, bad, fun impossible => False.elim (dictionary impossible)⟩
  · intro equal
    rw [equal] at low
    exact (by decide : ¬ SYNC < MEM) low
  · intro equal
    rw [equal] at low
    exact (by decide : ¬ MEM < MEM) low

#print axioms inflate_public_ok_pause
#print axioms inflate_public_ok_normal_modes
#print axioms inflate_body_ok_pause
#print axioms inflate_run_leave_pause
end Zlib.Uncompr.Proof.InflatePause
