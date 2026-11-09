import ZlibF.Proof.«uncompr.c.inflate-return-causes»
import ZlibF.Proof.«inflate.c.default-view-return-trace»
import ZlibF.Proof.«inflate.c.default-view-input-accounting»

namespace Zlib.Uncompr.Proof.InflateBufferCause
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A CHECK rebase either rejects the checksum and continues in BAD, or
finishes immediately with END. A wait retains the original output base. -/
theorem check_output_base_cause
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CHECK)
    (run : runX (inflate_CHECK c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    regs.out_ = l.out_ ∨ (outcome = .ok () ∧ returned.mode = BAD) ∨
      (outcome = .error Ex.leave ∧ regs.ret = Z_STREAM_END) := by
  by_cases raw : s.wrap = 0
  · let state := { s with mode := LENGTH }
    let heap := setI h zs state
    have stateGet : heap.istates zs = some state := by simp only [heap, setI_istates_same]
    have source := (inflate_CHECK_nowrap E.st E.hs raw).trans
      (inflate_LENGTH_skip (l := l) E.st stateGet (Or.inl raw))
    right; right
    have same := xrun_outcome_eq source run
    have sameRegs := xrun_regs_eq source run
    exact ⟨same.symm, by rw [←sameRegs]⟩
  · have flags : s.flags = 0 := (invariant.trailer (Or.inl mode)).resolve_left raw
    have statics : Zlib.Crc32.Proofs.StaticsOK h := by
      unfold Zlib.Crc32.Proofs.StaticsOK
      rw [invariant.globals]
      exact ⟨rfl, rfl⟩
    obtain ⟨decision, current, used, pull, _, _, _, _, shape, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 32 (by decide)
    obtain ⟨rr, nextRegs, j, read, _, _, _, waitRun, fullRun⟩ :=
      inflate_CHECK_views_run (l.out_ - l.left) rfl E.strm E.st E.hz E.hs raw buffers.bits statics
        (fun _ => leaveOutputView_of_cursor invariant.good buffers.output)
    rw [pull] at read
    cases read
    rcases kinds with normal | wait
    · obtain ⟨_, value, badRun, acceptedRun⟩ := fullRun normal
      let state := chkS s (l.out_ - l.left) value
      by_cases invalid : (s.wrap &&& 4) ≠ 0 ∧
          (if s.flags ≠ 0 then current.hold else ZSWAP32 current.hold) ≠ state.check
      · obtain ⟨i, _, source⟩ := badRun invalid.1 invalid.2
        have sameState := xrun_state_eq (firstState := { state with mode := BAD }) source run
          (by simp only [state, tcBadHeap, setI_istates_same]) get
        right; left
        exact ⟨(xrun_outcome_eq source run).symm, by rw [←sameState]⟩
      · let next := { state with mode := LENGTH }
        let heap := setI (chkH h r zs z s (l.out_ - l.left) value) zs next
        have stateGet : heap.istates zs = some next := by simp only [heap, setI_istates_same]
        have source := (acceptedRun invalid).trans
          (inflate_LENGTH_skip E.st stateGet (Or.inr flags))
        right; right
        exact ⟨(xrun_outcome_eq source run).symm, by rw [←xrun_regs_eq source run]⟩
    · obtain ⟨_, _, _, source⟩ := waitRun wait
      left
      rw [←xrun_regs_eq source run]
      change current.out_ = l.out_
      rw [shape]

private def BaseInv (r : ZStreamRef) (zs : Nat) (base : UInt32) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39 ∧
    (l.out_ = base ∨ s.mode = BAD)

private def BaseExit (base : UInt32) (exit : Ex) (l : IL) : Prop :=
  l.out_ = base ∨ (exit = Ex.leave ∧ (l.ret = Z_STREAM_END ∨ l.ret = Z_DATA_ERROR))

/-- A real body exit that changed the saved output base must already have
an END or DATA result. Thus a later BUF selection cannot erase output credit. -/
theorem inflate_run_output_base_cause
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL} {exit : Ex}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after)) :
    BaseExit z.avail_out exit regs := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : BaseInv r zs z.avail_out (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits, Or.inl rfl⟩
  have step : ∀ before heap outcome finalRegs finalHeap, BaseInv r zs z.avail_out before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => BaseInv r zs z.avail_out finalRegs finalHeap
      | .error stopped => BaseExit z.avail_out stopped finalRegs := by
    intro before heap outcome finalRegs finalHeap valid actual
    obtain ⟨stream, state, remaining, j, buffers, incoming, base⟩ := valid
    have env : Env c heap r zs stream state := ⟨E.strm, E.st, j.good.live.hz, j.good.live.hs⟩
    obtain ⟨_, _, _, nextZ, nextS, used, _, _, source, final, nextBuffers,
      _, _, _, _, _, nextBits, _⟩ :=
      inflate_dispatch_default_view_state_rank env j buffers incoming
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    have next : finalRegs.out_ = z.avail_out ∨
        (outcome = .ok () ∧ nextS.mode = BAD) ∨
        (outcome = .error Ex.leave ∧ (finalRegs.ret = Z_STREAM_END ∨ finalRegs.ret = Z_DATA_ERROR)) := by
      rcases base with original | bad
      · by_cases check : state.mode = CHECK
        · have checkRun := (inflate_dispatch_CHECK env before check).symm.trans actual
          rcases check_output_base_cause env j buffers check checkRun final.good.live.hs with fixed | rejected | ended
          · exact Or.inl (fixed.trans original)
          · exact Or.inr (Or.inl rejected)
          · exact Or.inr (Or.inr ⟨ended.1, Or.inl ended.2⟩)
        · exact Or.inl ((inflate_dispatch_output_base_noncheck env check actual).trans original)
      · have terminal := inflate_dispatch_terminal_run env before (Or.inr (Or.inl bad))
        have selected := xrun_outcome_eq terminal actual
        have ret := xrun_regs_eq terminal actual
        right; right
        refine ⟨?_, Or.inr ?_⟩
        · simpa only [terminalExit, bad, or_true, ↓reduceIte] using selected.symm
        · rw [←ret]
          simp only [terminalRegs, bad, show BAD ≠ DONE from by decide, ↓reduceIte]
    cases outcome with
    | ok value =>
      cases value
      refine ⟨nextZ, nextS, remaining.drop used, final, nextBuffers, nextBits, ?_⟩
      rcases next with fixed | ⟨_, bad⟩ | ⟨impossible, _⟩
      · exact Or.inl fixed
      · exact Or.inr bad
      · cases impossible
    | error stopped =>
      rcases next with fixed | ⟨impossible, _⟩ | ⟨selected, ret⟩
      · exact Or.inl fixed
      · cases impossible
      · exact Or.inr ⟨Except.error.inj selected, ret⟩
  rw [cut] at run
  exact xwhile_success_control_post _ _ step start run

/-- The literal actual data_type/return suffix has this exact selected
result after all preceding operations succeed. It does not assume their safety. -/
theorem leaveReturn_selected (c : Ctx) (l : IL) (z : ZStream) :
    ResultPostM (fun code => code =
      (if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) (leaveReturn c l z) := by
  unfold leaveReturn
  repeat' first
    | with_reducible refine resultPostM_bind_right (fun _ => ?_)
    | with_reducible refine resultPostM_pure _ ?_
    | split
    | rfl
  all_goals
    simp only [*, ↓reduceIte]
    exact resultPostM_pure _ rfl

private theorem buffer_selection {c : Ctx} {l : IL}
    (flush : c.flush = Z_NO_FLUSH) (ret : PublicLeaveRet l)
    (code : Z_BUF_ERROR = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
      l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) :
    l.ret = Z_OK ∧ l.in_ = l.have_ ∧ l.out_ = l.left := by
  have notBuffer : l.ret ≠ Z_BUF_ERROR := by
    rcases ret with ret | ret | ret <;> rw [ret] <;> decide
  have selected : ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
      l.ret == Z_OK) = true := by
    by_cases selected : ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
      l.ret == Z_OK) = true
    · exact selected
    · rw [if_neg selected] at code
      exact False.elim (notBuffer code.symm)
  have parts : (l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) = true ∧
      (l.ret == Z_OK) = true := by simpa only [Bool.and_eq_true] using selected
  have zeros : l.in_ - l.have_ = 0 ∧ l.out_ - l.left = 0 := by
    simpa only [flush, Z_NO_FLUSH, Z_FINISH, show ((0 : Int32) == 4) = false from rfl,
      Bool.or_false, Bool.and_eq_true, beq_iff_eq] using parts.1
  exact ⟨beq_iff_eq.mp parts.2,
    by simpa only [UInt32.zero_add] using UInt32.sub_eq_iff_eq_add.mp zeros.1,
    by simpa only [UInt32.zero_add] using UInt32.sub_eq_iff_eq_add.mp zeros.2⟩

/-- NO_FLUSH selects BUF only on zero real consumption and production.
The proof includes CHECK's actual output-credit rebase, so it concerns the
whole original caller segment, not merely the suffix after CHECK. -/
theorem inflate_body_buffer_zero
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {used made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (flush : c.flush = Z_NO_FLUSH)
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (Z_BUF_ERROR, after))
    (good : Good after r zs stream state) (accounting : StreamAccounting z stream used made) :
    used = 0 ∧ made = 0 := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, loopUsed, loopMade, _, run, current,
    packet, bits, _, _, inCount, _, outCount, _, loopAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  rw [bind_app, run] at body
  cases exit with
  | ret code =>
    change (Except.ok (code, loopHeap) : Except Fault (Int32 × Heap)) = .ok (Z_BUF_ERROR, after) at body
    have selected : code = Z_BUF_ERROR := congrArg Prod.fst (Except.ok.inj body)
    have codes := inflate_run_direct_codes run
    rw [selected] at codes
    exact False.elim (by rcases codes with codes | codes | codes <;> revert codes <;> decide)
  | leave =>
    change inflate_leave c regs loopHeap = .ok (Z_BUF_ERROR, after) at body
    have env : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨rc, heap1, returned, privateState, actual, final, _, _, inAvail, _, outAvail, outcome⟩ :=
      inflate_leave_default_public_accounting env current loopAllocator packet bits
    have same := Except.ok.inj (actual.symm.trans body)
    have selected : rc = Z_BUF_ERROR := congrArg Prod.fst same
    have heaps : heap1 = after := congrArg Prod.snd same
    subst heap1
    have streams : returned = stream := Option.some.inj (final.good.live.hz.symm.trans good.live.hz)
    subst returned
    rcases outcome with ordinary | memory
    · have ret := inflate_run_leave_ret_codes E invariant buffers nonnull inputValid run
      rw [selected] at ordinary
      obtain ⟨retOK, inZero, outZero⟩ := buffer_selection flush ret ordinary.1
      have base := inflate_run_output_base_cause E invariant buffers nonnull inputValid run
      have originalOut : regs.out_ = z.avail_out := by
        rcases base with original | ⟨_, ended | error⟩
        · exact original
        · exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) (retOK.symm.trans ended))
        · exact False.elim ((by decide : Z_OK ≠ Z_DATA_ERROR) (retOK.symm.trans error))
      have originalIn := inflate_run_default_view_input_base E invariant buffers nonnull inputValid run
      have inSame : stream.avail_in = z.avail_in := inAvail.trans (inZero.symm.trans originalIn)
      have outSame : stream.avail_out = z.avail_out := outAvail.trans (outZero.symm.trans originalOut)
      have consumed := accounting.2.2.1
      have produced := accounting.2.2.2.1
      rw [inSame] at consumed
      rw [outSame] at produced
      omega
    · exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_MEM_ERROR) (selected.symm.trans memory.1))

/-- `int inflate(z_streamp strm, int flush)`.
An actual default public NO_FLUSH BUF return has zero whole-call consumed
and produced bytes, including CHECK credit and temporary-object cleanup. -/
theorem inflate_public_buffer_zero
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState} {used made : Nat}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (Z_BUF_ERROR, after))
    (good : Good after r zs stream state) (accounting : StreamAccounting z stream used made) :
    used = 0 ∧ made = 0 := by
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
    exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_BUF_ERROR) impossible)
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
    have code : rc = Z_BUF_ERROR := congrArg Prod.fst same
    have heapEq : freeWin heap1 (syncBuf h) = after := congrArg Prod.snd same
    rw [code] at bodyRun
    have final := current.free_local get size
    have finalGet : r.get (freeWin heap1 (syncBuf h)) = some stream := by
      rw [heapEq]
      exact good.live.hz
    have sameStream : bodyStream = stream := Option.some.inj (final.good.live.hz.symm.trans finalGet)
    have bodyAccounting : StreamAccounting z bodyStream used made := by
      rw [sameStream]
      exact accounting
    exact inflate_body_buffer_zero env allocated allocator localBuffers nonnull inputValid rfl
      bodyRun current.good bodyAccounting

#print axioms leaveReturn_selected
#print axioms inflate_public_buffer_zero
#print axioms inflate_body_buffer_zero
#print axioms inflate_run_output_base_cause
end Zlib.Uncompr.Proof.InflateBufferCause
