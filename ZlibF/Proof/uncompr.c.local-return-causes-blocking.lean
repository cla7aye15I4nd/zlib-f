import ZlibF.Proof.«uncompr.c.inflate-buffer-blocking»
import ZlibF.Proof.«uncompr.c.local-pause-blocking-basic»
import ZlibF.Proof.«uncompr.c.local-return-causes-zero»

namespace Zlib.Uncompr.Proof.LocalBufferBlocking
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inflate.Local Zlib.Uncompr.Proof.InflatePause
open Zlib.Uncompr.Proof.InflateBufferBlocking
set_option autoImplicit false

/-- All default mode groups have the same actual ordinary-OK wait cause. -/
theorem dispatch_leave_blocked
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) (get : after.istates zs = some returned) : Blocked regs := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal
  · exact Or.inl (Zlib.Uncompr.Proof.LocalBasicBlocked.basic_dispatch_leave_blocked
      E invariant buffers flush (Or.inl head) run ret get)
  · rcases dictionary with mode | mode
    · exact Or.inl (Zlib.Uncompr.Proof.LocalBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inl mode)) run ret get)
    · exact Or.inl (Zlib.Uncompr.Proof.LocalBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inr (Or.inl mode))) run ret get)
  · rcases type with mode | mode
    · exact Or.inl (Zlib.Uncompr.Proof.LocalBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inr (Or.inr (Or.inl mode)))) run ret get)
    · exact Or.inl (Zlib.Uncompr.Proof.LocalBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode))))) run ret get)
  · exact complex_dispatch_leave_blocked E flush (Or.inl stored) run
  · exact complex_dispatch_leave_blocked E flush (Or.inr (Or.inl construction)) run
  · exact complex_dispatch_leave_blocked E flush (Or.inr (Or.inr data)) run
  · rcases trailer with check | length
    · exact Or.inl (Zlib.Uncompr.Proof.LocalBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr check))))) run ret get)
    · obtain ⟨source, _⟩ := Zlib.Inflate.Local.inflate_LENGTH_default_state_boundary E invariant buffers length
      have actual := (inflate_dispatch_LENGTH E l length).trans source
      have fixed := xrun_regs_eq actual run
      have ended : regs.ret = Z_STREAM_END := by rw [←fixed]
      rw [ret] at ended
      contradiction
  · have actual := inflate_dispatch_terminal_run E l terminal
    have outcome := xrun_outcome_eq actual run
    have fixed := xrun_regs_eq actual run
    rcases terminal with done | bad | mem | sync
    · have ended : regs.ret = Z_STREAM_END := by rw [←fixed]; simp [terminalRegs, done]
      rw [ret] at ended; contradiction
    · have failed : regs.ret = Z_DATA_ERROR := by rw [←fixed]; simp [terminalRegs, bad, show BAD ≠ DONE from by decide]
      rw [ret] at failed; contradiction
    · simp [terminalExit, mem, show MEM ≠ DONE from by decide, show MEM ≠ BAD from by decide] at outcome
    · simp [terminalExit, sync, show SYNC ≠ DONE from by decide, show SYNC ≠ BAD from by decide,
        show SYNC ≠ MEM from by decide] at outcome

private def BlockingInv (cutoff : Nat) (r : ZStreamRef) (zs : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39

/-- The actual complete mode loop carries the last executed dispatch's
blocking cause to its ordinary OK leave. -/
theorem inflate_run_leave_blocked
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) : Blocked regs := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    Zlib.Inflate.Local.inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : BlockingInv cutoff r zs (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits⟩
  have step : ∀ before heap outcome finalRegs finalHeap, BlockingInv cutoff r zs before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => BlockingInv cutoff r zs finalRegs finalHeap
      | .error exit => exit = Ex.leave → finalRegs.ret = Z_OK → Blocked finalRegs := by
    intro before heap outcome finalRegs finalHeap valid actual
    obtain ⟨stream, state, remaining, j, packet, incoming⟩ := valid
    have env : Env c heap r zs stream state := ⟨E.strm, E.st, j.good.live.hz, j.good.live.hs⟩
    obtain ⟨_, _, _, nextZ, nextS, used, _, _, source, final, nextBuffers,
      _, _, _, _, _, nextBits, _⟩ := Zlib.Inflate.Local.inflate_dispatch_default_view_state_rank env j packet incoming
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    cases outcome with
    | ok value => cases value; exact ⟨nextZ, nextS, remaining.drop used, final, nextBuffers, nextBits⟩
    | error exit =>
      intro selected ok
      subst exit
      exact dispatch_leave_blocked env j packet flush actual ok final.good.live.hs
  rw [cut] at run
  exact xwhile_success_control_post _ _ step start run rfl ret

private theorem buffer_ret_ok {c : Ctx} {l : IL} (ret : PublicLeaveRet l)
    (selected : Z_BUF_ERROR = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
      l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) : l.ret = Z_OK := by
  by_cases condition : ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
      l.ret == Z_OK) = true
  · have selectedOK : (l.ret == Z_OK) = true := (Bool.and_eq_true_iff.mp condition).2
    exact beq_iff_eq.mp selectedOK
  · rw [ite_eq_right condition] at selected
    rcases ret with ok | ended | bad
    · exact ok
    · rw [ended] at selected; contradiction
    · rw [bad] at selected; contradiction

/-- The same actual complete body returning BUF has an exhausted final
caller cursor. Both direct-return exclusions and real leave bookkeeping
are proved from execution, including allocation failure. -/
theorem inflate_body_buffer_blocked
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (flush : c.flush = Z_NO_FLUSH)
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (Z_BUF_ERROR, after))
    (good : Zlib.Inflate.Local.LocalGood after cutoff r zs stream state) : stream.avail_in = 0 ∨ stream.avail_out = 0 := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, _, _, _, run, current,
    packet, bits, _, _, _, _, _, _, loopAllocator⟩ :=
    Zlib.Inflate.Local.inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
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
      inflate_leave_local_public_accounting env current loopAllocator packet bits
    have same := Except.ok.inj (actual.symm.trans body)
    have selected : rc = Z_BUF_ERROR := congrArg Prod.fst same
    have heaps : heap1 = after := congrArg Prod.snd same
    subst heap1
    have streams : returned = stream := Option.some.inj (final.good.live.hz.symm.trans good.live.hz)
    subst returned
    rcases outcome with ordinary | memory
    · have ret := Zlib.Inflate.Local.inflate_run_leave_ret_codes E invariant buffers nonnull inputValid run
      rw [selected] at ordinary
      have retOK := buffer_ret_ok (c := c) ret ordinary.1
      have blocked := inflate_run_leave_blocked E invariant buffers nonnull inputValid flush run retOK
      rcases blocked with input | output
      · exact Or.inl (inAvail.trans input)
      · exact Or.inr (outAvail.trans output)
    · exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_MEM_ERROR) (selected.symm.trans memory.1))

/-- The public call's real temporary cleanup does not change its returned
stream cursors. An actual NO_FLUSH BUF therefore exposes an exhausted one. -/
theorem inflate_public_buffer_final_blocked
    {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (Z_BUF_ERROR, after))
    (good : Zlib.Inflate.Local.LocalGood after cutoff r zs stream state) : stream.avail_in = 0 ∨ stream.avail_out = 0 := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, Z_NO_FLUSH⟩
  have allocated := Zlib.Inflate.Local.default_state_syncAlloc invariant
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
    obtain ⟨rc, heap1, bodyStream, bodyState, bytes, bodyRun, current, _, get, size, ro⟩ :=
      Zlib.Inflate.Local.inflate_default_view_local_state_return env allocated allocator localBuffers nonnull inputValid
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
    have finalGet : r.get (freeWin heap1 (syncBuf h)) = some stream := by rw [heapEq]; exact good.live.hz
    have sameStream : bodyStream = stream := Option.some.inj (final.good.live.hz.symm.trans finalGet)
    rw [←sameStream]
    exact inflate_body_buffer_blocked env allocated allocator localBuffers nonnull inputValid rfl bodyRun current.good

/-- `int inflate(z_streamp strm, int flush)`.
On the same actual default NO_FLUSH BUF run, zero whole-call progress and
actual blocking imply that the original offered input or output was empty.
No callee contract or new public precondition is assumed. -/
theorem inflate_public_buffer_blocked
    {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {used made : Nat}
    (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (Z_BUF_ERROR, after))
    (good : Zlib.Inflate.Local.LocalGood after cutoff r zs stream state) (accounting : StreamAccounting z stream used made) :
    z.avail_in = 0 ∨ z.avail_out = 0 := by
  obtain ⟨usedZero, madeZero⟩ := Zlib.Uncompr.Proof.LocalBufferCause.inflate_public_buffer_zero
    invariant allocator buffers run good accounting
  have inputCount := accounting.2.2.1
  have outputCount := accounting.2.2.2.1
  rw [usedZero] at inputCount
  rw [madeZero] at outputCount
  rcases inflate_public_buffer_final_blocked invariant allocator buffers run good with input | output
  · left
    rw [input] at inputCount
    exact UInt32.toNat_inj.mp (by omega)
  · right
    rw [output] at outputCount
    exact UInt32.toNat_inj.mp (by omega)

#print axioms complex_dispatch_leave_blocked
#print axioms inflate_run_leave_blocked
#print axioms inflate_public_buffer_blocked
end Zlib.Uncompr.Proof.LocalBufferBlocking
