import ZlibF.Proof.«inflate.c.entry-header»
import ZlibF.Proof.«inflate.c.default-view-public-progress»
import ZlibF.Proof.«inflate.c.default-view-return-codes»
import ZlibF.Proof.«inflate.c.direct-terminal-loop»
import ZlibF.Proof.«inflate.c.leave-cause-run»

/-!
# inflate.c: the error clauses of one default call

After the entry checks pass and the decoder is not in `SYNC`, the call never
returns `Z_STREAM_ERROR`: the loop reaches `SYNC` only if it started there.
`Z_BUF_ERROR` is returned only when no input was consumed and no output was
made, or under `Z_FINISH`. zlib resets its local output count in `CHECK`; in
the default configuration that reset is followed in the same call by
`Z_STREAM_END` or `Z_DATA_ERROR` (`inflate.c.leave-cause-run`). Every leave
with `ret == Z_OK` has no input, no output space, or a `Z_BLOCK`/`Z_TREES`
stop, which gives the progress clause.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The loop state of a call that did not start in `SYNC`. -/
def NoSyncLoopInv (c : Ctx) (r : ZStreamRef) (zs : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ HeaderLocal c h r s l ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39 ∧
    s.mode ≠ SYNC

theorem inflate_dispatch_no_sync_step
    {c : Ctx} {r : ZStreamRef} {zs : Nat}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : NoSyncLoopInv c r zs l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => NoSyncLoopInv c r zs regs after
    | .error exit => ∀ code, exit = .ret code → code ≠ Z_STREAM_ERROR := by
  obtain ⟨stream, privateState, bs, invariant, local_, buffers, incoming, notSync⟩ := current
  have env : Env c h r zs stream privateState :=
    ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  cases outcome with
  | ok value =>
    cases value
    obtain ⟨outcome, nextRegs, nextHeap, nextZ, nextS, used, made, _, source, final,
      ⟨rest, _, packet⟩, _, _, _, _, _, bits, finalLocal, _⟩ :=
      inflate_dispatch_default_view_state_rank env invariant buffers local_ incoming
    have same := Except.ok.inj (source.symm.trans run)
    cases same
    have low := inflate_dispatch_normal_low env invariant buffers local_ incoming run final.good.live.hs
    refine ⟨nextZ, nextS, rest, final, finalLocal, packet, bits, ?_⟩
    intro sync
    rw [sync] at low
    exact (by decide : ¬ SYNC < MEM) low
  | error exit =>
    intro code selected refused
    subst selected
    subst refused
    obtain ⟨modes, _, _⟩ :=
      inflate_dispatch_direct_terminal env invariant buffers local_ incoming run (Or.inr rfl)
    rcases modes with ⟨_, impossible⟩ | ⟨sync, _⟩
    · exact (by decide : Z_STREAM_ERROR ≠ Z_MEM_ERROR) impossible
    · exact notSync sync

theorem inflate_default_no_sync_loop
    {c : Ctx} {r : ZStreamRef} {zs : Nat} {l regs : IL} {h after : Heap} {exit : Ex}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (current : NoSyncLoopInv c r zs l h)
    (run : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after)) :
    ∀ code, exit = .ret code → code ≠ Z_STREAM_ERROR := by
  apply xwhile_success_control_post (NoSyncLoopInv c r zs)
    (fun exit _ _ => ∀ code, exit = .ret code → code ≠ Z_STREAM_ERROR) ?_ current run
  intro before heap outcome finalRegs finalHeap valid source
  have result := inflate_dispatch_no_sync_step root state before heap outcome
    finalRegs finalHeap valid source
  cases outcome with
  | ok value =>
    cases value
    exact result
  | error stopped => exact result

/-- A body run that did not start in `SYNC` has no direct `Z_STREAM_ERROR`. -/
theorem inflate_run_default_no_stream_error
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL} {code : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (notSync : s.mode ≠ SYNC)
    (run : runX (inflate_run c) IL.init h = .ok ((.error (.ret code), regs), after)) :
    code ≠ Z_STREAM_ERROR := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _, stateEq⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have entryMode : entryState.mode ≠ SYNC := by
    rw [stateEq]
    by_cases type : s.mode = TYPE
    · rw [if_pos type]
      change TYPEDO ≠ SYNC
      decide
    · rw [if_neg type]
      exact notSync
  rw [cut] at run
  exact inflate_default_no_sync_loop E.strm E.st
    ⟨z, entryState, bs, current, entryLocal, packet, bits, entryMode⟩ run code rfl

/-- A `Z_BUF_ERROR` from the `inf_leave` return expression: `ret` was
`Z_OK`, and either nothing was used and nothing made since the saved counts,
or the flush is `Z_FINISH`. -/
theorem leave_buf_facts {l : IL} {flush : Int32} (codes : PublicLeaveRet l)
    (returned : Z_BUF_ERROR = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || flush == Z_FINISH) &&
      l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) :
    l.ret = Z_OK ∧ ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0) = true ∨ flush = Z_FINISH) := by
  by_cases condition : ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || flush == Z_FINISH) &&
      l.ret == Z_OK) = true
  · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at condition
    obtain ⟨stopped, ok⟩ := condition
    refine ⟨ok, ?_⟩
    rcases stopped with nothing | finish
    · left
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact nothing
    · exact Or.inr finish
  · rw [if_neg condition] at returned
    exfalso
    rcases codes with e | e | e <;> rw [e] at returned <;> exact absurd returned (by decide)

/-- The local body: no `Z_STREAM_ERROR`; `Z_BUF_ERROR` only without progress
or under `Z_FINISH`; and with input, output space and a flush other than
`Z_BLOCK`/`Z_TREES`, a `Z_BUF_ERROR` call has made progress. -/
theorem inflate_default_view_local_error_clauses
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s)) (notSync : s.mode ≠ SYNC)
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes used made,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      StreamAccounting z stream used made ∧
      rc ≠ Z_STREAM_ERROR ∧ (rc = Z_BUF_ERROR → (used = 0 ∧ made = 0) ∨ c.flush = Z_FINISH) ∧
      (z.avail_in ≠ 0 → z.avail_out ≠ 0 → c.flush ≠ Z_BLOCK → c.flush ≠ Z_TREES →
        rc = Z_BUF_ERROR → used ≠ 0 ∨ made ≠ 0) := by
  obtain ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, _, _, accounting, _⟩ :=
    inflate_default_view_local_input_accounting E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  obtain ⟨otherRc, otherHeap, otherZ, otherS, _, exit, regs, loopHeap, loopZ, loopS,
    used2, made2, source, otherFinal, _, _, _, _, run, current, _, _, _, _, _, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  have same := Except.ok.inj (source.symm.trans bodyRun)
  cases same
  have sameZ : otherZ = stream :=
    Option.some.inj (otherFinal.good.live.hz.symm.trans final.good.live.hz)
  subst otherZ
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, accounting, ?_⟩
  cases exit with
  | ret value =>
    obtain ⟨sameRc, _, _, _, direct⟩ := trace
    have notStream := inflate_run_default_no_stream_error E invariant buffers nonnull inputValid
      notSync run
    have noBuffer : rc ≠ Z_BUF_ERROR := by
      intro buffer
      rw [sameRc] at buffer
      rw [buffer] at direct
      unfold DirectInflateCode at direct
      revert direct
      decide
    exact ⟨by rw [sameRc]; exact notStream, fun buffer => absurd buffer noBuffer,
      fun _ _ _ _ buffer => absurd buffer noBuffer⟩
  | leave =>
    obtain ⟨_, availIn, _, availOut, outcome⟩ := trace
    have ret := inflate_run_leave_ret_codes E invariant buffers nonnull inputValid local_ run
    rcases outcome with success | failure
    · have ordinary : OrdinaryPublicCode rc :=
        success.1.symm ▸ leave_return_ordinary_code regs c.flush ret
      have inCount := accounting.2.2.1
      rw [availIn] at inCount
      have outCount := accounting.2.2.2.1
      rw [availOut] at outCount
      refine ⟨?_, ?_, ?_⟩
      · rcases ordinary with e | e | e | e <;> rw [e] <;> decide
      · intro buffer
        obtain ⟨retOk, condition⟩ := leave_buf_facts ret (buffer.symm.trans success.1)
        rcases condition with condition | finish
        · left
          obtain ⟨_, saved⟩ :=
            inflate_run_default_leave_cause E invariant buffers nonnull inputValid local_ run retOk
          obtain ⟨lower, _⟩ :=
            inflate_run_default_view_output_base E invariant buffers nonnull inputValid local_ run
          have savedInput := inflate_run_default_view_input_base E invariant buffers nonnull
            inputValid run
          simp only [Bool.and_eq_true, beq_iff_eq] at condition
          obtain ⟨inputZero, outputZero⟩ := condition
          have haveLe : regs.have_.toNat ≤ regs.in_.toNat := by
            rw [savedInput]
            omega
          have inEq : regs.in_.toNat = regs.have_.toNat := by
            have sub := congrArg UInt32.toNat inputZero
            rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr haveLe)] at sub
            simp at sub
            omega
          have outEq : regs.out_.toNat = regs.left.toNat := by
            have sub := congrArg UInt32.toNat outputZero
            rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr lower)] at sub
            simp at sub
            omega
          have savedInNat : regs.in_.toNat = z.avail_in.toNat := by rw [savedInput]
          exact ⟨by omega, by omega⟩
        · exact Or.inr finish
      · intro inputNonzero outputNonzero notBlock notTrees buffer
        obtain ⟨retOk, _⟩ := leave_buf_facts ret (buffer.symm.trans success.1)
        obtain ⟨cause, _⟩ :=
          inflate_run_default_leave_cause E invariant buffers nonnull inputValid local_ run retOk
        apply Classical.byContradiction
        intro none
        simp only [not_or, ne_eq, Decidable.not_not] at none
        obtain ⟨usedZero, madeZero⟩ := none
        rcases cause with empty | full | block | trees | code
        · apply inputNonzero
          apply UInt32.toNat_inj.mp
          rw [empty] at inCount
          simp only [UInt32.toNat_zero] at inCount ⊢
          omega
        · apply outputNonzero
          apply UInt32.toNat_inj.mp
          rw [full] at outCount
          simp only [UInt32.toNat_zero] at outCount ⊢
          omega
        · exact notBlock block
        · exact notTrees trees
        · exact code retOk
    · have noBuffer : rc ≠ Z_BUF_ERROR := by
        rw [failure.1]
        decide
      refine ⟨?_, fun buffer => absurd buffer noBuffer, fun _ _ _ _ buffer => absurd buffer noBuffer⟩
      rw [failure.1]
      decide

#print axioms inflate_run_default_no_stream_error
#print axioms inflate_default_view_local_error_clauses

/-- The public call with accepted entry arguments, not in `SYNC`: no
`Z_STREAM_ERROR`; `Z_BUF_ERROR` only when no input was consumed and no output
was made, or under `Z_FINISH`; and with input, output space and a flush other
than `Z_BLOCK`/`Z_TREES`, a `Z_BUF_ERROR` call has made progress. -/
theorem inflate_default_view_public_error_clauses
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z) (flush : Int32) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (notSync : s.mode ≠ SYNC) :
    ∃ rc after stream state used made,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ StreamAccounting z stream used made ∧
      rc ≠ Z_STREAM_ERROR ∧ (rc = Z_BUF_ERROR → (used = 0 ∧ made = 0) ∨ flush = Z_FINISH) ∧
      (z.avail_in ≠ 0 → z.avail_out ≠ 0 → flush ≠ Z_BLOCK → flush ≠ Z_TREES →
        rc = Z_BUF_ERROR → used ≠ 0 ∨ made ≠ 0) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have local_ : HeaderLocal c (syncAlloc h) r s (dispatchRegs z s) := entry_header_local invariant.good.fresh entry flush
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have accepted : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = false := by
    cases input : z.next_in <;> cases output : z.next_out <;> simp_all
  obtain ⟨rc, heap1, stream, state, bytes, used, made, bodyRun, current, _,
    localGet, localSize, localRo, accounting, notStream, buffer, progress⟩ :=
    inflate_default_view_local_error_clauses env allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid local_ notSync
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, used, made, ?_, final, accounting,
    notStream, buffer, progress⟩
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
  rw [freeBuf_run localGet localRo]
  rfl

#print axioms inflate_default_view_public_error_clauses

end Zlib.Inflate.Proofs
