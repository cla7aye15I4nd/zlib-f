import ZlibF.Proof.«inflate.c.default-view-public-progress»
import ZlibF.Proof.«inflate.c.default-view-return-codes»
import ZlibF.Proof.«inflate.c.direct-terminal-loop»

/-!
# inflate.c: the error clauses of one default call

After the entry checks pass and the decoder is not in `SYNC`, the call never
returns `Z_STREAM_ERROR`: the loop reaches `SYNC` only if it started there.
`Z_BUF_ERROR` is returned only without progress or under `Z_FINISH`, which is
the `inf_leave` rule of the source.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The loop state of a call that did not start in `SYNC`. -/
def NoSyncLoopInv (r : ZStreamRef) (zs : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39 ∧
    s.mode ≠ SYNC

theorem inflate_dispatch_no_sync_step
    {c : Ctx} {r : ZStreamRef} {zs : Nat}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : NoSyncLoopInv r zs l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => NoSyncLoopInv r zs regs after
    | .error exit => ∀ code, exit = .ret code → code ≠ Z_STREAM_ERROR := by
  obtain ⟨stream, privateState, bs, invariant, buffers, incoming, notSync⟩ := current
  have env : Env c h r zs stream privateState :=
    ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  cases outcome with
  | ok value =>
    cases value
    obtain ⟨outcome, nextRegs, nextHeap, nextZ, nextS, used, made, _, source, final,
      packet, _, _, _, _, _, bits, _⟩ :=
      inflate_dispatch_default_view_state_rank env invariant buffers incoming
    have same := Except.ok.inj (source.symm.trans run)
    cases same
    have low := inflate_dispatch_normal_low env invariant buffers incoming run final.good.live.hs
    refine ⟨nextZ, nextS, bs.drop used, final, packet, bits, ?_⟩
    intro sync
    rw [sync] at low
    exact (by decide : ¬ SYNC < MEM) low
  | error exit =>
    intro code selected refused
    subst selected
    subst refused
    obtain ⟨modes, _, _⟩ :=
      inflate_dispatch_direct_terminal env invariant buffers incoming run (Or.inr rfl)
    rcases modes with ⟨_, impossible⟩ | ⟨sync, _⟩
    · exact (by decide : Z_STREAM_ERROR ≠ Z_MEM_ERROR) impossible
    · exact notSync sync

theorem inflate_default_no_sync_loop
    {c : Ctx} {r : ZStreamRef} {zs : Nat} {l regs : IL} {h after : Heap} {exit : Ex}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (current : NoSyncLoopInv r zs l h)
    (run : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after)) :
    ∀ code, exit = .ret code → code ≠ Z_STREAM_ERROR := by
  apply xwhile_success_control_post (NoSyncLoopInv r zs)
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
    ⟨z, entryState, bs, current, packet, bits, entryMode⟩ run code rfl

/-- The local body: no `Z_STREAM_ERROR`, and `Z_BUF_ERROR` only without
progress or under `Z_FINISH`. -/
theorem inflate_default_view_local_error_clauses
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (notSync : s.mode ≠ SYNC)
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
      rc ≠ Z_STREAM_ERROR ∧ (rc = Z_BUF_ERROR → (used = 0 ∧ made = 0) ∨ c.flush = Z_FINISH) := by
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
  refine ⟨otherRc, otherHeap, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, accounting, ?_⟩
  cases exit with
  | ret value =>
    obtain ⟨sameRc, _, _, _, direct⟩ := trace
    have notStream := inflate_run_default_no_stream_error E invariant buffers nonnull inputValid
      notSync run
    refine ⟨by rw [sameRc]; exact notStream, ?_⟩
    intro buffer
    exfalso
    rw [sameRc] at buffer
    rw [buffer] at direct
    unfold DirectInflateCode at direct
    revert direct
    decide
  | leave =>
    obtain ⟨_, availIn, _, availOut, outcome⟩ := trace
    have ret := inflate_run_leave_ret_codes E invariant buffers nonnull inputValid run
    rcases outcome with success | failure
    · have ordinary : OrdinaryPublicCode otherRc :=
        success.1.symm ▸ leave_return_ordinary_code regs c.flush ret
      refine ⟨?_, ?_⟩
      · rcases ordinary with e | e | e | e <;> rw [e] <;> decide
      · intro buffer
        have returned := buffer.symm.trans success.1
        by_cases finish : c.flush = Z_FINISH
        · exact Or.inr finish
        · left
          have savedInput := inflate_run_default_view_input_base E invariant buffers nonnull
            inputValid run
          obtain ⟨lower, upper⟩ := inflate_run_default_view_output_base E invariant buffers
            nonnull inputValid run
          have finishFalse : (c.flush == Z_FINISH) = false := by simpa using finish
          by_cases condition : (regs.in_ - regs.have_ == 0 && regs.out_ - regs.left == 0) = true
          · have inputZero : regs.in_ - regs.have_ = 0 := by
              simp only [Bool.and_eq_true, beq_iff_eq] at condition
              exact condition.1
            have outputZero : regs.out_ - regs.left = 0 := by
              simp only [Bool.and_eq_true, beq_iff_eq] at condition
              exact condition.2
            have inCount := accounting.2.2.1
            have outCount := accounting.2.2.2.1
            rw [availIn] at inCount
            rw [availOut] at outCount
            have haveLe : regs.have_.toNat ≤ regs.in_.toNat := by
              rw [savedInput]
              omega
            have inEq : regs.in_.toNat = regs.have_.toNat := by
              have sub := congrArg UInt32.toNat inputZero
              rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr haveLe)] at sub
              simp at sub
              omega
            have leftLe : regs.left.toNat ≤ regs.out_.toNat := by omega
            have outEq : regs.out_.toNat = regs.left.toNat := by
              have sub := congrArg UInt32.toNat outputZero
              rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr leftLe)] at sub
              simp at sub
              omega
            have savedInNat : regs.in_.toNat = z.avail_in.toNat := by rw [savedInput]
            constructor <;> omega
          · exfalso
            have conditionFalse : (regs.in_ - regs.have_ == 0 && regs.out_ - regs.left == 0) = false := by
              simpa using condition
            simp only [conditionFalse, finishFalse, Bool.false_or, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte] at returned
            rcases ret with e | e | e <;> rw [e] at returned <;> exact absurd returned (by decide)
    · refine ⟨?_, ?_⟩
      · rw [failure.1]
        decide
      · intro buffer
        exact absurd (buffer.symm.trans failure.1) (by decide)

#print axioms inflate_run_default_no_stream_error
#print axioms inflate_default_view_local_error_clauses

end Zlib.Inflate.Proofs
