import ZlibF.Proof.«inflate.c.leave-cause-modes»
import ZlibF.Proof.«inflate.c.output-base-run»
import ZlibF.Proof.«inflate.c.default-view-dispatch-rank»

/-!
# inflate.c: the registers at `inf_leave` in the default configuration

When the default loop leaves with `ret == Z_OK`, it leaves for a leave reason
(no input, no output space, or a `Z_BLOCK`/`Z_TREES` stop), and the saved
output count `out` is still the caller's `avail_out`: CHECK's rebase of `out`
is followed in the same call by `Z_STREAM_END` or by `BAD` and
`Z_DATA_ERROR`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `case BAD: ret = Z_DATA_ERROR; goto inf_leave;` -/
theorem inflate_dispatch_BAD_leave {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = BAD) :
    runX (inflate_dispatch c) l h = .ok ((.error .leave, { l with ret := Z_DATA_ERROR }), h) := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
    LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD]
  all_goals rfl

/-- The default modes exclude the gzip header field modes. -/
theorem default_mode_not_strings {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (invariant : DefaultStateJ h r zs z s) (notHeader : ¬ GzipHeaderMode s) :
    s.mode ≠ FLAGS ∧ s.mode ≠ TIME ∧ s.mode ≠ OS ∧ s.mode ≠ EXLEN ∧
      s.mode ≠ EXTRA ∧ s.mode ≠ NAME ∧ s.mode ≠ COMMENT := by
  rcases invariant.modes with head | ⟨low, _⟩ | header
  · rw [head]
    decide
  · exact absurd header notHeader
  · have bound := UInt32.le_iff_toNat_le.mp low
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro equal <;> rw [equal] at bound <;>
      exact absurd bound (by decide)

def LeaveLoopInv (r : ZStreamRef) (zs : Nat) (base : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ DispatchBuffers h r l bs ∧
    l.bits.toNat ≤ 39 ∧ (l.out_.toNat = base ∨ s.mode = BAD)

/-- One default dispatch keeps the saved output count or enters `BAD`, and a
leave with `ret == Z_OK` has a leave reason and the saved output count. -/
theorem inflate_dispatch_leave_loop_step
    {c : Ctx} {r : ZStreamRef} {zs base : Nat}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : LeaveLoopInv r zs base l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => LeaveLoopInv r zs base regs after
    | .error exit => exit = .leave → regs.ret = Z_OK →
        LeaveCause c.flush regs ∧ regs.out_.toNat = base := by
  obtain ⟨z, s, bs, invariant, buffers, incoming, saved⟩ := current
  have E : Env c h r zs z s := ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  by_cases bad : s.mode = BAD
  · have same := Except.ok.inj ((inflate_dispatch_BAD_leave E l bad).symm.trans run)
    cases same
    intro _ ret
    exact absurd ret (by decide : Z_DATA_ERROR ≠ Z_OK)
  have savedBase : l.out_.toNat = base := saved.resolve_right bad
  obtain ⟨otherOutcome, otherRegs, otherHeap, stream, privateState, used, _, _, source,
    final, packet, _, _, _, _, _, bits, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers incoming
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  have reset : regs.out_ = l.out_ ∨ (outcome = .error Ex.leave ∧ (regs.ret = Z_STREAM_END ∨ privateState.mode = LENGTH)) ∨
      (outcome = .ok () ∧ privateState.mode = BAD) := by
    by_cases check : s.mode = CHECK
    · obtain ⟨o2, r2, h2, z2, s2, _, _, source2, final2, _, _, _, _, _, _, _, _, _, _, _, _,
        resetCheck, _⟩ :=
        inflate_CHECK_default_state_accounting_rank E invariant buffers check incoming
      have same2 := Except.ok.inj (((inflate_dispatch_CHECK E l check).trans source2).symm.trans run)
      cases same2
      have sameState : s2 = privateState := Option.some.inj (final2.good.live.hs.symm.trans final.good.live.hs)
      subst s2
      exact resetCheck
    · exact Or.inl (inflate_dispatch_output_base_noncheck E check run)
  cases outcome with
  | ok value =>
    cases value
    refine ⟨stream, privateState, bs.drop used, final, packet, bits, ?_⟩
    rcases reset with kept | ⟨stopped, _⟩ | ⟨_, entered⟩
    · exact Or.inl (by rw [kept]; exact savedBase)
    · cases stopped
    · exact Or.inr entered
  | error exit =>
    intro leave ret
    subst exit
    by_cases header : GzipHeaderMode s
    · sorry
    refine ⟨leaveAt_inflate_dispatch E (default_mode_not_strings invariant header) run, ?_⟩
    rcases reset with kept | ⟨_, ended | waiting⟩ | ⟨stopped, _⟩
    · rw [kept]
      exact savedBase
    · exact absurd (ended.symm.trans ret) (by decide)
    · sorry
    · cases stopped

/-- The complete default loop: a leave with `ret == Z_OK` has a leave reason,
and its saved output count is the caller's `avail_out`. -/
theorem inflate_run_default_leave_cause
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error .leave, regs), after))
    (ret : regs.ret = Z_OK) :
    LeaveCause c.flush regs ∧ regs.out_.toNat = z.avail_out.toNat := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : LeaveLoopInv r zs z.avail_out.toNat (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits, Or.inl rfl⟩
  rw [cut] at run
  suffices key : Ex.leave = Ex.leave → regs.ret = Z_OK →
      LeaveCause c.flush regs ∧ regs.out_.toNat = z.avail_out.toNat from key rfl ret
  apply xwhile_success_control_post (LeaveLoopInv r zs z.avail_out.toNat)
    (fun exit l _ => exit = .leave → l.ret = Z_OK →
      LeaveCause c.flush l ∧ l.out_.toNat = z.avail_out.toNat) ?_ start run
  intro before heap outcome finalRegs finalHeap valid source
  have result := inflate_dispatch_leave_loop_step E.strm E.st before heap outcome
    finalRegs finalHeap valid source
  cases outcome with
  | ok value => cases value; exact result
  | error stopped => exact result

#print axioms inflate_run_default_leave_cause
end Zlib.Inflate.Proofs
