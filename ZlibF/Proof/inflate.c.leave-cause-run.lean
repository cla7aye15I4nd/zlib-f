import ZlibF.Proof.«inflate.c.leave-cause-modes»
import ZlibF.Proof.«inflate.c.output-base-run»
import ZlibF.Proof.«inflate.c.default-view-dispatch-rank»
import ZlibF.Proof.«inflate.c.no-input-check»

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
  · have bound := UInt32.le_iff_toNat_le.mp low
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro equal <;> rw [equal] at bound <;>
      exact absurd bound (by decide)
  · exact absurd header notHeader

def LeaveLoopInv (c : Ctx) (r : ZStreamRef) (zs : Nat) (base input : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ HeaderLocal c h r s l ∧ DispatchBuffers h r l bs ∧
    l.bits.toNat ≤ 39 ∧ (l.out_.toNat = base ∨ s.mode = BAD) ∧ l.have_.toNat ≤ input ∧
    (s.mode ≠ BAD → s.mode ≠ MEM → s.mode ≠ SYNC → l.bits.toNat ≤ 32) ∧
    (input = 0 → l.left.toNat ≠ base → AfterOutput s.mode l.bits)

/-- One default dispatch keeps the saved output count or enters `BAD`, and a
leave with `ret == Z_OK` has a leave reason, and the saved output count or
consumed input. CHECK rebases `out` and LENGTH may then leave; with no input
in the call that happens only before any output (`AfterOutput`). -/
theorem inflate_dispatch_leave_loop_step
    {c : Ctx} {r : ZStreamRef} {zs base input : Nat}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : LeaveLoopInv c r zs base input l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => LeaveLoopInv c r zs base input regs after
    | .error exit => exit = .leave → regs.ret = Z_OK →
        LeaveCause c.flush regs ∧ (regs.out_.toNat = base ∨ regs.have_.toNat ≠ input) := by
  obtain ⟨z, s, bs, invariant, local_, buffers, incoming, saved, consumed, held, afterOutput⟩ := current
  have E : Env c h r zs z s := ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  by_cases bad : s.mode = BAD
  · have same := Except.ok.inj ((inflate_dispatch_BAD_leave E l bad).symm.trans run)
    cases same
    intro _ ret
    exact absurd ret (by decide : Z_DATA_ERROR ≠ Z_OK)
  have savedBase : l.out_.toNat = base := saved.resolve_right bad
  obtain ⟨otherOutcome, otherRegs, otherHeap, stream, privateState, used, _, _, source,
    final, ⟨rest, _, packet⟩, _, _, count, _, _, bits, finalLocal, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers local_ incoming
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  have empty (noInput : input = 0) : l.have_ = 0 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_zero]
    omega
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
    have strong := HeldBits.strong E invariant buffers held run (fun v e => by cases e)
    refine ⟨stream, privateState, rest, final, finalLocal, packet, bits, ?_, by omega,
      fun notBad _ _ => inflate_dispatch_held_bound E invariant buffers local_ strong run final.good.live.hs notBad, ?_⟩
    · rcases reset with kept | ⟨stopped, _⟩ | ⟨_, entered⟩
      · exact Or.inl (by rw [kept]; exact savedBase)
      · cases stopped
      · exact Or.inr entered
    · intro noInput
      exact inflate_dispatch_no_input_step E invariant buffers local_ incoming strong (empty noInput) base
        (afterOutput noInput) run final.good.live.hs rfl
  | error exit =>
    intro leave ret
    subst exit
    by_cases header : GzipHeaderMode s
    · have inRange : HEAD ≤ s.mode ∧ s.mode ≤ HCRC := by
        obtain ⟨low, high, _⟩ := header
        exact ⟨UInt32.le_trans (by decide : HEAD ≤ FLAGS) low, high⟩
      obtain ⟨_, _, _, _, _, _, _, run2, _, _, _, _, _, _, _, out, _, _, _, _, _, _, _, leaveCause, _⟩ :=
        inflate_dispatch_gzip_header_state_rank E invariant buffers header (local_ inRange.1 inRange.2) incoming
      rw [run] at run2
      cases run2
      exact ⟨Or.inl (leaveCause rfl), Or.inl (by rw [out]; exact savedBase)⟩
    refine ⟨leaveAt_inflate_dispatch E (default_mode_not_strings invariant header) run, ?_⟩
    rcases reset with kept | ⟨_, ended | waiting⟩ | ⟨stopped, _⟩
    · rw [kept]
      exact Or.inl savedBase
    · exact absurd (ended.symm.trans ret) (by decide)
    · -- CHECK rebased `out` and LENGTH left waiting for input
      by_cases check : s.mode ≠ CHECK
      · rw [inflate_dispatch_output_base_noncheck E check run]
        exact Or.inl savedBase
      have check : s.mode = CHECK := Classical.byContradiction check
      have run' := run
      rw [inflate_dispatch_CHECK E l check] at run'
      obtain ⟨_, regs2, after2, _, state2, _, _, run2, final2, _, _, _, _, _, left2, _, _, _, _, _, _, _, _,
        ⟨_, _, _, _, _, lengthFacts⟩⟩ :=
        inflate_CHECK_default_state_accounting_rank E invariant buffers check incoming
      obtain ⟨outcomeEq, regsEq, heapEq⟩ := runX_same run' run2
      subst outcomeEq regsEq heapEq
      have sameState : privateState = state2 := Option.some.inj (final.good.live.hs.symm.trans final2.good.live.hs)
      subst sameState
      obtain ⟨rebased, noneLeft, _⟩ := lengthFacts waiting
      by_cases noInput : input = 0
      · left
        by_cases moved : l.left.toNat = base
        · rw [rebased, left2]; exact moved
        · rcases afterOutput noInput moved with bad' | ⟨d, _⟩ | ⟨_, small⟩
          · exact absurd bad' bad
          · rw [check] at d; exact absurd d (by unfold DataTableMode; decide)
          · exact absurd waiting
              (inflate_dispatch_check_after E invariant buffers check (empty noInput) small run final.good.live.hs).1
      · right
        rw [noneLeft rfl]
        simpa using Ne.symm noInput
    · cases stopped

/-- The complete default loop: a leave with `ret == Z_OK` has a leave reason,
and its saved output count is the caller's `avail_out`. -/
theorem inflate_run_default_leave_cause
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s)) (held : HeldBits s)
    (run : runX (inflate_run c) IL.init h = .ok ((.error .leave, regs), after))
    (ret : regs.ret = Z_OK) :
    LeaveCause c.flush regs ∧
      (regs.out_.toNat = z.avail_out.toNat ∨ regs.have_.toNat ≠ z.avail_in.toNat) := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, entrySizes, entryFrame, entryHeapEq,
    entryStateEq⟩ := inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant current entrySizes entryFrame entryHeapEq entryStateEq local_
  have start : LeaveLoopInv c r zs z.avail_out.toNat z.avail_in.toNat (dispatchRegs z entryState) entryHeap := by
    refine ⟨z, entryState, bs, current, entryLocal, packet, bits, Or.inl rfl, Nat.le_refl _, ?_,
      fun _ moved => absurd rfl moved⟩
    intro notBad notMem notSync
    have bitsEq : (dispatchRegs z entryState).bits = s.bits := by
      rw [entryStateEq]
      split <;> rfl
    have modeOf (m : UInt32) (special : m = BAD ∨ m = MEM ∨ m = SYNC) (sm : s.mode = m) : entryState.mode = m := by
      rw [entryStateEq]
      split
      · next type => rw [sm] at type; subst type; rcases special with e | e | e <;> exact absurd e (by decide)
      · exact sm
    rw [bitsEq]
    exact held (fun e => notBad (modeOf _ (Or.inl rfl) e)) (fun e => notMem (modeOf _ (Or.inr (Or.inl rfl)) e))
      (fun e => notSync (modeOf _ (Or.inr (Or.inr rfl)) e))
  rw [cut] at run
  suffices key : Ex.leave = Ex.leave → regs.ret = Z_OK →
      LeaveCause c.flush regs ∧
        (regs.out_.toNat = z.avail_out.toNat ∨ regs.have_.toNat ≠ z.avail_in.toNat) from key rfl ret
  apply xwhile_success_control_post (LeaveLoopInv c r zs z.avail_out.toNat z.avail_in.toNat)
    (fun exit l _ => exit = .leave → l.ret = Z_OK →
      LeaveCause c.flush l ∧ (l.out_.toNat = z.avail_out.toNat ∨ l.have_.toNat ≠ z.avail_in.toNat)) ?_ start run
  intro before heap outcome finalRegs finalHeap valid source
  have result := inflate_dispatch_leave_loop_step E.strm E.st before heap outcome
    finalRegs finalHeap valid source
  cases outcome with
  | ok value => cases value; exact result
  | error stopped => exact result

#print axioms inflate_run_default_leave_cause
end Zlib.Inflate.Proofs
