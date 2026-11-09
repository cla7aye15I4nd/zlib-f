import ZlibF.Proof.«inflate.c.local-ret-construction»
import ZlibF.Proof.«inflate.c.ret-loop»
import ZlibF.Proof.«inflate.c.local-run»
import ZlibF.Proof.«inflate.c.loop-control-post»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Internal table errors can only persist until the next BAD dispatch.
All actual ordinary leaves already have a public return-register value. -/
theorem inflate_dispatch_ret_classification
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (initial : l.ret = Z_OK ∨ s.mode = BAD)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    (outcome = .ok () → regs.ret = Z_OK ∨ returned.mode = BAD) ∧
      (outcome = .error Ex.leave → PublicLeaveRet regs) := by
  by_cases bad : s.mode = BAD
  · have source := inflate_dispatch_terminal_run E l (Or.inr (Or.inl bad))
    have selected : outcome = .error Ex.leave := by
      simpa only [terminalExit, bad, or_true, ↓reduceIte] using (xrun_outcome_eq source run).symm
    have ret : regs.ret = Z_DATA_ERROR := by
      rw [← xrun_regs_eq source run]
      simp only [terminalRegs, bad, show BAD ≠ DONE from by decide, ↓reduceIte]
    constructor
    · intro normal
      rw [selected] at normal
      cases normal
    · intro _
      exact Or.inr (Or.inr ret)
  · have initialOK := initial.resolve_right bad
    by_cases table : s.mode = TABLE
    · have result := inflate_dispatch_ret_construction E invariant buffers (Or.inl table) initialOK run get
      constructor
      · intro normal
        rcases result with ok | ⟨_, mode⟩
        · exact Or.inl ok
        · exact Or.inr mode
      · intro leaves
        rcases result with ok | ⟨normal, _⟩
        · exact Or.inl ok
        · cases normal.symm.trans leaves
    · by_cases lengths : s.mode = LENLENS
      · have result := inflate_dispatch_ret_construction E invariant buffers (Or.inr (Or.inl lengths)) initialOK run get
        constructor
        · intro normal
          rcases result with ok | ⟨_, mode⟩
          · exact Or.inl ok
          · exact Or.inr mode
        · intro leaves
          rcases result with ok | ⟨normal, _⟩
          · exact Or.inl ok
          · cases normal.symm.trans leaves
      · by_cases codes : s.mode = CODELENS
        · have result := inflate_dispatch_ret_construction E invariant buffers (Or.inr (Or.inr codes)) initialOK run get
          constructor
          · intro normal
            rcases result with ok | ⟨_, mode⟩
            · exact Or.inl ok
            · exact Or.inr mode
          · intro leaves
            rcases result with ok | ⟨normal, _⟩
            · exact Or.inl ok
            · cases normal.symm.trans leaves
        · have result := inflate_dispatch_ret_nonconstruction E table lengths codes bad run
          rw [initialOK] at result
          constructor
          · intro normal
            rcases result with ok | ⟨leaves, _⟩
            · exact Or.inl ok
            · cases normal.symm.trans leaves
          · intro _
            rcases result with ok | ⟨_, ended⟩
            · exact Or.inl ok
            · exact Or.inr (Or.inl ended)

def RetLoopInv (cutoff : Nat) (r : ZStreamRef) (zs : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, LocalStateJ h cutoff r zs z s ∧ DispatchBuffers h r l bs ∧
    l.bits.toNat ≤ 39 ∧ (l.ret = Z_OK ∨ s.mode = BAD)

theorem inflate_dispatch_ret_loop_step
    {c : Ctx} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : RetLoopInv cutoff r zs l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => RetLoopInv cutoff r zs regs after
    | .error exit => exit = .leave → PublicLeaveRet regs := by
  obtain ⟨z, s, bs, invariant, buffers, incoming, initial⟩ := current
  have E : Env c h r zs z s := ⟨root, state, invariant.good.live.hz, invariant.good.live.hs⟩
  obtain ⟨otherOutcome, otherRegs, otherHeap, stream, privateState, used, _, _, source,
    final, packet, _, _, _, _, _, bits, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers incoming
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  obtain ⟨normalRet, leaveRet⟩ :=
    inflate_dispatch_ret_classification E invariant buffers initial run final.good.live.hs
  cases outcome with
  | ok value =>
    cases value
    exact ⟨stream, privateState, bs.drop used, final, packet, bits, normalRet rfl⟩
  | error exit =>
    intro selected
    subst exit
    exact leaveRet rfl

/-- The real entry initializes ret=OK; the entire actual mode loop then
reaches ordinary inf_leave only with OK, STREAM_END or DATA_ERROR. -/
theorem inflate_run_leave_ret_codes
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, regs), after)) :
    PublicLeaveRet regs := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : RetLoopInv cutoff r zs (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits, Or.inl rfl⟩
  rw [cut] at run
  have step : ∀ before heap outcome finalRegs finalHeap, RetLoopInv cutoff r zs before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => RetLoopInv cutoff r zs finalRegs finalHeap
      | .error exit => exit = .leave → PublicLeaveRet finalRegs := by
    intro before heap outcome finalRegs finalHeap valid source
    have result := inflate_dispatch_ret_loop_step E.strm E.st before heap outcome finalRegs finalHeap valid source
    cases outcome with
    | ok value => cases value; exact result
    | error stopped => exact result
  exact xwhile_success_control_post _ _ step start run rfl

#print axioms inflate_run_leave_ret_codes
end Zlib.Inflate.Local
