import ZlibF.Proof.«inflate.c.low-output»
import ZlibF.Proof.«inflate.c.header-progress-leave»
import ZlibF.Proof.«inflate.c.lenlens-code-length-entry»
import ZlibF.Proof.«inflate.c.dispatch-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Input exhaustion in the actual LENLENS dispatch preserves the explicit
received word and the initialized state, on the same returned execution. -/
theorem inflate_dispatch_LENLENS_header_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (progress : LenlensProgress s l.hold l.bits received)
    (short : (stream l bs).length / 3 < s.ncode.toNat - s.«have».toNat) :
    ∃ regs after state,
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) ∧
      DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs [] ∧
      regs.bits.toNat < 3 ∧
      LenlensProgress state regs.hold regs.bits (received ++ bytesBits bs) := by
  obtain ⟨ncode, haveBound, _nlen, _ndist, _prefix⟩ := invariant.headerLengths mode
  obtain ⟨outcome, regs, used, count, countEq, run, bound, inv, trace⟩ :=
    ll1_header_progress E.st E.hs invariant.good.inv.wf.1 ncode haveBound buffers.bits progress
  subst count
  obtain ⟨outcome1, regs1, used1, run1, bound1, inv1, _remaining, _shape, wait, _full⟩ :=
    ll1_run E.st E.hs invariant.good.inv.wf.1 ncode haveBound buffers.bits
  rw [run] at run1
  cases run1
  obtain ⟨exitEq, _empty, usedEq, bits⟩ := wait (by
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) short)
  subst outcome
  have sameUse : used = used1 := by
    have count0 := inv.have_eq
    have count1 := inv1.have_eq
    rw [List.length_drop] at count0 count1
    omega
  subst used1
  subst used
  rw [List.take_length] at trace
  obtain ⟨outcome2, regs2, after, state, used2, bound2, run2, nextJ,
    packet, _sizes, _next, count2, _put, _left, _total, _bits, _budget⟩ :=
    ll1_default_J E invariant.toDefaultStateJ.toDefaultDecodeJ buffers mode
  rw [run] at run2
  cases run2
  have used2Eq : used2 = bs.length := by
    have count0 := inv.have_eq
    rw [List.drop_length, List.length_nil] at count0
    have initialCount := buffers.bits.have_eq
    omega
  subst used2
  rw [List.drop_length] at packet
  have stateEq : state = llSt s (stream l bs)
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)) := by
    have get := nextJ.good.live.hs
    rw [setI_istates_same] at get
    exact (Option.some.inj get).symm
  have config : DefaultConfigFrame s state := by
    rw [stateEq]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have current := invariant.toDefaultStateJ.config_update nextJ config
    (invariant.construction_format (Or.inr (Or.inl mode)))
  have fields : originStateFields state = originStateFields s := by rw [stateEq]; rfl
  have origin := invariant.of_fields current (congrArg Prod.fst fields)
    (congrArg (fun v => v.2.1) fields) (congrArg (fun v => v.2.2.1) fields)
  refine ⟨regs, _, state, ?_, origin, packet, bits, ?_⟩
  · rw [inflate_dispatch_LENLENS E l mode, inflate_LENLENS_eq, runX_bind, run]
  · rw [stateEq]
    exact trace

/-- The actual LOAD, dispatch loop and complete leave suffix preserve the
header word when this call runs out of input. No future buffer is retained
in the word, and no callee execution is a caller premise. -/
theorem inflate_body_LENLENS_header_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null)
    (input : BitInv h (dispatchRegs z s) bs)
    (mode : s.mode = LENLENS)
    (progress : LenlensProgress s s.hold s.bits received)
    (short : (stream (dispatchRegs z s) bs).length / 3 < s.ncode.toNat - s.«have».toNat) :
    ∃ rc after stream state,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      LenlensProgress state state.hold state.bits (received ++ bytesBits bs) := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, zget, inputRange, _outputRange, separate⟩ := id buffers
  have eqz : z0 = z := Option.some.inj (zget.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs :=
    ⟨inputRange, output, separate, input⟩
  obtain ⟨regs, heap0, state0, step, current, packet0, bits, trace⟩ :=
    inflate_dispatch_LENLENS_header_wait E invariant packet mode progress short
  have loop := xwhile_run_chain (inflate_dispatch c)
    (fun _ => dispatchRegs z s) (fun _ => h) 0 (by unfold fuel; decide)
    Ex.leave regs heap0 (by intro j impossible; omega) step
  have noType : s.mode ≠ TYPE := by rw [mode]; decide
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  have env0 : Env c heap0 r zs z state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have inputValid : z.next_in = .null → z.avail_in = 0 := by
    intro null
    rcases input.next with empty | ⟨_, _, _, pointer, _⟩
    · have count := input.have_eq
      rw [empty] at count
      exact UInt32.toNat_inj.mp (by simpa [dispatchRegs] using count)
    · change z.next_in = _ at pointer
      rw [null] at pointer
      cases pointer
  obtain ⟨rc, after, stream0, state, leave, final, finalAlloc, finalTrace⟩ :=
    inflate_leave_header_progress env0 current allocator trace packet0 (by omega)
      (inflate_run_default_low_out E invariant.toDefaultStateJ buffers nonnull inputValid
        (entry.trans loop) current.good.live.hs)
  refine ⟨rc, after, stream0, state, ?_, final, finalAlloc, finalTrace⟩
  rw [bind_app, entry, loop]
  exact leave

#print axioms inflate_dispatch_LENLENS_header_wait
#print axioms inflate_body_LENLENS_header_wait
end Zlib.Inflate.Proofs
