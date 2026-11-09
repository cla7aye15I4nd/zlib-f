import ZlibF.Proof.«inflate.c.local-control-state»
import ZlibF.Proof.«inflate.c.default-view-run»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem inflate_run_default_view_entry {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      LocalStateJ after cutoff r zs z state ∧ Env c after r zs z state ∧
      DispatchBuffers after r (dispatchRegs z state) bs ∧
      (dispatchRegs z state).bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      after = setI h zs state := by
  let good := invariant.good
  let tables := invariant.tables
  let pending := invariant.pending
  let hold := invariant.held
  obtain ⟨after, state, run, finalGood, env, sizes, frame, heapEq, stateEq⟩ :=
    run_dispatch_entry_local E good
  have currentBuffers : StreamBuffers after r := by
    obtain ⟨stream, streamGet, input, out, separate⟩ := buffers
    have eq : stream = z := Option.some.inj (streamGet.symm.trans good.live.hz)
    subst stream
    refine ⟨z, finalGood.live.hz, ?_, ?_, separate⟩
    · apply callerRange_local_transport good finalGood (by rw [frame]) _ _ input
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    · apply callerRange_local_transport good finalGood (by rw [frame]) _ _ out
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
  obtain ⟨bs, inv, separate⟩ := dispatchRegs_input (s := state) finalGood.live.hz currentBuffers inputValid
    (by rw [frame]; exact hold)
  have input : CallerRange after r z.next_in z.avail_in.toNat false := by
    obtain ⟨stream, get, input, _⟩ := currentBuffers
    have eq : stream = z := Option.some.inj (get.symm.trans finalGood.live.hz)
    subst stream
    exact input
  have finalTables : DataTableInvariant after state := by
    by_cases type : s.mode = TYPE
    · intro active
      rw [stateEq, if_pos type] at active
      change DataTableMode TYPEDO at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;> contradiction
    · have sameState : state = s := by rw [stateEq, if_neg type]
      have sameHeap : after = h := by rw [heapEq, sameState]; simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  have finalPending : DataPendingInvariant state := by
    by_cases type : s.mode = TYPE
    · apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
      rw [stateEq, if_pos type]
      change TYPEDO ≠ LENEXT ∧ TYPEDO ≠ DIST ∧ TYPEDO ≠ DISTEXT ∧ TYPEDO ≠ MATCH
      decide
    · rw [stateEq, if_neg type]
      exact pending
  have finalJ : LocalStateJ after cutoff r zs z state := by
    by_cases type : s.mode = TYPE
    · have blockFrame : BlockHeaderFrame s state := by rw [stateEq, if_pos type]; rfl
      have modes : BlockControlMode state.mode := by
        rw [stateEq, if_pos type]
        exact Or.inr (Or.inl rfl)
      have format := invariant.block_format (Or.inl type)
      have base := invariant.toLocalDecodeJ.block_update finalGood finalTables finalPending blockFrame modes format sizes
        (by rw [heapEq]; rfl)
      exact invariant.config_update base frame.default_config format (by rw [frame])
    · have sameState : state = s := by rw [stateEq, if_neg type]
      have sameHeap : after = h := by rw [heapEq, sameState]; simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  have output := dispatchRegs_output finalGood.live.hz currentBuffers nonnull state
  exact ⟨after, state, bs, run, finalJ, env, ⟨input, output, separate, inv⟩,
    finalGood.inv.bits, sizes, frame, heapEq⟩

#print axioms inflate_run_default_view_entry
end Zlib.Inflate.Local
