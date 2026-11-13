import ZlibF.Proof.«inflate.c.default-view-loop»
import ZlibF.Proof.«inflate.c.pending-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual TYPE normalization, LOAD and initial counters establish the
complete persistent default relation from the public buffer domain. -/
theorem inflate_run_default_view_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ after state bs,
      runX (inflate_run c) IL.init h =
        runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state) after ∧
      DefaultStateJ after r zs z state ∧ Env c after r zs z state ∧
      DispatchBuffers after r (dispatchRegs z state) bs ∧
      (dispatchRegs z state).bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      after = setI h zs state ∧ state = (if s.mode = TYPE then { s with mode := TYPEDO } else s) := by
  let good := invariant.good
  let tables := invariant.tables
  let pending := invariant.pending
  let hold := invariant.held
  obtain ⟨after, state, run, finalGood, env, output, sizes, frame, heapEq, stateEq⟩ :=
    inflate_run_output_entry_frame_state E good buffers nonnull
  have currentBuffers : StreamBuffers after r := by
    obtain ⟨stream, streamGet, input, out, separate⟩ := buffers
    have eq : stream = z := Option.some.inj (streamGet.symm.trans good.live.hz)
    subst stream
    refine ⟨z, finalGood.live.hz, ?_, ?_, separate⟩
    · apply callerRange_transport good finalGood (by rw [frame]) _ _ input
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    · apply callerRange_transport good finalGood (by rw [frame]) _ _ out
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
  have finalJ : DefaultStateJ after r zs z state := by
    by_cases type : s.mode = TYPE
    · have blockFrame : BlockHeaderFrame s state := by rw [stateEq, if_pos type]; rfl
      have modes : BlockControlMode state.mode := by
        rw [stateEq, if_pos type]
        exact Or.inr (Or.inl rfl)
      have format := invariant.block_format (Or.inl type)
      have base := invariant.toDefaultDecodeJ.block_update finalGood finalTables finalPending blockFrame modes format sizes
        (by rw [heapEq]; rfl)
      exact invariant.config_update base frame.default_config format
    · have sameState : state = s := by rw [stateEq, if_neg type]
      have sameHeap : after = h := by rw [heapEq, sameState]; simp [setI, upd_self _ _ _ good.live.hs]
      rwa [sameHeap, sameState]
  exact ⟨after, state, bs, run, finalJ, env, ⟨input, output, separate, inv⟩,
    finalGood.inv.bits, sizes, frame, heapEq, stateEq⟩


/-- The per-call header facts at the start of the loop. -/
theorem inflate_run_entry_local {c : Ctx} {h heap0 : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state0 : InflateState} (invariant : DefaultStateJ h r zs z s)
    (currentJ : DefaultStateJ heap0 r zs z state0) (sizes : ByteViewSizes h heap0)
    (frame : DecodeStateFrame s state0) (heapEq : heap0 = setI h zs state0)
    (stateEq : state0 = (if s.mode = TYPE then { s with mode := TYPEDO } else s))
    (local_ : HeaderLocal c h r s (dispatchRegs z s)) :
    HeaderLocal c heap0 r state0 (dispatchRegs z state0) := by
  have regsEq : dispatchRegs z state0 = dispatchRegs z s := by rw [frame]; rfl
  rw [regsEq]
  by_cases typeMode : s.mode = TYPE
  · intro _ high
    rw [stateEq, if_pos typeMode] at high
    exact absurd high (by change ¬ TYPEDO ≤ HCRC; decide)
  · have same : state0 = s := by rw [stateEq, if_neg typeMode]
    have readonly : ∀ ref : BRef, Space.ro heap0 ref = Space.ro h ref := by
      intro ref
      rw [heapEq, byte_view_ro_setI]
    have headers : heap0.gzheaders = h.gzheaders := by rw [heapEq]; rfl
    exact local_.transfer invariant.good currentJ.good (by rw [same]) (by rw [same]) (by rw [same])
      (by rw [same]) sizes readonly headers

/-- The actual complete inflate_run body, including its source entry
prefix and every mode-loop case, returns without a runtime fault. One
persistent default relation and exact caller cursor/count accounting hold
throughout on general public caller byte views. The public entry, inf_leave,
ownership and all-history conclusions remain separate obligations. -/
theorem inflate_run_default_view {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s)) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      HeaderLocal c after r state regs ∧ regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat := by
  obtain ⟨heap0, state0, bs, entryRun, currentJ, currentEnv, packet, bits, sizes, frame, heapEq, stateEq⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant currentJ sizes frame heapEq stateEq local_
  obtain ⟨exit, regs, after, stream, state, used, made, bound, run, final, finalPacket, finalLocal,
    finalBits, finalSizes, next, count, put, left⟩ :=
    inflate_default_view_loop currentEnv currentJ packet entryLocal bits
  exact ⟨bs, exit, regs, after, stream, state, used, made, bound, entryRun.trans run,
    final, finalPacket, finalLocal, finalBits, sizes.trans finalSizes, next, count, put, left⟩

#print axioms inflate_run_default_view_entry
#print axioms inflate_run_default_view
end Zlib.Inflate.Proofs
