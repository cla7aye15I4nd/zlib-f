import ZlibF.Proof.«inflate.c.header-counts-wait»
import ZlibF.Proof.«inflate.c.header-progress-table-start»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A real TABLE dispatch followed by the complete leave produces the
first stored LENLENS progress relation, including its explicit received word.
The accepted counts and insufficient alphabet bits are source conditions;
no post-state invariant or callee contract is an assumption. -/
theorem inflate_body_TABLE_header_wait_seed
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null) (input : BitInv h (dispatchRegs z s) bs)
    (mode : s.mode = TABLE) :
    ∃ outcome pulled used,
      runX (NEEDBITS 14) (dispatchRegs z s) h = .ok ((outcome, pulled), h) ∧ used ≤ bs.length ∧
      BitInv h pulled (bs.drop used) ∧
      (outcome = .ok () →
        ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) →
        (stream (tableRegs pulled) (bs.drop used)).length / 3 <
          (tableCounts s pulled.hold).ncode.toNat →
        ∃ rc after stream0 state,
          (do
            let (result, regs) ← runX (inflate_run c) IL.init
            match result with
            | .error (.ret value) => pure value
            | _ => inflate_leave c regs) h = .ok (rc, after) ∧
          DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
          LenlensProgress state state.hold state.bits
            (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++
              bytesBits (bs.drop used)) ∧
          state.ncode = (tableCounts s pulled.hold).ncode ∧
          state.nlen = (tableCounts s pulled.hold).nlen ∧
          state.ndist = (tableCounts s pulled.hold).ndist ∧
          ∃ hlit hdist hclen firstRest secondRest,
            readBits 5 (Zlib.Inflate.Proofs.stream (dispatchRegs z s) bs) = some (hlit, firstRest) ∧
            readBits 5 firstRest = some (hdist, secondRest) ∧
            readBits 4 secondRest = some (hclen, Zlib.Inflate.Proofs.stream (tableRegs pulled) (bs.drop used)) ∧
            state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧
            state.ncode.toNat = hclen + 4) := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, zget, inputRange, _outputRange, separate⟩ := buffers
  have sameZ : z0 = z := Option.some.inj (zget.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨outcome, pulled, used, pull, bound, inv, accepted⟩ :=
    inflate_TABLE_header_phase_start E initial packet mode
  refine ⟨outcome, pulled, used, pull, bound, inv, ?_⟩
  intro normal valid short
  obtain ⟨phase, phasePacket, seed, fields, tableRun⟩ := accepted normal valid
  let startState := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
  let startHeap := setI h zs startState
  have phaseEnv : Env c startHeap r zs z startState :=
    ⟨E.strm, E.st, phase.good.live.hz, phase.good.live.hs⟩
  have short0 : (Zlib.Inflate.Proofs.stream (tableRegs pulled) (bs.drop used)).length / 3 <
      startState.ncode.toNat - startState.«have».toNat := by
    simpa only [startState, UInt32.toNat_zero, Nat.sub_zero] using short
  obtain ⟨regs, heap0, state0, waiting, current, packet0, bits, trace⟩ :=
    inflate_dispatch_LENLENS_header_wait phaseEnv phase phasePacket rfl seed short0
  have readCounts := inflate_dispatch_LENLENS_header_wait_counts phaseEnv phase
    phasePacket rfl short0 waiting current.good.live.hs
  have step : runX (inflate_dispatch c) (dispatchRegs z s) h =
      .ok ((.error Ex.leave, regs), heap0) := by
    rw [inflate_dispatch_TABLE E _ mode, tableRun]
    rw [inflate_dispatch_LENLENS phaseEnv _ rfl] at waiting
    exact waiting
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
  obtain ⟨rc, after, stream0, state, leave, final, finalAllocator, finalTrace,
    _nextIn, _availIn, _nextOut, _availOut⟩ :=
    inflate_leave_header_progress_accounting env0 current allocator trace packet0 (by omega)
  obtain ⟨rc0, after0, stream1, state1, leave0, final0, _allocator0, codeCount, litCount, distCount⟩ :=
    inflate_leave_header_counts env0 current allocator packet0 (by omega)
  have same : (rc, after) = (rc0, after0) := Except.ok.inj (leave.symm.trans leave0)
  cases same
  have sameState : state = state1 := Option.some.inj (final.good.live.hs.symm.trans final0.good.live.hs)
  subst state1
  have code := codeCount.trans readCounts.1
  have lit := litCount.trans readCounts.2.1
  have dist := distCount.trans readCounts.2.2
  refine ⟨rc, after, stream0, state, ?_, final, finalAllocator, finalTrace, code, lit, dist, ?_⟩
  · rw [bind_app, entry, loop]
    exact leave
  · obtain ⟨hlit, hdist, hclen, firstRest, secondRest, firstRead, secondRead, thirdRead,
      lit0, dist0, code0⟩ := fields
    exact ⟨hlit, hdist, hclen, firstRest, secondRest, firstRead, secondRead, thirdRead,
      by rw [lit]; exact lit0, by rw [dist]; exact dist0, by rw [code]; exact code0⟩

#print axioms inflate_body_TABLE_header_wait_seed

end Zlib.Inflate.Proofs
