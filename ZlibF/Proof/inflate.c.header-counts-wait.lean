import ZlibF.Proof.«inflate.c.header-counts-leave»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual waiting read loop changes have/lens, retaining all three
count fields initialized by the preceding TABLE prefix. -/
theorem inflate_dispatch_LENLENS_header_wait_counts
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (short : (stream l bs).length / 3 < s.ncode.toNat - s.«have».toNat)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (stateGet : after.istates zs = some state) :
    state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist := by
  obtain ⟨ncode, haveBound, _nlen, _ndist, prefixValues⟩ := invariant.headerLengths mode
  obtain ⟨regs0, used, _bound, _input, _remaining, _shape, waiting, _complete,
    _cursor, _bits, _read⟩ :=
    inflate_LENLENS_code_length_cursor E.strm E.st E.hz E.hs invariant.good.inv.wf
      ncode haveBound prefixValues buffers.bits
  obtain ⟨_empty, _allUsed, _bits0, run⟩ :=
    waiting (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) short)
  rw [inflate_dispatch_LENLENS E l mode, run] at actual
  cases actual
  rw [setI_istates_same] at stateGet
  have same := Option.some.inj stateGet
  rw [← same]
  exact ⟨rfl, rfl, rfl⟩

#print axioms inflate_dispatch_LENLENS_header_wait_counts

theorem inflate_body_LENLENS_header_wait_counts
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null) (input : BitInv h (dispatchRegs z s) bs)
    (mode : s.mode = LENLENS) (progress : LenlensProgress s s.hold s.bits received)
    (short : (stream (dispatchRegs z s) bs).length / 3 < s.ncode.toNat - s.«have».toNat) :
    ∃ rc after stream state,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, zget, inputRange, _outputRange, separate⟩ := buffers
  have eqz : z0 = z := Option.some.inj (zget.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨regs, heap0, state0, step, current, packet0, bits, trace⟩ :=
    inflate_dispatch_LENLENS_header_wait E invariant packet mode progress short
  have readCounts := inflate_dispatch_LENLENS_header_wait_counts E invariant packet mode short step current.good.live.hs
  obtain ⟨_, _, _, waitLeft, waitOut⟩ :=
    inflate_dispatch_LENLENS_header_wait_registers E invariant packet mode short step
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
  obtain ⟨rc, after, stream0, state, leave, final, finalAllocator, codeCount, litCount, distCount⟩ :=
    inflate_leave_header_counts env0 current allocator packet0 (by omega)
      (fun _ => by rw [waitOut, waitLeft]; rfl)
  refine ⟨rc, after, stream0, state, ?_, final, finalAllocator,
    codeCount.trans readCounts.1, litCount.trans readCounts.2.1, distCount.trans readCounts.2.2⟩
  rw [bind_app, entry, loop]
  exact leave

#print axioms inflate_body_LENLENS_header_wait_counts

end Zlib.Inflate.Proofs
