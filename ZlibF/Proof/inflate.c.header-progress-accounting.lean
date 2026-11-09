import ZlibF.Proof.«inflate.c.header-progress-public-wait»
import ZlibF.Proof.«inflate.c.leave-default-public-accounting»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual leave run retains both the phase word and the
cursor bindings used by independent observations of public calls. -/
theorem inflate_leave_header_progress_accounting
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (progress : LenlensProgress s l.hold l.bits received)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      LenlensProgress state state.hold state.bits received ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧
      stream.next_out = l.put ∧ stream.avail_out = l.left := by
  obtain ⟨rc, after, stream, state, run, final, finalAllocator, trace⟩ :=
    inflate_leave_header_progress E invariant allocator progress buffers bits
  obtain ⟨rc0, after0, stream0, state0, run0, final0, _allocator0,
    nextIn, availIn, nextOut, availOut, _outcome⟩ :=
    inflate_leave_default_public_accounting E invariant.toDefaultStateJ allocator buffers bits
  have same : (rc, after) = (rc0, after0) := Except.ok.inj (run.symm.trans run0)
  cases same
  have sameZ : stream = stream0 :=
    Option.some.inj (final.good.live.hz.symm.trans final0.good.live.hz)
  subst stream0
  exact ⟨rc, after, stream, state, run, final, finalAllocator, trace, nextIn, availIn, nextOut, availOut⟩

/-- A particular actual waiting dispatch has exactly the input-exhaustion
registers and has not changed the output interval. The execution premise
is an operational observation, supplied by the closed waiting theorem. -/
theorem inflate_dispatch_LENLENS_header_wait_registers
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (short : (stream l bs).length / 3 < s.ncode.toNat - s.«have».toNat)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after)) :
    regs.have_ = 0 ∧ regs.next = inputAdvance l.next bs.length ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ := by
  obtain ⟨ncode, haveBound, _nlen, _ndist, prefixValues⟩ := invariant.headerLengths mode
  obtain ⟨regs0, used, _bound, _input, _remaining, shape, waiting, _complete,
    cursor, _bits, _read⟩ :=
    inflate_LENLENS_code_length_cursor E.strm E.st E.hz E.hs invariant.good.inv.wf
      ncode haveBound prefixValues buffers.bits
  obtain ⟨empty, allUsed, _bits0, run⟩ :=
    waiting (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) short)
  rw [inflate_dispatch_LENLENS E l mode, run] at actual
  cases actual
  refine ⟨empty, ?_, ?_, ?_, ?_⟩
  · rw [cursor, allUsed]
  all_goals rw [shape]

/-- The complete actual body on input exhaustion preserves the phase word
and exhausts the real input counter without consuming output capacity. -/
theorem inflate_body_LENLENS_header_wait_accounting
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
      LenlensProgress state state.hold state.bits (received ++ bytesBits bs) ∧
      stream.next_in = inputAdvance z.next_in bs.length ∧ stream.avail_in = 0 ∧
      stream.next_out = z.next_out ∧ stream.avail_out = z.avail_out := by
  have output := dispatchRegs_output E.hz buffers nonnull s
  obtain ⟨z0, zget, inputRange, _outputRange, separate⟩ := buffers
  have eqz : z0 = z := Option.some.inj (zget.symm.trans E.hz)
  subst z0
  have packet : DispatchBuffers h r (dispatchRegs z s) bs := ⟨inputRange, output, separate, input⟩
  obtain ⟨regs, heap0, state0, step, current, packet0, bits, trace⟩ :=
    inflate_dispatch_LENLENS_header_wait E invariant packet mode progress short
  obtain ⟨empty, next, put, left, _out⟩ :=
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
  obtain ⟨rc, after, stream0, state, leave, final, finalAllocator, finalTrace,
    nextIn, availIn, nextOut, availOut⟩ :=
    inflate_leave_header_progress_accounting env0 current allocator trace packet0 (by omega)
  refine ⟨rc, after, stream0, state, ?_, final, finalAllocator, finalTrace, ?_, ?_, ?_, ?_⟩
  · rw [bind_app, entry, loop]
    exact leave
  · exact nextIn.trans next
  · exact availIn.trans empty
  · exact nextOut.trans put
  · exact availOut.trans left

#print axioms inflate_leave_header_progress_accounting
#print axioms inflate_dispatch_LENLENS_header_wait_registers
#print axioms inflate_body_LENLENS_header_wait_accounting
end Zlib.Inflate.Proofs
