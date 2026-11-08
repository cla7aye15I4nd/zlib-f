import ZlibF.Proof.«inflate.c.fast-view-prelude-ready-invariant»
import ZlibF.Proof.«inflate.c.fast-view-loop-full-input-budget»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The source-order fast prefix and complete actual loop retain the
input rollback and output bounds, including broken decoder exits. -/
theorem fastEntryLoop_run_with_rollback
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ (ctx : FastLoopContext) (initial result : Zlib.Inffast.L)
        (after : Heap) (startOff off used : Nat) (input : Array UInt8),
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, initial), h) ∧
      ctx.r = r ∧ ctx.zs = zs ∧
      initial.in_ = .ref ctx.inputRef startOff ∧
      initial.bits.toNat < 8 ∧
      FastLoopReady ctx h initial ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) initial) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      FastLoopInputBudget ctx startOff initial.bits.toNat result ∧
      FastLoopOutputRange ctx after result ∧
      FastLoopInputLimit ctx result ∧
      result.in_ = .ref ctx.inputRef off ∧
      Space.get after ctx.inputRef = some input ∧
      used ≤ off - startOff ∧
      used + (result.bits >>> 3).toNat = off - startOff ∧
      C.run (Zlib.Inffast.subn result.in_ (result.bits >>> 3)) after =
        .ok (.ref ctx.inputRef (startOff + used), after) := by
  obtain ⟨ctx, initial, prefixRun, ready⟩ :=
    fastEntryPrefix_ready invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  obtain ⟨ir, dest, io, oo, nextPtr, putPtr, exactRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform buffers
      (invariant.tables mode) inputCursor inputCount outputCursor
      outputCount stateHold stateBits fast
  have same := Except.ok.inj (prefixRun.symm.trans exactRun)
  have exactStrm : ctx.c.strm = some r := by
    have field := congrArg (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap => p.1.1.strm) same
    simpa using field
  have exactState : ctx.c.state = some (.tab zs) := by
    have field := congrArg (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap => p.1.1.state) same
    simpa using field
  have sameR : ctx.r = r := Option.some.inj (ctx.streamPtr.symm.trans exactStrm)
  have sameZs : ctx.zs = zs := by
    have eq := Option.some.inj (ctx.statePtr.symm.trans exactState)
    cases eq
    rfl
  have initialBits : initial.bits.toNat < 8 := by
    have bitsEq : initial.bits = slow.bits := by
      have second := congrArg (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap => p.1.2.bits) same
      simpa using second
    rw [bitsEq]
    have margins : slow.bits < 8 := by
      have facts : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧ slow.bits < 8 := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
      exact facts.2
    exact UInt32.lt_iff_toNat_lt.mp margins
  obtain ⟨startOff, result, after, off, used, input,
    initialCursor, loopRun, final, budget, output, limit,
    resultCursor, inputGet, usedBound, count, rollback⟩ :=
    ready.run_with_accounted_rollback initialBits
  exact ⟨ctx, initial, result, after, startOff, off, used, input,
    prefixRun, sameR, sameZs, initialCursor, initialBits, ready, loopRun, final, budget, output,
    limit, resultCursor, inputGet, usedBound, count, rollback⟩

#print axioms fastEntryLoop_run_with_rollback
end Zlib.Inflate.Proofs
