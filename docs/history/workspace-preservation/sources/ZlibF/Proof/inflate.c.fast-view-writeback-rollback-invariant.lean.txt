import ZlibF.Proof.«inflate.c.fast-view-loop-accounted-entry-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A loop exit with the call-entry bit account safely returns its whole
held bytes. The resulting pointer stays at or after the call-entry cursor. -/
theorem FastLoopExit.rollback_accounted
    {ctx : FastLoopContext} {h : Heap}
    {result : Zlib.Inffast.L}
    {startOff startBits : Nat}
    (final : FastLoopExit ctx h result)
    (account : FastInputAccount ctx startOff
      startBits result)
    (initialBits : startBits < 8) :
    ∃ off input,
      result.in_ = .ref ctx.inputRef off ∧
      Space.get h ctx.inputRef = some input ∧
      startOff ≤ off - (result.bits >>> 3).toNat ∧
      C.run (Zlib.Inffast.subn result.in_
        (result.bits >>> 3)) h =
        .ok (.ref ctx.inputRef
          (off - (result.bits >>> 3).toNat), h) := by
  obtain ⟨finalSlow, finalBs, finalZ, finalS,
    finalPacket, finalJ, finalBuffers⟩ := final
  obtain ⟨off, cursor, lower, budget⟩ := account
  have slowPtr : finalSlow.next =
      .ref ctx.inputRef off :=
    finalPacket.cursor.symm.trans cursor
  obtain ⟨input, inputGet, inputBound⟩ :=
    caller_range_ref_view (by
      simpa only [slowPtr] using finalBuffers.input)
  have buffered : (result.bits >>> 3).toNat ≤
      off - startOff := by
    rw [Zlib.Inffast.Proofs.bits_whole]
    omega
  have length : (result.bits >>> 3).toNat ≤ off := by
    omega
  have rollbackLower : startOff ≤
      off - (result.bits >>> 3).toNat := by
    omega
  have rollback := Zlib.Inffast.Proofs.subn_ok
    (h := h) (r := ctx.inputRef) (a := input)
    (off := off) (n := result.bits >>> 3)
    inputGet length (by omega)
  refine ⟨off, input, cursor, inputGet,
    rollbackLower, ?_⟩
  rw [cursor]
  exact rollback

/-- Every nonbreaking actual fast-loop exit satisfies the translated
input-byte rollback when the entry count is below eight bits. -/
theorem FastLoopReady.rollback_after_run
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (initialBits : q.bits.toNat < 8) :
    ∃ startOff result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) q) h =
          .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = false →
        ∃ off input,
          result.in_ = .ref ctx.inputRef off ∧
          Space.get after ctx.inputRef = some input ∧
          startOff ≤ off - (result.bits >>> 3).toNat ∧
          C.run (Zlib.Inffast.subn result.in_
            (result.bits >>> 3)) after =
            .ok (.ref ctx.inputRef
              (off - (result.bits >>> 3).toNat), after)) := by
  obtain ⟨startOff, result, after, cursor,
    loopRun, final, account⟩ :=
    ready.run_account_from_entry
  refine ⟨startOff, result, after, loopRun,
    final, ?_⟩
  intro notBroken
  exact final.rollback_accounted (account notBroken)
    initialBits

/-- The actual prelude loads the same sub-byte held count as the synchronized
caller registers. -/
theorem fastEntryPrefix_initial_bits
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    {ctx : FastLoopContext} {q : Zlib.Inffast.L}
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
      slow.bits < 8) = true)
    (prefixRun : C.run
      (fastEntryPrefix (some r) slow.out_) h =
      .ok ((ctx.c, q), h)) :
    q.bits.toNat < 8 := by
  obtain ⟨ir, dest, io, oo, nextPtr, putPtr,
    exactRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform
      buffers (invariant.tables mode) inputCursor inputCount
      outputCursor outputCount stateHold stateBits fast
  have pairEq := Except.ok.inj
    (prefixRun.symm.trans exactRun)
  have bitsEq : q.bits = slow.bits := by
    have eq := congrArg
      (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) ×
        Heap => p.1.2.bits) pairEq
    simpa using eq
  rw [bitsEq]
  have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
      slow.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq]
      using fast
  simpa [UInt32.lt_iff_toNat_lt] using margins.2

/-- The translated fast prelude and loop safely reach the input rollback
on all nonbreaking exits. The error-break case remains open. -/
theorem fastEntryLoop_rollback_run
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
    ∃ (ctx : FastLoopContext) (result : Zlib.Inffast.L)
        (after : Heap) (startOff : Nat),
      C.run (fastEntryLoop (some r) slow.out_) h =
        .ok ((ctx.c, result), after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = false →
        ∃ off input,
          result.in_ = .ref ctx.inputRef off ∧
          Space.get after ctx.inputRef = some input ∧
          startOff ≤ off - (result.bits >>> 3).toNat ∧
          C.run (Zlib.Inffast.subn result.in_
            (result.bits >>> 3)) after =
            .ok (.ref ctx.inputRef
              (off - (result.bits >>> 3).toNat), after)) := by
  obtain ⟨ctx, q, result, after, startOff,
    prefixRun, cursor, combinedRun, final, account⟩ :=
    fastEntryLoop_account_run invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have initialBits : q.bits.toNat < 8 :=
    fastEntryPrefix_initial_bits invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast prefixRun
  refine ⟨ctx, result, after, startOff,
    combinedRun, final, ?_⟩
  intro notBroken
  exact final.rollback_accounted (account notBroken)
    initialBits

end Zlib.Inflate.Proofs
