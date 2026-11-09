import ZlibF.Proof.«inflate.c.local-fast-loop-summary»
import ZlibF.Proof.«inflate.c.fast-view-entry-loop-budget»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

theorem FastLoopExit.rollback_full_input_budget
    {cutoff : Nat} {ctx : FastLoopContext} {h : Heap} {result : Zlib.Inffast.L}
    {startOff startBits : Nat}
    (final : FastLoopExit cutoff ctx h result)
    (account : FastLoopInputBudget ctx startOff startBits result)
    (initialBits : startBits < 8) :
    ∃ off input used,
      result.in_ = .ref ctx.inputRef off ∧
      Space.get h ctx.inputRef = some input ∧
      used ≤ off - startOff ∧
      used + (result.bits >>> 3).toNat = off - startOff ∧
      C.run (Zlib.Inffast.subn result.in_ (result.bits >>> 3)) h =
        .ok (.ref ctx.inputRef (startOff + used), h) := by
  obtain ⟨slow, bs, z, s, packet, invariant, buffers⟩ := final
  obtain ⟨off, cursor, lower, budget⟩ := account
  have slowPtr : slow.next = .ref ctx.inputRef off := packet.cursor.symm.trans cursor
  obtain ⟨input, inputGet, inputBound⟩ :=
    caller_range_ref_view (by simpa only [slowPtr] using buffers.input)
  have exactOffset : startOff + (off - startOff) = off := by omega
  have cursorFromEntry : result.in_ = .ref ctx.inputRef (startOff + (off - startOff)) := by
    rw [exactOffset]
    exact cursor
  obtain ⟨used, usedBound, count, _, rollback⟩ :=
    Zlib.Inffast.Proofs.rollback_input_account inputGet cursorFromEntry
      (by rw [exactOffset]; omega) initialBits (by omega)
  exact ⟨off, input, used, cursor, inputGet, usedBound, count, rollback⟩

/-- Source-level prefix geometry stays attached to the exact loop run. -/
theorem fastEntryLoop_run_with_geometry
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : LocalStateJ h cutoff r zs z s)
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
    ∃ (ir dest : BRef) (io oo : Nat) (ctx : FastLoopContext)
        (initial result : Zlib.Inffast.L) (after : Heap)
        (off used : Nat) (input : Array UInt8),
      slow.next = .ref ir io ∧ slow.put = .ref dest oo ∧
      ctx.inputRef = ir ∧ ctx.dest = dest ∧ ctx.oo = oo ∧
      ctx.leftTotal = slow.left ∧ ctx.r = r ∧ ctx.zs = zs ∧
      ctx.c.last = .ref ir (io + slow.have_.toNat - 5) ∧
      ctx.c.end_ = .ref dest (oo + slow.left.toNat - 257) ∧
      initial.in_ = slow.next ∧ initial.out = slow.put ∧
      initial.bits = slow.bits ∧
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, initial), h) ∧
      FastLoopReady cutoff ctx h initial ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) initial) h = .ok (result, after) ∧
      FastLoopExit cutoff ctx after result ∧
      FastLoopInputBudget ctx io initial.bits.toNat result ∧
      FastLoopOutputRange ctx after result ∧
      FastLoopInputLimit ctx result ∧
      result.in_ = .ref ir off ∧
      Space.get after ir = some input ∧
      used ≤ off - io ∧
      used + (result.bits >>> 3).toNat = off - io ∧
      C.run (Zlib.Inffast.subn result.in_ (result.bits >>> 3)) after =
        .ok (.ref ir (io + used), after) ∧
      FastLoopSummary cutoff ctx h io initial.bits.toNat result after := by
  obtain ⟨ir, dest, io, oo, ctx, initial, nextPtr, putPtr,
    inputRef, destRef, outputOff, leftTotal, sameR, sameZs,
    last, end_, inEq, outEq, bitsEq, prefixRun, ready⟩ :=
    fastEntryPrefix_ready_geometry invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have initialBits : initial.bits.toNat < 8 := by
    rw [bitsEq]
    have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧ slow.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    exact UInt32.lt_iff_toNat_lt.mp margins.2
  obtain ⟨_, _, _, _, _, _, actualPrefix⟩ := fastEntryPrefix_run invariant.good invariant.platform
    buffers (invariant.tables mode) inputCursor inputCount outputCursor outputCount stateHold stateBits fast
  have unbroken : initial.broke = false := by
    have pairEq := Except.ok.inj (prefixRun.symm.trans actualPrefix)
    exact congrArg (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap => p.1.2.broke) pairEq
  have initialCursor : initial.in_ = .ref ctx.inputRef io := by rw [inEq, nextPtr, inputRef]
  obtain ⟨result, after, loopRun, summary⟩ := ready.run_summary (FastLoopInputBudget.initial initialCursor) unbroken
  have retained := summary
  obtain ⟨final, budget, output, limit, _⟩ := summary
  obtain ⟨off, input, used, resultCursor, inputGet, usedBound, count, rollback⟩ :=
    final.rollback_full_input_budget budget initialBits
  rw [inputRef] at resultCursor inputGet rollback
  exact ⟨ir, dest, io, oo, ctx, initial, result, after, off,
    used, input, nextPtr, putPtr, inputRef, destRef,
    outputOff, leftTotal, sameR, sameZs, last, end_,
    inEq, outEq, bitsEq, prefixRun, ready, loopRun,
    final, budget, output, limit, resultCursor,
    inputGet, usedBound, count, rollback, retained⟩


end Zlib.Inflate.Local
