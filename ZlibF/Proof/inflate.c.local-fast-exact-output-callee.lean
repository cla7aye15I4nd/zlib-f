import ZlibF.Proof.«inflate.c.local-fast-callee»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-loop»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-writeback»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual complete fast call changes only the returned output prefix,
including disjoint intervals within one byte object. -/
theorem inflate_fast_default_view_exact_frame
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
    ∃ finished zNext sNext made,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      LocalStateJ finished cutoff r zs zNext sNext ∧
      zNext.next_out = advance slow.put made ∧
      made ≤ slow.left.toNat ∧
      BufferFrame h finished (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, made⟩] := by
  obtain ⟨ir, dest, io, oo, ctx, initial, result, after,
    off, used, input, slowNext, slowPut, inputRef, destRef,
    outputOff, leftTotal, sameR, sameZs, last, end_,
    inEq, outEq, bitsEq, hPrefix, ready, hLoop, final,
    budget, output, limit, resultCursor, inputGet,
    usedBound, count, rollback, summary⟩ :=
    fastEntryLoop_run_with_geometry invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have initialBits : initial.bits.toNat < 8 := by
    rw [bitsEq]
    have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
        slow.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    exact UInt32.lt_iff_toNat_lt.mp margins.2
  have sizes : ByteViewSizes h after := summary.2.2.2.2.1
  obtain ⟨framedResult, framedAfter, finalK, framedRun, _,
    finalOut, finalLower, finalUpper, loopFrame,
    loopMemory, loopWrite⟩ := ready.run_exact_output
  have sameLoop : (framedResult, framedAfter) = (result, after) :=
    Except.ok.inj (framedRun.symm.trans hLoop)
  cases sameLoop
  have finalOff : result.out = .ref ctx.dest finalK := finalOut
  obtain ⟨entrySlow, entryBs, entryOutput, entryOff, k,
    packet, entryJ, entryBuffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr,
    inputMargin, outPtr, outputGet, outputWrite,
    outputSize, current, beginLe, span, guard⟩ := ready
  obtain ⟨initialInput, initialGet, initialBound⟩ :=
    caller_range_ref_view
      (by simpa only [slowNext] using buffers.input)
  have sizeEq : input.size = initialInput.size := by
    have sized := sizes ir
    rw [initialGet, inputGet] at sized
    simpa only [Option.map_some, Option.some.injEq] using sized
  have inputBoundAfter : io + slow.have_.toNat ≤
      input.size := by omega
  have inputGetCtx : Space.get after ctx.inputRef = some input := by
    simpa only [inputRef] using inputGet
  have lastCtx : ctx.c.last = .ref ctx.inputRef
      (io + slow.have_.toNat - 5) := by
    simpa only [inputRef] using last
  have inputMarginSlow : 6 ≤ slow.have_.toNat := by
    have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
        slow.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    exact UInt32.le_iff_toNat_le.mp margins.1.1
  let regions : List Region :=
    [⟨.ref ctx.dest ctx.oo, finalK - ctx.oo⟩]
  obtain ⟨finished, zNext, sNext, hSuffix, good,
    suffixFrame, _, _, _, _⟩ :=
    final.writeback_default_state_run budget limit output
      initialBits lastCtx inputMarginSlow
      (UInt32.toNat_lt slow.have_) inputGetCtx
      inputBoundAfter regions
  have loopExact : C.run
      (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) initial) h =
      .ok (result, after) := hLoop
  have wholeRun :
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) :=
    inflate_fast_compose (some r) slow.out_ ctx.c initial result
      hPrefix loopExact hSuffix
  have metadata := fastMemoryMetaFrameM_inflate_fast r slow.out_
    h () finished wholeRun
  have ro : finished.ro = h.ro := by
    simp only [FastMemoryMetaFrame, fastMemoryMeta, Prod.mk.injEq]
      at metadata
    exact metadata.1
  have finalWrite : Space.ro finished ctx.dest = false := by
    simpa only [Space.ro, ro] using outputWrite
  have fullFrame : BufferFrame h finished
      (fun b => StreamRoot ctx.r b ∨ b = ctx.zs) regions :=
    BufferFrame.singleton_trans_live loopFrame suffixFrame (fast_memory_live loopMemory)
      outputGet loopWrite finalWrite
  have resultStored : zNext.next_out = result.out :=
    final.writeback_exact_output_cursor budget limit output
      initialBits lastCtx inputMarginSlow
      (UInt32.toNat_lt slow.have_) inputGetCtx
      inputBoundAfter hSuffix good
  have madeBound : finalK - ctx.oo ≤ slow.left.toNat := by
    rw [leftTotal] at finalUpper
    omega
  exact ⟨finished, zNext, sNext, finalK - ctx.oo,
    wholeRun, by simpa only [sameR, sameZs] using good,
    by
      rw [resultStored, finalOff, slowPut]
      simp only [advance, destRef, outputOff]
      congr 1
      omega,
    madeBound,
    by
      rw [slowPut]
      simpa only [regions, destRef, outputOff, leftTotal,
        sameR, sameZs] using fullFrame⟩

#print axioms inflate_fast_default_view_exact_frame

end Zlib.Inflate.Local
