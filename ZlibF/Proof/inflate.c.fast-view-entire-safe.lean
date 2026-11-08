import ZlibF.Proof.«inflate.c.fast-view-entry-loop-budget»
import ZlibF.Proof.«inflate.c.fast-view-loop-byte-sizes»
import ZlibF.Proof.«inflate.c.fast-view-loop-writeback-execution»
import ZlibF.Proof.«inflate.c.fast-view-loop-writeback-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Compose the three actual source-order fragments of `inflate_fast`. -/
theorem inflate_fast_compose {h after finished : Heap}
    (strm : ZStreamPtr) (start : UInt32)
    (c : Zlib.Inffast.Ctx) (initial result : Zlib.Inffast.L)
    (hPrefix : C.run (fastEntryPrefix strm start) h = .ok ((c, initial), h))
    (hLoop : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body c)
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ c.last then
          pure (← Ptr.lt q.out c.end_, q)
        else pure (false, q)) initial) h = .ok (result, after))
    (hSuffix : C.run (fastAfterLoopView c result) after = .ok ((), finished)) :
    C.run (Zlib.Inffast.inflate_fast strm start) h = .ok ((), finished) := by
  rw [inflate_fast_prefix_split]
  change (fastEntryPrefix strm start) h = .ok ((c, initial), h) at hPrefix
  change (cdoWhile (Zlib.Inffast.inflate_fast_body c)
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ c.last then
          pure (← Ptr.lt q.out c.end_, q)
        else pure (false, q)) initial) h = .ok (result, after) at hLoop
  change (fastAfterLoop c result) after = .ok ((), finished) at hSuffix
  change (do
      let pair ← fastEntryPrefix strm start
      fastAfterPrefix pair.1 pair.2) h = .ok ((), finished)
  unfold fastAfterPrefix
  simp only [bind_app, hPrefix, hLoop, hSuffix]

/-- The translated complete fast call executes and retains `Good` for a
default decoder on general caller byte views. The input and output may
refer to disjoint intervals in one allocation. -/
theorem inflate_fast_default_view_safe
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
    ∃ finished zNext sNext,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      Good finished r zs zNext sNext := by
  obtain ⟨ctx, initial, result, after, startOff, off, used,
    input, hPrefix, sameR, sameZs, startCursor, initialBits, ready, hLoop,
    final, budget, output, limit, resultCursor, inputGet,
    usedBound, count, rollback⟩ :=
    fastEntryLoop_run_with_rollback invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have sizes : ByteViewSizes h after := ready.byte_view_sizes_of_run hLoop
  obtain ⟨entrySlow, entryBs, entryOutput, entryOff, k,
    packet, entryJ, entryBuffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr,
    inputMargin, outPtr, outputGet, outputWrite,
    outputSize, current, beginLe, span, guard⟩ := ready
  have entryCursor : entrySlow.next = .ref ctx.inputRef startOff := by
    exact packet.cursor.symm.trans startCursor
  have sameEntryOff : entryOff = startOff :=
    (Ptr.ref.inj (nextPtr.symm.trans entryCursor)).2
  subst entryOff
  obtain ⟨initialInput, initialGet, initialBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using entryBuffers.input)
  have sizeEq : input.size = initialInput.size := by
    have sized := sizes ctx.inputRef
    rw [initialGet, inputGet] at sized
    simpa only [Option.map_some, Option.some.injEq] using sized
  have inputBoundAfter : startOff + entrySlow.have_.toNat ≤ input.size := by
    omega
  obtain ⟨finished, zNext, sNext, hSuffix, good, _, _, _, _, _⟩ :=
    final.writeback_run budget limit output initialBits lastPtr
      inputMargin (UInt32.toNat_lt entrySlow.have_)
      inputGet inputBoundAfter []
  have loopExact : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ ctx.c.last then
          pure (← Ptr.lt q.out ctx.c.end_, q)
        else pure (false, q)) initial) h = .ok (result, after) := hLoop
  exact ⟨finished, zNext, sNext,
    inflate_fast_compose (some r) slow.out_ ctx.c initial result
      hPrefix loopExact hSuffix, by simpa only [sameR, sameZs] using good⟩

/-- The translated complete fast call preserves the default decoder relation
on general caller byte views, including every broken decoder exit. -/
theorem inflate_fast_default_view_J
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
    ∃ finished zNext sNext,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext := by
  obtain ⟨ctx, initial, result, after, startOff, off, used,
    input, hPrefix, sameR, sameZs, startCursor, initialBits, ready, hLoop,
    final, budget, output, limit, resultCursor, inputGet,
    usedBound, count, rollback⟩ :=
    fastEntryLoop_run_with_rollback invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have sizes : ByteViewSizes h after := ready.byte_view_sizes_of_run hLoop
  obtain ⟨entrySlow, entryBs, entryOutput, entryOff, k,
    packet, entryJ, entryBuffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr,
    inputMargin, outPtr, outputGet, outputWrite,
    outputSize, current, beginLe, span, guard⟩ := ready
  have entryCursor : entrySlow.next = .ref ctx.inputRef startOff := by
    exact packet.cursor.symm.trans startCursor
  have sameEntryOff : entryOff = startOff :=
    (Ptr.ref.inj (nextPtr.symm.trans entryCursor)).2
  subst entryOff
  obtain ⟨initialInput, initialGet, initialBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using entryBuffers.input)
  have sizeEq : input.size = initialInput.size := by
    have sized := sizes ctx.inputRef
    rw [initialGet, inputGet] at sized
    simpa only [Option.map_some, Option.some.injEq] using sized
  have inputBoundAfter : startOff + entrySlow.have_.toNat ≤ input.size := by
    omega
  obtain ⟨finished, zNext, sNext, hSuffix, good, _, _, _, _, _⟩ :=
    final.writeback_default_state_run budget limit output initialBits lastPtr
      inputMargin (UInt32.toNat_lt entrySlow.have_)
      inputGet inputBoundAfter []
  have loopExact : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ ctx.c.last then
          pure (← Ptr.lt q.out ctx.c.end_, q)
        else pure (false, q)) initial) h = .ok (result, after) := hLoop
  exact ⟨finished, zNext, sNext,
    inflate_fast_compose (some r) slow.out_ ctx.c initial result
      hPrefix loopExact hSuffix, by simpa only [sameR, sameZs] using good⟩

#print axioms inflate_fast_compose
#print axioms inflate_fast_default_view_safe
#print axioms inflate_fast_default_view_J
end Zlib.Inflate.Proofs
