import ZlibF.Proof.«inflate.c.fast-view-entire-safe»
import ZlibF.Proof.«inflate.c.fast-view-public-accounting»
import ZlibF.Proof.«inflate.c.fast-view-whole-state-fields»
import ZlibF.Proof.«inflate.c.fast-view-whole-memory-shape»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The translated complete fast call preserves the default decoder relation
on general caller byte views, including every broken decoder exit. -/
theorem inflate_fast_default_view_normalized
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
      DefaultStateJ finished r zs zNext sNext ∧ sNext.bits.toNat < 8 := by
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
  obtain ⟨finished, zNext, sNext, hSuffix, good, _, _, _, small, _⟩ :=
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
      hPrefix loopExact hSuffix, by simpa only [sameR, sameZs] using good, small⟩

/-- The actual general-view fast call supplies the state, stream, size,
window and held-bit fields needed by the caller. Its output interval frame
is a separate source-derived obligation, not an assumed callee contract. -/
theorem inflate_fast_default_view_caller_fields
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
    ∃ finished zNext sNext used made,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h = .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      StreamAccounting z zNext used made ∧
      ByteViewSizes h finished ∧ sNext.window = s.window ∧
      (sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) ∧
      sNext.bits.toNat < 8 ∧
      (∀ ref : BRef, Space.ro finished ref = Space.ro h ref) ∧
      LiveChange h finished (fun _ => False) (fun _ => False) ∧
      finished.nalloc = h.nalloc := by
  obtain ⟨finished, zNext, sNext, used, made, run, current, accounting⟩ :=
    inflate_fast_default_view_public_core invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  obtain ⟨fieldsHeap, fieldsZ, fieldsS, fieldsRun, fieldsJ,
    sizes, window, modes⟩ :=
    inflate_fast_default_view_state_fields invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  have sameHeap : finished = fieldsHeap := congrArg Prod.snd
    (Except.ok.inj (run.symm.trans fieldsRun))
  subst fieldsHeap
  have sameState : fieldsS = sNext := Option.some.inj
    (fieldsJ.good.live.hs.symm.trans current.good.live.hs)
  subst fieldsS
  obtain ⟨normHeap, normZ, normS, normRun, normJ, small⟩ :=
    inflate_fast_default_view_normalized invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  have sameNorm : finished = normHeap := congrArg Prod.snd
    (Except.ok.inj (run.symm.trans normRun))
  subst normHeap
  have sameNormS : normS = sNext := Option.some.inj
    (normJ.good.live.hs.symm.trans current.good.live.hs)
  subst normS
  obtain ⟨live, nalloc, nextBlk, static, allocOk, garbage, ro⟩ :=
    inflate_fast_live_nalloc_of_run run
  have readonly : ∀ ref : BRef, Space.ro finished ref = Space.ro h ref := by
    intro ref
    cases ref <;> simp only [Space.ro, ro]
  exact ⟨finished, zNext, sNext, used, made, run, current, accounting,
    sizes, window, modes, small, readonly, live, nalloc⟩

#print axioms inflate_fast_default_view_caller_fields

#print axioms inflate_fast_default_view_normalized
end Zlib.Inflate.Proofs
