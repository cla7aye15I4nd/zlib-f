import ZlibF.Proof.«inflate.c.fast-view-entire-safe»
import ZlibF.Proof.«inflate.c.fast-view-loop-stream-fields-frame»
import ZlibF.Proof.«inflate.c.fast-writeback-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The complete translated fast call accounts for byte movements against
the original public stream, including every broken decoder exit. -/
theorem inflate_fast_default_view_accounting
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
    ∃ finished zNext sNext used produced,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      Good finished r zs zNext sNext ∧
      StreamAccounting z zNext used produced := by
  obtain ⟨ir, dest, io, oo, ctx, initial, result, after,
    off, used, input, nextPtr, putPtr, inputRef, destRef,
    outputOff, leftTotal, sameR, sameZs, last, end_,
    initialIn, initialOut, initialBitsEq, prefixRun, ready,
    loopRun, final, budget, output, limit, resultCursor,
    inputGet, usedBound, count, rollback⟩ :=
    fastEntryLoop_run_with_geometry invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have sizes : ByteViewSizes h after := ready.byte_view_sizes_of_run loopRun
  obtain ⟨initialInput, initialGet, initialBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using buffers.input)
  have inputSizeEq : input.size = initialInput.size := by
    have equal := sizes ir
    rw [initialGet, inputGet] at equal
    simpa only [Option.map_some, Option.some.injEq] using equal
  have inputBoundAfter : io + slow.have_.toNat ≤ input.size := by omega
  obtain ⟨finalSlow, finalBs, finalZ, finalS,
    finalPacket, finalJ, finalBuffers⟩ := final
  have fields : streamFastFields finalZ = streamFastFields z := by
    have frame := fast_loop_stream_fields_of_run loopRun
    have initialGet := invariant.good.live.hz
    have finalGet := finalJ.good.live.hz
    rw [sameR] at frame finalGet
    simp only [StreamFastFrame, initialGet, finalGet,
      Option.map_some, Option.some.injEq] at frame
    exact frame
  have nextInEq : finalZ.next_in = z.next_in := by
    have projected := congrArg ZStream.next_in fields
    simpa only [streamFastFields] using projected
  have availInEq : finalZ.avail_in = z.avail_in := by
    have projected := congrArg ZStream.avail_in fields
    simpa only [streamFastFields] using projected
  have nextOutEq : finalZ.next_out = z.next_out := by
    have projected := congrArg ZStream.next_out fields
    simpa only [streamFastFields] using projected
  have availOutEq : finalZ.avail_out = z.avail_out := by
    have projected := congrArg ZStream.avail_out fields
    simpa only [streamFastFields] using projected
  have stateEq : finalZ.state = z.state := by
    have projected := congrArg ZStream.state fields
    simpa only [streamFastFields] using projected
  have allocEq : finalZ.zalloc = z.zalloc := by
    have projected := congrArg ZStream.zalloc fields
    simpa only [streamFastFields] using projected
  have freeEq : finalZ.zfree = z.zfree := by
    have projected := congrArg ZStream.zfree fields
    simpa only [streamFastFields] using projected
  have opaqueEq : finalZ.opaque = z.opaque := by
    have projected := congrArg ZStream.opaque fields
    simpa only [streamFastFields] using projected
  have reservedEq : finalZ.reserved = z.reserved := by
    have projected := congrArg ZStream.reserved fields
    simpa only [streamFastFields] using projected
  obtain ⟨outOff, outputArray, outPtr, outLower, outUpper,
    outputGet, outputSize⟩ := output
  simp only [destRef, outputOff, leftTotal] at outPtr outLower outUpper outputGet outputSize
  obtain ⟨limitOff, lastOff, limitCursor, limitLast,
    limitBound⟩ := limit
  rw [inputRef] at limitCursor limitLast
  have sameOff : limitOff = off :=
    (Ptr.ref.inj (limitCursor.symm.trans resultCursor)).2
  subst limitOff
  have sameLast : lastOff = io + slow.have_.toNat - 5 :=
    (Ptr.ref.inj (limitLast.symm.trans last)).2
  subst lastOff
  have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧ slow.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputMarginNat : 6 ≤ slow.have_.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.1
  obtain ⟨accountOff, accountPtr, accountLower, accountBits⟩ := budget
  rw [inputRef] at accountPtr
  have sameAccountOff : accountOff = off :=
    (Ptr.ref.inj (accountPtr.symm.trans resultCursor)).2
  have ioLeOff : io ≤ off := by rw [sameAccountOff] at accountLower; exact accountLower
  have cursorBound : off ≤ input.size := by omega
  have buffered : (result.bits >>> 3).toNat ≤ off := by omega
  let produced := outOff - oo
  have inputMove : off - (result.bits >>> 3).toNat = io + used := by omega
  have outputMove : outOff = oo + produced := by omega
  have usedAtMost : used ≤ slow.have_.toNat := by omega
  have producedAtMost : produced ≤ slow.left.toNat := by omega
  have inputPtr : finalZ.next_in = .ref ir io := by
    rw [nextInEq, inputCursor, nextPtr]
  have outputPtr : finalZ.next_out = .ref dest oo := by
    rw [nextOutEq, outputCursor, putPtr]
  have lastFinal : ctx.c.last = .ref ir
      (io + finalZ.avail_in.toNat - 5) := by
    rw [availInEq, inputCount]
    exact last
  have endFinal : ctx.c.end_ = .ref dest
      (oo + finalZ.avail_out.toNat - 257) := by
    rw [availOutEq, outputCount]
    exact end_
  have inMargin : 6 ≤ finalZ.avail_in.toNat := by
    rw [availInEq, inputCount]
    exact inputMarginNat
  have outMargin : 258 ≤ finalZ.avail_out.toNat := by
    rw [availOutEq, outputCount]
    simpa [UInt32.le_iff_toNat_le] using margins.1.2
  have inputBound : io + finalZ.avail_in.toNat ≤ input.size := by
    rw [availInEq, inputCount]
    exact inputBoundAfter
  have outputBound : oo + finalZ.avail_out.toNat ≤ outputArray.size := by
    rw [availOutEq, outputCount]
    exact outputSize
  have usedFinal : used ≤ finalZ.avail_in.toNat := by
    rw [availInEq, inputCount]
    exact usedAtMost
  have producedFinal : produced ≤ finalZ.avail_out.toNat := by
    rw [availOutEq, outputCount]
    exact producedAtMost
  have post := fastAfterLoopView_public_post ctx.c result ctx.streamPtr
    ctx.statePtr finalJ.good inputGet outputGet
    (finalJ.platform ir input inputGet)
    (finalJ.platform dest outputArray outputGet)
    inputPtr outputPtr resultCursor outPtr lastFinal endFinal
    inMargin outMargin inputBound outputBound cursorBound buffered
    inputMove outputMove usedFinal producedFinal []
  dsimp only at post
  obtain ⟨finished, suffixRun, good, accounting, _, _, _, _, _⟩ := post
  let zNext : ZStream := { finalZ with
    next_in := .ref ir (io + used),
    next_out := .ref dest (oo + produced),
    avail_in := UInt32.ofNat (finalZ.avail_in.toNat - used),
    avail_out := UInt32.ofNat (finalZ.avail_out.toNat - produced) }
  let bits := result.bits - ((result.bits >>> 3) <<< 3)
  let hold := result.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  let sNext : InflateState := { finalS with hold, bits }
  have publicAccounting : StreamAccounting z zNext used produced := by
    change StreamAccounting finalZ zNext used produced at accounting
    simpa only [StreamAccounting, nextInEq, availInEq, nextOutEq,
      availOutEq, stateEq, allocEq, freeEq, opaqueEq, reservedEq]
      using accounting
  have loopExact : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ ctx.c.last then
          pure (← Ptr.lt q.out ctx.c.end_, q)
        else pure (false, q)) initial) h = .ok (result, after) := loopRun
  refine ⟨finished, zNext, sNext, used, produced,
    inflate_fast_compose (some r) slow.out_ ctx.c initial result
      prefixRun loopExact suffixRun, ?_, publicAccounting⟩
  simpa only [sameR, sameZs, zNext, sNext, bits, hold] using good

/-- The actual fast call simultaneously retains the initialized decoder
relation and accounts for bytes against its entry stream. -/
theorem inflate_fast_default_view_public_core
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
    ∃ finished zNext sNext used produced,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      StreamAccounting z zNext used produced := by
  obtain ⟨finished, zNext, sNext, run, invariantNext⟩ :=
    inflate_fast_default_view_J invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  obtain ⟨other, otherZ, otherS, used, produced,
    otherRun, good, accounting⟩ :=
    inflate_fast_default_view_accounting invariant buffers mode
      inputCursor inputCount outputCursor outputCount
      stateHold stateBits fast
  have same : finished = other := congrArg Prod.snd
    (Except.ok.inj (run.symm.trans otherRun))
  subst other
  have sameZ : zNext = otherZ := Option.some.inj
    (invariantNext.good.live.hz.symm.trans good.live.hz)
  have sameS : sNext = otherS := Option.some.inj
    (invariantNext.good.live.hs.symm.trans good.live.hs)
  subst otherZ
  subst otherS
  exact ⟨finished, zNext, sNext, used, produced,
    run, invariantNext, accounting⟩

#print axioms inflate_fast_default_view_accounting
#print axioms inflate_fast_default_view_public_core
end Zlib.Inflate.Proofs
