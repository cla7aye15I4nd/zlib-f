import ZlibF.Proof.«inflate.c.fast-future-callee-prefix-cursor»
import ZlibF.Proof.«inflate.c.fast-view-loop-state-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-output-effect»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- One actual fast decoder effect leaves checksum and wrapper selectors
untouched. The BAD case changes only `msg` and `mode`; TYPE changes only
`mode`, and output writes change only the byte view. -/
theorem FastOutputEffect.checksum_frame
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z zNext : ZStream} {s sNext : InflateState}
    {slow : IL} {dest : BRef}
    (effect : FastOutputEffect before after r zs z s slow dest)
    (source : DefaultStateJ before r zs z s)
    (final : DefaultStateJ after r zs zNext sNext) :
    sNext.check = s.check ∧ zNext.adler = z.adler ∧
      sNext.wrap = s.wrap ∧ sNext.flags = s.flags := by
  rcases effect with ⟨array, heapEq, _⟩ | ⟨i, heapEq⟩ | heapEq
  · subst after
    obtain ⟨streamEq, stateEq⟩ :=
      source.same_records_of_byte_put final
    subst zNext; subst sNext
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have stateEq : sNext = {s with mode := BAD} := by
      have get := final.good.live.hs
      simp only [heapEq, badHeap, setI_istates_same] at get
      exact Option.some.inj get.symm
    have streamEq : zNext = {z with msg := .ref (.str i) 0} := by
      have get := final.good.live.hz
      rw [heapEq, badHeap, ZStreamRef.get_setI,
        ZStreamRef.get_put_same source.good.live.hz] at get
      exact Option.some.inj get.symm
    subst zNext; subst sNext
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have stateEq : sNext = {s with mode := TYPE} := by
      have get := final.good.live.hs
      simp only [heapEq, setI_istates_same] at get
      exact Option.some.inj get.symm
    have streamEq : zNext = z := by
      have get := final.good.live.hz
      rw [heapEq, ZStreamRef.get_setI] at get
      exact Option.some.inj (get.symm.trans source.good.live.hz)
    subst zNext; subst sNext
    exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms FastOutputEffect.checksum_frame

/-- The actual last decoder body retains checksum and wrapper fields in the
state and stream records, including BAD and TYPE exits. -/
theorem FastLoopReady.body_checksum_frame
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) ∧
      ∀ zNext sNext, DefaultStateJ after ctx.r ctx.zs zNext sNext →
        sNext.check = ctx.s.check ∧ zNext.adler = ctx.z.adler ∧
          sNext.wrap = ctx.s.wrap ∧ sNext.flags = ctx.s.flags := by
  rcases ready with ⟨slow, bs, output, off, k, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth, rest, rfl⟩ :=
    packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by
    rw [leftEq]
    exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by
    rw [leftEq]
    exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  obtain ⟨slowFinal, result, after, run, effect, _⟩ :=
    packet.fast_body_output_effect invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  refine ⟨result, after, run, ?_⟩
  intro zNext sNext currentJ
  exact effect.checksum_frame invariant currentJ

#print axioms FastLoopReady.body_checksum_frame

/-- The complete finite semantic exit has a real last body, so checksum and
wrapper fields can be read from that source event without induction over
bytes or an assumed callee contract. -/
theorem FastFutureExitCursor.checksum_frame
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (exit : FastFutureExitCursor ctx L D dict future tail target h q) :
    ∀ zNext sNext, DefaultStateJ h ctx.r ctx.zs zNext sNext →
      sNext.check = ctx.s.check ∧ zNext.adler = ctx.z.adler ∧
        sNext.wrap = ctx.s.wrap ∧ sNext.flags = ctx.s.flags := by
  obtain ⟨_, before, prior, ready, bodyRun, _⟩ := exit
  obtain ⟨result, after, replay, fields⟩ := ready.toSafety.body_checksum_frame
  have same : (q, h) = (result, after) :=
    Except.ok.inj (bodyRun.symm.trans replay)
  cases same
  exact fields

#print axioms FastFutureExitCursor.checksum_frame

/-- The actual fast writeback changes only stream byte cursors/counts and
held-bit registers. In particular it does not credit any bytes to Adler
or change the current checksum. -/
theorem FastLoopExit.writeback_checksum_frame
    {ctx : FastLoopContext} {h : Heap} {result : Zlib.Inffast.L}
    {startOff startBits inputCount : Nat} {input : Array UInt8}
    (final : FastLoopExit ctx h result)
    (account : FastLoopInputBudget ctx startOff startBits result)
    (limit : FastLoopInputLimit ctx result)
    (output : FastLoopOutputRange ctx h result)
    (initialBits : startBits < 8)
    (last : ctx.c.last = .ref ctx.inputRef (startOff + inputCount - 5))
    (inputMargin : 6 ≤ inputCount) (inputWidth : inputCount < 2 ^ 32)
    (inputGet : Space.get h ctx.inputRef = some input)
    (inputBound : startOff + inputCount ≤ input.size) :
    ∃ finished zNext sNext zBefore sBefore,
      C.run (fastAfterLoopView ctx.c result) h = .ok ((), finished) ∧
      DefaultStateJ h ctx.r ctx.zs zBefore sBefore ∧
      DefaultStateJ finished ctx.r ctx.zs zNext sNext ∧
      sNext.check = sBefore.check ∧ zNext.adler = zBefore.adler ∧
      sNext.wrap = sBefore.wrap ∧ sNext.flags = sBefore.flags := by
  obtain ⟨slow, bs, z, s, packet, invariant, buffers⟩ := final
  obtain ⟨io, inPtr, lower, budget⟩ := account
  obtain ⟨io2, lastOff, limitPtr, lastPtr, upper⟩ := limit
  have sameIn : io2 = io := (Ptr.ref.inj (limitPtr.symm.trans inPtr)).2
  subst io2
  have sameLast : lastOff = startOff + inputCount - 5 :=
    (Ptr.ref.inj (lastPtr.symm.trans last)).2
  subst lastOff
  obtain ⟨oo, array, outPtr, outputLower, outputUpper,
    outputGet, outputSize⟩ := output
  have returned : (result.bits >>> 3).toNat ≤ io - startOff := by
    rw [Zlib.Inffast.Proofs.bits_whole]
    omega
  have inputFit : input.size < 2 ^ 63 :=
    invariant.platform ctx.inputRef input inputGet
  have outputFit : array.size < 2 ^ 63 :=
    invariant.platform ctx.dest array outputGet
  have outputWidth := UInt32.toNat_lt ctx.leftTotal
  have outputMargin := ctx.avail
  have raw := fastAfterLoopView_run ctx.c result ctx.streamPtr
    ctx.statePtr invariant.good.live.hz
    (by cases ctx.r <;> rfl) invariant.good.live.hs
    inputGet outputGet inputFit outputFit inPtr last outPtr
    ctx.endPtr (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  let bits := result.bits - ((result.bits >>> 3) <<< 3)
  let hold := result.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  let in_ : BPtr := .ref ctx.inputRef
    (io - (result.bits >>> 3).toNat)
  let ai := UInt32.ofNat
    (startOff + inputCount - 5 + 5 -
      (io - (result.bits >>> 3).toNat))
  let ao := UInt32.ofNat
    (ctx.oo + ctx.leftTotal.toNat - 257 + 257 - oo)
  let zNext : ZStream := { z with
    next_in := in_, next_out := result.out,
    avail_in := ai, avail_out := ao }
  let sNext : InflateState := { s with hold, bits }
  let finished := setI (ctx.r.put h zNext) ctx.zs sNext
  have run : C.run (fastAfterLoopView ctx.c result) h =
      .ok ((), finished) := by
    simpa only [finished, zNext, sNext, hold, bits, in_,
      ai, ao, setI, C.run] using raw
  have current :=
    (invariant.fast_writeback_normalized result in_ result.out ai ao).1
  exact ⟨finished, zNext, sNext, z, s, run, invariant,
    current, rfl, rfl, rfl, rfl⟩

#print axioms FastLoopExit.writeback_checksum_frame

/-- One complete actual fast call leaves the checksum state uncredited.
The only writes to the stream are byte cursor/count updates, and the final
held-bit normalization preserves `check`, `adler`, `wrap`, and `flags`. -/
theorem FastFutureReady.callee_checksum_frame
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h after finished : Heap} {q result : Zlib.Inffast.L}
    {zNext : ZStream} {sNext : InflateState}
    (semantic : FastFutureReady ctx L D dict future tail target h q)
    (smallBits : q.bits.toNat < 8)
    (loopRun : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after))
    (suffixRun : C.run (fastAfterLoopView ctx.c result) after =
      .ok ((), finished))
    (current : DefaultStateJ finished ctx.r ctx.zs zNext sNext) :
    sNext.check = ctx.s.check ∧ zNext.adler = ctx.z.adler ∧
      sNext.wrap = ctx.s.wrap ∧ sNext.flags = ctx.s.flags := by
  rcases semantic.toSafety with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, currentOut,
    beginLe, span, guard⟩
  have cursor : q.in_ = .ref ctx.inputRef off :=
    packet.cursor.trans nextPtr
  obtain ⟨other, otherAfter, otherRun, exit, budget,
    outputRange, inputLimit, sizes⟩ := semantic.run_accounted
      (FastLoopInputBudget.initial cursor)
  have same : (result, after) = (other, otherAfter) :=
    Except.ok.inj (loopRun.symm.trans otherRun)
  cases same
  obtain ⟨inputBefore, beforeGet, beforeBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using buffers.input)
  obtain ⟨inputAfter, afterGet, sizeEq⟩ := sizes.view beforeGet
  have inputBound : off + slow.have_.toNat ≤ inputAfter.size := by
    omega
  obtain ⟨finishedOther, zOther, sOther, zBefore, sBefore,
    otherSuffix, beforeJ, afterJ, checkEq, adlerEq, wrapEq,
    flagsEq⟩ := exit.1.writeback_checksum_frame budget inputLimit
      outputRange smallBits lastPtr inputMargin
      (UInt32.toNat_lt slow.have_) afterGet inputBound
  have sameSuffix : finished = finishedOther := by
    have pair := Except.ok.inj (suffixRun.symm.trans otherSuffix)
    exact congrArg Prod.snd pair
  subst finishedOther
  have sameZ : zNext = zOther := Option.some.inj
    (current.good.live.hz.symm.trans afterJ.good.live.hz)
  have sameS : sNext = sOther := Option.some.inj
    (current.good.live.hs.symm.trans afterJ.good.live.hs)
  subst zOther
  subst sOther
  obtain ⟨cursorResult, cursorAfter, cursorRun, cursorExit⟩ :=
    semantic.run_with_output_cursor
  have sameCursor : (result, after) =
      (cursorResult, cursorAfter) :=
    Except.ok.inj (loopRun.symm.trans cursorRun)
  cases sameCursor
  obtain ⟨checkBefore, adlerBefore, wrapBefore, flagsBefore⟩ :=
    cursorExit.checksum_frame zBefore sBefore beforeJ
  exact ⟨checkEq.trans checkBefore,
    adlerEq.trans adlerBefore,
    wrapEq.trans wrapBefore,
    flagsEq.trans flagsBefore⟩

#print axioms FastFutureReady.callee_checksum_frame
end Zlib.Inflate.Proofs
