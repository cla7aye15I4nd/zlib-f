import ZlibF.Proof.«inflate.c.local-fast-canonical»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Internal observations of the same actual body execution. The entry
proof fixes the caller packet and output cursor used by the source proof.
This metadata is produced internally, never assumed at a public entry. -/
inductive FastLoopBodyObserved (cutoff : Nat) (ctx : FastLoopContext)
    (h : Heap) (q result : Zlib.Inffast.L) (after : Heap) : Prop where
  | intro (slow : IL) (bs : List UInt8)
      (output : Array UInt8) (off start : Nat)
      (packet : FastInputPacket h slow bs q)
      (invariant : LocalStateJ h cutoff ctx.r ctx.zs ctx.z ctx.s)
      (buffers : DispatchBuffers h ctx.r slow bs)
      (codesGet : Space.get h ctx.codeRef = some ctx.codes)
      (distGet : Space.get h ctx.distRef = some ctx.distCodes)
      (bitsBound : slow.bits.toNat ≤ 30)
      (leftEq : slow.left = ctx.leftTotal)
      (outEq : slow.out_ = ctx.outTotal)
      (putPtr : slow.put = .ref ctx.dest ctx.oo)
      (nextPtr : slow.next = .ref ctx.inputRef off)
      (lastPtr : ctx.c.last = .ref ctx.inputRef
        (off + slow.have_.toNat - 5))
      (inputMargin : 6 ≤ slow.have_.toNat)
      (outPtr : q.out = .ref ctx.dest start)
      (outputGet : Space.get h ctx.dest = some output)
      (outputWrite : Space.ro h ctx.dest = false)
      (outputSize : ctx.oo + slow.left.toNat ≤ output.size)
      (current : ctx.oo ≤ start)
      (beginLe : ctx.bg ≤ start)
      (span : start - ctx.bg < 2 ^ 32)
      (guard : C.run (Ptr.lt q.out ctx.c.end_) h = .ok (true, h))
      (zNext : ZStream) (sNext : InflateState) (witness : IL) (witnessBytes : List UInt8)
      (run : C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after))
      (currentJ : LocalStateJ after cutoff ctx.r ctx.zs zNext sNext)
      (returnedPacket : FastInputPacket after witness witnessBytes result)
      (sizes : ByteViewSizes h after)
      (effect : FastExecEffect h after ctx.r ctx.zs ctx.z ctx.s slow ctx.dest start q result 6 258) :
      FastLoopBodyObserved cutoff ctx h q result after

/-- The actual body observations either exit or establish the next local
loop entry with a strict output-space decrease. -/
theorem FastLoopReady.step_of_observed
    {cutoff : Nat} {ctx : FastLoopContext} {h after : Heap}
    {q result : Zlib.Inffast.L}
    (observed : FastLoopBodyObserved cutoff ctx h q result after) :
    C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      ((fastLoopCond ctx result after = .ok ((false, result), after) ∧
          FastLoopExit cutoff ctx after result) ∨
       (fastLoopCond ctx result after = .ok ((true, result), after) ∧
          FastLoopReady cutoff ctx after result ∧
          fastLoopMeasure ctx result < fastLoopMeasure ctx q)) := by
  rcases observed with ⟨slow, bs, output, off, start, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard, zNext, sNext, witness, witnessBytes, run, nextJ, oldPacket, sizes, effect⟩
  obtain ⟨pulled, pulledBound, usedBound, canonicalPacket, finalBuffers, next,
      count, put, left, total, budget, held⟩ :=
    canonical_fast_body_packet invariant nextJ buffers packet oldPacket ctx.streamPtr run effect
      sizes putPtr outputGet inputMargin bitsBound
  let regs := canonicalFastSlow slow result pulled
  have packet' : FastInputPacket after regs (bs.drop pulled) result := canonicalPacket
  have nextPtr' : regs.next = .ref ctx.inputRef (off + pulled) := by
    rw [next, nextPtr]
    rfl
  have lastPtr' : ctx.c.last = .ref ctx.inputRef
      (off + pulled + regs.have_.toNat - 5) := by
    have count' : regs.have_.toNat + pulled = slow.have_.toNat := count
    have position : off + slow.have_.toNat - 5 = off + pulled + regs.have_.toNat - 5 := by omega
    rw [lastPtr, position]
  have endPtr : ctx.c.end_ = .ref ctx.dest (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have room := fast_output_max_room_of_guard outPtr endPtr outputGet outputSize current avail guard
  obtain ⟨finish, outputPtr, outputLower, outputUpper⟩ := effect.output
  have within : finish ≤ ctx.oo + slow.left.toNat := by omega
  have exit : FastLoopExit cutoff ctx after result :=
    ⟨regs, bs.drop pulled, zNext, sNext, packet', nextJ, finalBuffers⟩
  refine ⟨run, ?_⟩
  by_cases broken : result.broke = true
  · left
    exact ⟨fast_loop_cond_broken broken, exit⟩
  · have notBroken : result.broke = false := by cases value : result.broke <;> simp_all
    have condition := packet'.fast_loop_cond_from_buffers finalBuffers notBroken nextPtr' lastPtr'
      outputPtr (put.trans putPtr) (by rw [left]; exact endPtr) (by rw [left]; exact within)
      (by rw [left]; exact avail)
    let keepGoing := decide (6 ≤ regs.have_.toNat) &&
      decide (finish + 258 ≤ ctx.oo + slow.left.toNat)
    have condRun : fastLoopCond ctx result after = .ok ((keepGoing, result), after) := by
      change fastLoopCond ctx result after = .ok
        ((decide (6 ≤ regs.have_.toNat) && decide (finish + 258 ≤ ctx.oo + regs.left.toNat), result), after) at condition
      simpa only [keepGoing, regs, canonicalFastSlow] using condition
    cases flag : keepGoing
    · left
      rw [flag] at condRun
      exact ⟨condRun, exit⟩
    · have margins : 6 ≤ regs.have_.toNat ∧ finish + 258 ≤ ctx.oo + slow.left.toNat := by
        simpa only [keepGoing, Bool.and_eq_true, decide_eq_true_eq] using flag
      obtain ⟨nextOutput, heapEq⟩ := effect.heap.nonbreaking_byte_put notBroken
      have streamEq : zNext = ctx.z := by
        have get := nextJ.good.live.hz
        rw [heapEq, byte_view_put_stream] at get
        exact Option.some.inj (get.symm.trans invariant.good.live.hz)
      have stateEq : sNext = ctx.s := by
        have get := nextJ.good.live.hs
        rw [heapEq, byte_view_put_istates] at get
        exact Option.some.inj (get.symm.trans invariant.good.live.hs)
      have currentJ : LocalStateJ after cutoff ctx.r ctx.zs ctx.z ctx.s := by
        simpa only [streamEq, stateEq] using nextJ
      obtain ⟨nextCodes, nextDist⟩ := fast_continuing_table_views heapEq codesGet distGet
      obtain ⟨progress, progressPtr, strict⟩ := effect.progress notBroken
      have same : progress = finish := (Ptr.ref.inj (progressPtr.symm.trans outputPtr)).2
      subst progress
      have decrease : ctx.oo + slow.left.toNat - finish < ctx.oo + slow.left.toNat - start := by omega
      have madeBound : slow.out_.toNat - slow.left.toNat ≤ ctx.oo := by rw [outEq, leftEq]; exact ctx.made
      have beginEq : ctx.bg = ctx.oo - (slow.out_.toNat - slow.left.toNat) := by rw [outEq, leftEq]; exact ctx.beginEq
      obtain ⟨array, arrayGet, sizeEq, arrayWrite, nextCurrent, nextBegin, nextSpan, nextGuard⟩ :=
        fast_continuing_output_view sizes heapEq outputGet outputWrite outputSize outputPtr endPtr current
          decrease margins.2 buffers.output.count madeBound beginEq
      have measure : fastLoopMeasure ctx result < fastLoopMeasure ctx q := by
        simp only [fastLoopMeasure, outputPtr, outPtr]
        rw [← leftEq]
        exact decrease
      right
      rw [flag] at condRun
      refine ⟨condRun, ?_, measure⟩
      exact ⟨regs, bs.drop pulled, array, off + pulled, finish, packet', currentJ, finalBuffers,
        nextCodes, nextDist, held notBroken, left.trans leftEq, total.trans outEq, put.trans putPtr,
        nextPtr', lastPtr', margins.1, outputPtr, arrayGet, arrayWrite,
        by rw [left]; omega, nextCurrent, nextBegin, nextSpan, nextGuard⟩

end Zlib.Inflate.Local
