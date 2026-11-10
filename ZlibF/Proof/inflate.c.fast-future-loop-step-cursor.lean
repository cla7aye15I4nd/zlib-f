import ZlibF.Proof.«inflate.c.fast-future-loop-exit-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeTableInvariant
set_option autoImplicit false
set_option maxRecDepth 8192

/-- One real fast-loop body either exits safely or carries the independent
parser and output prefix into the exact next actual safety state. -/
theorem FastFutureReady.step_with_output_cursor
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (semantic : FastFutureReady ctx L D dict future tail target h q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      ((fastLoopCond ctx result after = .ok ((false, result), after) ∧
          FastFutureExitCursor ctx L D dict future tail target after result) ∨
       (fastLoopCond ctx result after = .ok ((true, result), after) ∧
          FastFutureReady ctx L D dict future tail target after result ∧
          fastLoopMeasure ctx result < fastLoopMeasure ctx q)) := by
  have incoming := semantic
  rcases semantic with ⟨slow, bs, output, off, k, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard, lenMeaning, distMeaning, distFlags,
    saved, woff, windowView, dictionary, dictCount, history,
    written, historyCount, input, lengthSource, parsed⟩
  obtain ⟨lenUsed, meaning⟩ := lenMeaning
  obtain ⟨distUsed, distMeaning'⟩ := distMeaning
  have readyNow : FastLoopReady ctx h q := by
    exact ⟨slow, bs, output, off, k, packet, invariant, buffers,
      codesGet, distGet, bitsBound, leftEq, outEq, putPtr,
      nextPtr, lastPtr, inputMargin, outPtr, outputGet,
      outputWrite, outputSize, current, beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth, rest, rfl⟩ :=
    packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  have whaveBound : ctx.c.whave.toNat ≤ ctx.c.wsize.toNat := by
    rw [ctx.whaveEq, ctx.wsizeEq]
    exact invariant.good.inv.win.hv
  have wnextBound : ctx.c.wnext.toNat ≤ ctx.c.wsize.toNat := by
    rw [ctx.wnextEq, ctx.wsizeEq]
    rcases invariant.good.inv.win.wn with lt | zero <;> omega
  have wsizeBound : ctx.c.wsize.toNat ≤ 32768 := by
    rw [ctx.wsizeEq]
    have pow := Nat.pow_le_pow_right
      (by decide : 0 < 2) invariant.good.inv.win.wbits
    rcases invariant.good.inv.win.ws with zero | size <;> omega
  obtain ⟨usedSem, usedSafety, semResult, semAfter,
    semanticSlow, safetySlow, array, made, next, done,
    semBound, semRaw, safetyBound, semRun, semPacket,
    safetyPacket, semCursor, semGet, token, bytes,
    out, terminal, endSource, continuation, normalHeap,
    aligned⟩ :=
    packet.fast_body_symbols_future_safety_aligned
      invariant buffers ctx.statePtr ctx.mode ctx.lcodePtr codesGet
      ctx.lenSafe meaning ctx.lenMask bitsBound ctx.dcodePtr distGet
      ctx.distSafe distMeaning' distFlags ctx.distMask left avail
      outPtr putPtr ctx.begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard whaveBound
      wnextBound wsizeBound windowView lengthSource dictionary
      dictCount written historyCount parsed ctx.streamPtr
      ctx.whaveEq ctx.wsizeEq ctx.wnextEq ctx.windowEq
      nextPtr lastPtr
  obtain ⟨result, after, safetyRun, outcome⟩ := readyNow.step
  have same : (semResult, semAfter) = (result, after) :=
    Except.ok.inj (semRun.symm.trans safetyRun)
  cases same
  refine ⟨semResult, semAfter, semRun, ?_⟩
  rcases outcome with stopped | continuing
  · refine Or.inl ⟨stopped.1, stopped.2, h, q, incoming, semRun, semanticSlow,
      (first :: second :: third :: fourth :: fifth :: sixth :: rest).drop usedSem,
      array, k, made, next, done,
      input, history, semPacket, semGet, token, bytes, beginLe, ?_, ?_, ?_⟩
    · cases done with
      | false => exact out rfl
      | true =>
        have decodedEob : ∃ restBits,
            decodeSym L
              (stream slow
                (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
              some (256, restBits) := by
          cases token with
          | eob decode =>
              exact ⟨_, by simpa only [lengthSource] using decode⟩
        have kBound : k ≤ ctx.oo + slow.left.toNat := by
          have endWithin : ctx.oo + slow.left.toNat - 257 ≤ output.size := by
            omega
          have kWithin : k ≤ output.size := by
            by_cases inside : k ≤ output.size
            · exact inside
            · have impossible := guard
              simp [C.run, Ptr.lt, outPtr, endPtr, outputGet, inside] at impossible
          have inside := guard
          simp [C.run, Ptr.lt, outPtr, endPtr, outputGet,
            kWithin, endWithin] at inside
          omega
        obtain ⟨restBits, decoded⟩ := decodedEob
        obtain ⟨sourceResult, sourceAfter, sourceRun, sourceOut⟩ :=
          packet.fast_body_eob_output_cursor invariant buffers
            ctx.statePtr ctx.mode ctx.lcodePtr codesGet ctx.lenSafe
            meaning ctx.lenMask (oo := ctx.oo) outPtr outputGet kBound
            decoded
        have sameSource : (semResult, semAfter) = (sourceResult, sourceAfter) :=
          Except.ok.inj (semRun.symm.trans sourceRun)
        cases sameSource
        have zero : made = 0 := (terminal rfl).2.2
        simpa only [zero, Nat.add_zero] using sourceOut.trans outPtr
    · intro notDone
      exact continuation notDone
    · intro isDone
      exact ⟨(endSource isDone).1, (endSource isDone).2,
        (terminal isDone).2.1, (terminal isDone).1,
        (terminal isDone).2.2⟩
  · obtain ⟨condRun, nextReady, measure⟩ := continuing
    have normal := fastLoopCond_true_not_broken condRun
    have doneFalse : done = false := by
      cases done with
      | false => rfl
      | true => exact False.elim (by have t := terminal rfl; simp [normal] at t)
    rcases nextReady with ⟨slowN, bsN, outputN, offN, kN,
      packetN, invariantN, buffersN, codesGetN, distGetN,
      bitsBoundN, leftEqN, outEqN, putPtrN, nextPtrN, lastPtrN,
      inputMarginN, outPtrN, outputGetN, outputWriteN,
      outputSizeN, currentN, beginLeN, spanN, guardN⟩
    have rawMargin : 6 ≤
        (first :: second :: third :: fourth :: fifth :: sixth :: rest).length := by simp
    have nextMargin : 6 ≤ bsN.length := by
      rw [← packetN.source.have_eq]
      exact inputMarginN
    have oldLast : ctx.c.last = .ref ctx.inputRef
        (off + (first :: second :: third :: fourth :: fifth :: sixth :: rest).length - 5) := by
      simpa only [packet.source.have_eq] using lastPtr
    have newLast : ctx.c.last = .ref ctx.inputRef
        (offN + bsN.length - 5) := by
      simpa only [packetN.source.have_eq] using lastPtrN
    have physical : semResult.in_ = inputAdvance (.ref ctx.inputRef off) usedSem := by
      rw [semCursor, packet.cursor, nextPtr]
    obtain ⟨sameRaw, sameStream, parsedN⟩ :=
      fast_continuing_future_symbols_transport semPacket packetN
        rawMargin nextMargin semRaw oldLast newLast physical
        nextPtrN (continuation doneFalse)
    have outNext := out doneFalse
    have outEqNext : kN = k + made := by
      have samePtr := outNext.symm.trans outPtrN
      exact (Ptr.ref.inj samePtr).2.symm
    have arrayEq : array = outputN :=
      Option.some.inj (semGet.symm.trans outputGetN)
    have writtenN : ZlibF.Math.LZ77Copy.writtenBytes outputN
        kN (kN - ctx.bg) = next := by
      rw [← arrayEq, outEqNext]
      have countEq : k + made - ctx.bg = (k - ctx.bg) + made := by omega
      rw [countEq]
      exact bytes
    obtain ⟨newOutput, writeEq⟩ := normalHeap normal
    have windowN : 0 < ctx.c.whave.toNat → ∃ window,
        window ≠ ctx.dest ∧ ctx.c.window = .ref window woff ∧
        Space.get semAfter window = some saved ∧
        woff + ctx.c.wsize.toNat ≤ saved.size :=
      fast_window_view_after_output windowView writeEq
    have historyCountN : next.length = kN - ctx.bg := by
      rw [← writtenN]
      simp only [ZlibF.Math.LZ77Copy.writtenBytes,
        List.length_take, List.length_drop, Array.length_toList]
      have endN : ctx.c.end_ = .ref ctx.dest
          (ctx.oo + slowN.left.toNat - 257) := by
        rw [leftEqN]
        exact ctx.endPtr
      have endWithin : ctx.oo + slowN.left.toNat - 257 ≤ outputN.size := by
        omega
      have kWithin : kN ≤ outputN.size := by
        by_cases inside : kN ≤ outputN.size
        · exact inside
        · have impossible := guardN
          simp [C.run, Ptr.lt, outPtrN, endN, outputGetN, inside] at impossible
      have g : kN < ctx.oo + slowN.left.toNat - 257 := by
        have equal := guardN
        simp [C.run, Ptr.lt, outPtrN, endN, outputGetN,
          kWithin, endWithin] at equal
        exact equal
      omega
    have semanticN : FastFutureReady ctx L D dict future tail target
        semAfter semResult := by
      exact ⟨slowN, bsN, outputN, offN, kN, packetN, invariantN,
        buffersN, codesGetN, distGetN, bitsBoundN, leftEqN,
        outEqN, putPtrN, nextPtrN, lastPtrN, inputMarginN,
        outPtrN, outputGetN, outputWriteN, outputSizeN, currentN,
        beginLeN, spanN, guardN, ⟨lenUsed, meaning⟩,
        ⟨distUsed, distMeaning'⟩, distFlags, saved, woff,
        windowN, dictionary, dictCount, next, writtenN,
        historyCountN, stream slowN bsN, rfl, parsedN⟩
    exact Or.inr ⟨condRun, semanticN, measure⟩

#print axioms FastFutureReady.step_with_output_cursor
end Zlib.Inflate.Proofs
