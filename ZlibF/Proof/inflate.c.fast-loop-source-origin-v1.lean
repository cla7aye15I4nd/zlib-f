import ZlibF.Math.InflateFastSource
import ZlibF.Proof.«inflate.c.fast-future-loop-step-cursor»
import ZlibF.Proof.«inflate.c.payload-token-progress-stage»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeTableInvariant
open ZlibF.Math.InflateFastSource
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Physical input origin retained alongside the decoder's safety/parser
state. Pull and consumption counts are existential ghosts produced by the
actual source statements. They assert no future parse or public history. -/
def FastLoopSource (ctx : FastLoopContext) (entry : Zlib.Inffast.L)
    (startOff : Nat) (input : List UInt8) (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  ∃ pulled consumed slow,
    FastInputPacket h slow (input.drop pulled) q ∧
    Origin entry.hold.toNat entry.bits.toNat input q.hold.toNat q.bits.toNat pulled consumed ∧
    q.in_ = inputAdvance (.ref ctx.inputRef startOff) pulled

/-- The immutable fast `last` pointer and physical cursor identify the
current unread source, including arrays containing repeated bytes. -/
theorem FastLoopSource.align_packet
    {ctx : FastLoopContext} {entry q : Zlib.Inffast.L} {h : Heap}
    {startOff off pulled consumed : Nat} {input bs : List UInt8} {sourceSlow slow : IL}
    (rawMargin : 6 ≤ input.length)
    (initialLast : ctx.c.last = .ref ctx.inputRef (startOff + input.length - 5))
    (sourcePacket : FastInputPacket h sourceSlow (input.drop pulled) q)
    (source : Origin entry.hold.toNat entry.bits.toNat input q.hold.toNat q.bits.toNat pulled consumed)
    (physical : q.in_ = inputAdvance (.ref ctx.inputRef startOff) pulled)
    (packet : FastInputPacket h slow bs q)
    (nextPtr : slow.next = .ref ctx.inputRef off)
    (lastPtr : ctx.c.last = .ref ctx.inputRef (off + slow.have_.toNat - 5))
    (margin : 6 ≤ slow.have_.toNat) : bs = input.drop pulled := by
  have count : 6 ≤ bs.length := by rw [← packet.source.have_eq]; exact margin
  have last : ctx.c.last = .ref ctx.inputRef (off + bs.length - 5) := by
    simpa only [packet.source.have_eq] using lastPtr
  have sameLength : (input.drop pulled).length = bs.length :=
    fast_remaining_length_of_cursor rawMargin count source.pulledBound initialLast last physical
      (packet.cursor.trans nextPtr)
  have nonempty : input.drop pulled ≠ [] := by
    intro empty
    rw [empty] at sameLength
    simp only [List.length_nil] at sameLength
    omega
  exact (sourcePacket.unread_unique_of_length packet nonempty sameLength).symm

#print axioms FastLoopSource.align_packet

/-- A real fast body advances its exact physical source on both EOB and
continuing paths. The semantic body supplies the actual cursor and token;
no choice of a future suffix is used to identify unread bytes. -/
theorem FastFutureReady.step_source_origin
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q entry : Zlib.Inffast.L} {startOff : Nat} {input0 : List UInt8}
    (semantic : FastFutureReady ctx L D dict future tail target h q)
    (tracked : FastLoopSource ctx entry startOff input0 h q)
    (rawMargin : 6 ≤ input0.length)
    (initialLast : ctx.c.last = .ref ctx.inputRef (startOff + input0.length - 5)) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      FastLoopSource ctx entry startOff input0 after result ∧
      ((fastLoopCond ctx result after = .ok ((false, result), after) ∧
          FastFutureExitCursor ctx L D dict future tail target after result) ∨
       (fastLoopCond ctx result after = .ok ((true, result), after) ∧
          FastFutureReady ctx L D dict future tail target after result ∧
          fastLoopMeasure ctx result < fastLoopMeasure ctx q)) := by
  have incoming := semantic
  obtain ⟨pulled, consumed, sourceSlow, sourcePacket, origin, physical⟩ := tracked
  rcases semantic with ⟨slow, bs, output, off, k, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard, lenMeaning, distMeaning, distFlags,
    saved, woff, windowView, dictionary, dictCount, history,
    written, historyCount, input, lengthSource, parsed⟩
  have rawEq := FastLoopSource.align_packet rawMargin initialLast sourcePacket origin physical
    packet nextPtr lastPtr inputMargin
  obtain ⟨lenUsed, meaning⟩ := lenMeaning
  obtain ⟨distUsed, distMeaning'⟩ := distMeaning
  obtain ⟨first, second, third, fourth, fifth, sixth, rest, rfl⟩ :=
    packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]; exact ctx.endPtr
  have whaveBound : ctx.c.whave.toNat ≤ ctx.c.wsize.toNat := by
    rw [ctx.whaveEq, ctx.wsizeEq]; exact invariant.good.inv.win.hv
  have wnextBound : ctx.c.wnext.toNat ≤ ctx.c.wsize.toNat := by
    rw [ctx.wnextEq, ctx.wsizeEq]
    rcases invariant.good.inv.win.wn with lt | zero <;> omega
  have wsizeBound : ctx.c.wsize.toNat ≤ 32768 := by
    rw [ctx.wsizeEq]
    have pow := Nat.pow_le_pow_right (by decide : 0 < 2) invariant.good.inv.win.wbits
    rcases invariant.good.inv.win.ws with zero | size <;> omega
  obtain ⟨usedSem, usedSafety, semResult, semAfter,
    semanticSlow, safetySlow, array, made, next, done,
    semBound, semRaw, safetyBound, semRun, semPacket,
    safetyPacket, semCursor, semGet, token, bytes,
    out, terminal, endSource, continuation, normalHeap, aligned⟩ :=
    packet.fast_body_symbols_future_safety_aligned
      invariant buffers ctx.statePtr ctx.mode ctx.lcodePtr codesGet
      ctx.lenSafe meaning ctx.lenMask bitsBound ctx.dcodePtr distGet
      ctx.distSafe distMeaning' distFlags ctx.distMask left avail
      outPtr putPtr ctx.begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard whaveBound
      wnextBound wsizeBound windowView lengthSource dictionary
      dictCount written historyCount parsed ctx.streamPtr
      ctx.whaveEq ctx.wsizeEq ctx.wnextEq ctx.windowEq nextPtr lastPtr
  obtain ⟨taken, _positive, takenBound, takenSource, _takenCount⟩ := token.consumed_count
  rw [lengthSource] at takenBound takenSource
  have beforeWord : stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest) =
      natBits q.bits.toNat q.hold.toNat ++ bytesBits (input0.drop pulled) := by
    simp only [stream, ← packet.bits, ← packet.hold, rawEq]
  have usedBound : usedSem ≤ (input0.drop pulled).length := by rwa [rawEq] at semRaw
  have takenBound0 : taken ≤ (natBits q.bits.toNat q.hold.toNat ++ bytesBits (input0.drop pulled)).length := by
    rwa [beforeWord] at takenBound
  have stepSource : natBits semResult.bits.toNat semResult.hold.toNat ++
      bytesBits ((input0.drop pulled).drop usedSem) =
      (natBits q.bits.toNat q.hold.toNat ++ bytesBits (input0.drop pulled)).drop taken := by
    simpa only [stream, ← semPacket.bits, ← semPacket.hold, ← packet.bits, ← packet.hold, rawEq] using takenSource
  have nextOrigin := origin.advance usedBound takenBound0 stepSource
  have nextPacket : FastInputPacket semAfter semanticSlow (input0.drop (pulled + usedSem)) semResult := by
    simpa only [rawEq, List.drop_drop] using semPacket
  have nextCursor : semResult.in_ = inputAdvance (.ref ctx.inputRef startOff) (pulled + usedSem) := by
    rw [semCursor, physical, inputAdvance_add]
  have nextTracked : FastLoopSource ctx entry startOff input0 semAfter semResult :=
    ⟨pulled + usedSem, consumed + taken, semanticSlow, nextPacket, nextOrigin, nextCursor⟩
  obtain ⟨result, after, actual, outcome⟩ := incoming.step_with_output_cursor
  have same := Except.ok.inj (semRun.symm.trans actual)
  cases same
  exact ⟨semResult, semAfter, semRun, nextTracked, outcome⟩

#print axioms FastFutureReady.step_source_origin
/-- The actual finite do-while produces a physical source origin at exit.
No public-history closure or chosen unread suffix is assumed at an
intermediate body. -/
theorem FastFutureReady.run_source_origin_tracked
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q entry : Zlib.Inffast.L} {startOff : Nat} {input0 : List UInt8}
    (semantic : FastFutureReady ctx L D dict future tail target h q)
    (tracked : FastLoopSource ctx entry startOff input0 h q)
    (rawMargin : 6 ≤ input0.length)
    (initialLast : ctx.c.last = .ref ctx.inputRef (startOff + input0.length - 5)) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c) (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastFutureExitCursor ctx L D dict future tail target after result ∧
      FastLoopSource ctx entry startOff input0 after result := by
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastFutureReady ctx L D dict future tail target heap current ∧
      FastLoopSource ctx entry startOff input0 heap current
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastFutureExitCursor ctx L D dict future tail target heap current ∧
      FastLoopSource ctx entry startOff input0 heap current
  have step : ∀ current heap, Inv current heap →
      ∃ result after, Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2, fastLoopCond ctx result after = .ok ((false, next), heap2) ∧ Final next heap2) ∨
         (∃ next heap2, fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
           Inv next heap2 ∧ fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap state
    obtain ⟨result, after, body, source, outcome⟩ :=
      state.1.step_source_origin state.2 rawMargin initialLast
    refine ⟨result, after, body, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1, stopped.2, source⟩
    · exact Or.inr ⟨result, after, continuing.1, ⟨continuing.2.1, source⟩, continuing.2.2⟩
  have fuelBound : fastLoopMeasure ctx q < fuel := by
    rcases semantic.toSafety with ⟨slow, bs, output, off, k, packet, invariant, buffers,
      codesGet, distGet, bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current, beginLe, span, guard⟩
    apply Zlib.Inffast.Proofs.lt_fuel_of
    simp only [fastLoopMeasure, outPtr]
    have width := UInt32.toNat_lt ctx.leftTotal
    omega
  obtain ⟨result, after, run, final⟩ :=
    Zlib.Inffast.Proofs.Wp.exists_eq
      (Zlib.Inffast.Proofs.Wp.cdoWhile Inv (fastLoopMeasure ctx) Final step
        ⟨semantic, tracked⟩ fuelBound)
  exact ⟨result, after, run, final⟩

/-- Initial actual source packet and physical entry geometry establish the
Origin base automatically, then the real loop produces its exit origin.
There is no incoming Origin or assumed callee run. -/
theorem FastFutureReady.run_source_origin_from_entry
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L} {startOff : Nat} {input0 : List UInt8} {entrySlow : IL}
    (semantic : FastFutureReady ctx L D dict future tail target h q)
    (packet : FastInputPacket h entrySlow input0 q)
    (entryCursor : q.in_ = .ref ctx.inputRef startOff)
    (rawMargin : 6 ≤ input0.length)
    (initialLast : ctx.c.last = .ref ctx.inputRef (startOff + input0.length - 5)) :
    ∃ result after finalSlow pulled consumed,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c) (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastFutureExitCursor ctx L D dict future tail target after result ∧
      FastInputPacket after finalSlow (input0.drop pulled) result ∧
      Origin q.hold.toNat q.bits.toNat input0 result.hold.toNat result.bits.toNat pulled consumed ∧
      result.in_ = inputAdvance (.ref ctx.inputRef startOff) pulled := by
  have tracked : FastLoopSource ctx q startOff input0 h q := by
    exact ⟨0, 0, entrySlow, by simpa only [List.drop_zero] using packet,
      Origin.initial q.hold.toNat q.bits.toNat input0, by simpa only [inputAdvance_zero] using entryCursor⟩
  obtain ⟨result, after, run, final, pulled, consumed, finalSlow, packet, origin, cursor⟩ :=
    semantic.run_source_origin_tracked tracked rawMargin initialLast
  exact ⟨result, after, finalSlow, pulled, consumed, run, final, packet, origin, cursor⟩

/-- The semantic entry already contains the actual physical input packet,
its margin and its fixed-last geometry. Thus a source-tracked real loop
exists without any additional caller source contract. -/
theorem FastFutureReady.run_source_origin
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (semantic : FastFutureReady ctx L D dict future tail target h q) :
    ∃ input0 startOff entrySlow result after finalSlow pulled consumed,
      FastInputPacket h entrySlow input0 q ∧ q.in_ = .ref ctx.inputRef startOff ∧
      ctx.c.last = .ref ctx.inputRef (startOff + input0.length - 5) ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c) (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastFutureExitCursor ctx L D dict future tail target after result ∧
      FastInputPacket after finalSlow (input0.drop pulled) result ∧
      Origin q.hold.toNat q.bits.toNat input0 result.hold.toNat result.bits.toNat pulled consumed ∧
      result.in_ = inputAdvance (.ref ctx.inputRef startOff) pulled := by
  rcases semantic.toSafety with ⟨slow, bs, output, off, k, packet, invariant, buffers,
    codesGet, distGet, bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current, beginLe, span, guard⟩
  have cursor : q.in_ = .ref ctx.inputRef off := packet.cursor.trans nextPtr
  have margin : 6 ≤ bs.length := by rw [← packet.source.have_eq]; exact inputMargin
  have last : ctx.c.last = .ref ctx.inputRef (off + bs.length - 5) := by
    simpa only [packet.source.have_eq] using lastPtr
  obtain ⟨result, after, finalSlow, pulled, consumed, run, final, packetAfter, origin, resultCursor⟩ :=
    semantic.run_source_origin_from_entry packet cursor margin last
  exact ⟨bs, off, slow, result, after, finalSlow, pulled, consumed,
    packet, cursor, last, run, final, packetAfter, origin, resultCursor⟩

#print axioms FastFutureReady.run_source_origin_tracked
#print axioms FastFutureReady.run_source_origin_from_entry
#print axioms FastFutureReady.run_source_origin

end Zlib.Inflate.Proofs
