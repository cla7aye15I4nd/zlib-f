import ZlibF.Proof.«inflate.c.fast-causal-loop-rejected-word-interface»
namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open ZlibF.Math.LZ77Copy ZlibF.Math.InflateCommittedTokens ZlibF.Math.InflateFastSource
set_option autoImplicit false
set_option maxRecDepth 8192

/-- A real fast body preserves its existing accepted/EOB source packets,
or records the last rejected word after the already committed prefix.
The source-derived table-take properties are fixed internal data facts. -/
theorem WordReady.body_with_rejected_word
    {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    (wordState : WordReady p h q)
    (dstable : StableQuery DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (ltake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (dtake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake DISTS ctx.distCodes ctx.distOff ctx.distWidth) :
    ∃ result after, C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      WordRejectedOutcome p after result := by
  let state := wordState.state
  rcases state.safety with ⟨slow, bs, output, off, j, packet, invariant, buffers,
    codesGet, distGet, bits, leftEq, _outEq, put, next, last, margin, out,
    get, write, size, current, beginLe, span, guard⟩
  have rawEq := FastLoopSource.align_packet p.rawMargin p.initialLast state.tracked.packet
    state.tracked.origin state.tracked.physical packet next last margin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]; exact ctx.endPtr
  have whave : ctx.c.whave.toNat ≤ ctx.c.wsize.toNat := by
    rw [ctx.whaveEq, ctx.wsizeEq]; exact invariant.good.inv.win.hv
  have wnext : ctx.c.wnext.toNat ≤ ctx.c.wsize.toNat := by
    rw [ctx.wnextEq, ctx.wsizeEq]
    rcases invariant.good.inv.win.wn with valid | ⟨zero, nextZero⟩ <;> omega
  have wsize : ctx.c.wsize.toNat ≤ 32768 := by
    rw [ctx.wsizeEq]
    rcases invariant.good.inv.win.ws with zero | full
    · omega
    · rw [invariant.window] at full
      change ctx.s.wsize.toNat = 32768 at full
      omega
  obtain ⟨lextent, linv⟩ := p.lmeaning
  obtain ⟨dextent, dinv⟩ := p.dmeaning
  obtain ⟨used, result, after, finalSlow, array, _usedBound, rawBound, cursor, actual,
    finalPacket, finalBuffers, finalGet, event⟩ :=
    FastArbitraryBody.fast_body_arbitrary_causal packet buffers margin bits ctx.lcodePtr ctx.lenSafe ctx.lenMask
      invariant codesGet linv p.lflags p.lstable ctx.dcodePtr distGet ctx.distSafe ctx.distMask dinv p.dflags
      ctx.streamPtr ctx.statePtr ctx.mode left avail whave wnext wsize out put ctx.begPtr endPtr get write size
      current beginLe span guard state.tracked.windowData p.dictionary p.dictCount
  have history := state.tracked.historyView j output out get
  refine ⟨result, after, actual, ?_⟩
  rcases event with ⟨made, _madeBound, heap, resultOut, currentJ, token⟩ | eob | bad
  · have original := FunctionalEpoch.token_expand_retained_context token
    rw [history] at original
    obtain ⟨consumed, source, grammar⟩ := state.tracked.committed.advance linv.acceptable dinv.acceptable original
    have heldSource : natBits q.bits.toNat q.hold.toNat ++ bytesBits (bs.take used) =
        consumed ++ natBits result.bits.toNat result.hold.toNat := by
      simpa only [← packet.bits, ← packet.hold, ← finalPacket.bits, ← finalPacket.hold] using source
    have observed : ∀ k a, result.out = .ref ctx.dest k → Space.get after ctx.dest = some a →
        writtenBytes a k (k - ctx.bg) = writtenBytes array (j + made) ((j - ctx.bg) + made) := by
      intro k a pointer getA
      have index : k = j + made := (Ptr.ref.inj (pointer.symm.trans resultOut)).2
      have same : a = array := Option.some.inj (getA.symm.trans finalGet)
      subst k a
      congr 1
      omega
    have window : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window p.woff ∧
        Space.get after window = some p.saved ∧ p.woff + ctx.c.wsize.toNat ≤ p.saved.size := by
      intro nonzero
      obtain ⟨w, different, pointer, getW, bound⟩ := state.tracked.windowData nonzero
      refine ⟨w, different, pointer, ?_, bound⟩
      rw [heap, byte_view_get_put_ne h different]
      exact getW
    let observation := state.tracked.toObservation.advance_word
      (writtenBytes array (j + made) ((j - ctx.bg) + made)) rawEq rawBound cursor finalPacket heldSource observed window
    let tracked : Tracked p after result := {
      toObservation := observation
      committed := by simpa only [observation, Observation.advance_word, List.append_assoc] using grammar }
    left
    refine ⟨tracked, ?_, currentJ⟩
    exact WordSource.advance wordState.source rfl rfl rawEq heldSource
  · obtain ⟨heap, broke, resultOut, sameArray, currentJ, token⟩ := eob
    have original := FunctionalEpoch.token_expand_retained_context token
    rw [history] at original
    obtain ⟨consumed, source, _same, grammar⟩ := state.tracked.committed.finish linv.acceptable dinv.acceptable original
    have heldSource : natBits q.bits.toNat q.hold.toNat ++ bytesBits (bs.take used) =
        consumed ++ natBits result.bits.toNat result.hold.toNat := by
      simpa only [← packet.bits, ← packet.hold, ← finalPacket.bits, ← finalPacket.hold] using source
    have observed : ∀ k a, result.out = .ref ctx.dest k → Space.get after ctx.dest = some a →
        writtenBytes a k (k - ctx.bg) = state.tracked.history := by
      intro k a pointer getA
      have sameOut : result.out = q.out := resultOut.trans out.symm
      rw [sameOut] at pointer
      rw [heap, byte_view_get_setI] at getA
      exact state.tracked.historyView k a pointer getA
    have window : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window p.woff ∧
        Space.get after window = some p.saved ∧ p.woff + ctx.c.wsize.toNat ≤ p.saved.size := by
      intro nonzero
      obtain ⟨w, different, pointer, getW, bound⟩ := state.tracked.windowData nonzero
      refine ⟨w, different, pointer, ?_, bound⟩
      rw [heap, byte_view_get_setI]
      exact getW
    let observation := state.tracked.toObservation.advance_word state.tracked.history
      rawEq rawBound cursor finalPacket heldSource observed window
    let ended : Ended p after result := {
      toObservation := observation
      broke := broke
      state := currentJ
      symbols := by simpa only [observation, Observation.advance_word, List.append_assoc] using grammar }
    right; left
    refine ⟨ended, ?_⟩
    exact WordSource.advance wordState.source rfl rfl rawEq heldSource
  · obtain ⟨message, _heap, _broke, _out, _array, currentBad⟩ := bad
    have classified := FastArbitraryBody.fast_body_nonbad_or_rejected_word packet buffers margin bits
      ctx.lcodePtr ctx.lenSafe ctx.lenMask invariant codesGet linv p.lflags p.lstable ltake
      ctx.dcodePtr distGet ctx.distSafe ctx.distMask dinv p.dflags dstable dtake ctx.mode
      ctx.streamPtr ctx.statePtr left avail whave wnext wsize out put ctx.begPtr endPtr get write size
      current beginLe span guard state.tracked.windowData p.dictionary p.dictCount
    rcases classified with nonBad | badWord
    · obtain ⟨other, otherHeap, otherZ, otherState, sourceRun, good, notBad⟩ := nonBad
      have same := Except.ok.inj (actual.symm.trans sourceRun)
      cases same
      have stateEq : otherState = {ctx.s with mode := BAD} :=
        Option.some.inj (good.live.hs.symm.trans currentBad.good.live.hs)
      exact False.elim (notBad (by rw [stateEq]))
    · have logical := badWord.logical_context
      have history := state.tracked.historyView j output out get
      rw [history] at logical
      obtain ⟨used, rejectedWord, badResult, badHeap, finalSlow, i, _usedBound, rawBound, cursor,
        badRun, _heap, broke, sameOut, finalPacket, finalBuffers, badState, views, credit, rejected⟩ := logical
      have same := Except.ok.inj (actual.symm.trans badRun)
      cases same
      have heldSource : natBits q.bits.toNat q.hold.toNat ++ bytesBits (bs.take used) =
          rejectedWord ++ natBits result.bits.toNat result.hold.toNat := by
        simpa only [← packet.bits, ← packet.hold, ← finalPacket.bits, ← finalPacket.hold] using credit
      have observed : ∀ k a, result.out = .ref ctx.dest k → Space.get after ctx.dest = some a →
          writtenBytes a k (k - ctx.bg) = state.tracked.history := by
        intro k a pointer getA
        have beforeGet : Space.get h ctx.dest = some a := by rw [← views]; exact getA
        rw [sameOut] at pointer
        exact state.tracked.historyView k a pointer beforeGet
      have window : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window p.woff ∧
          Space.get after window = some p.saved ∧ p.woff + ctx.c.wsize.toNat ≤ p.saved.size := by
        intro nonzero
        obtain ⟨w, different, pointer, getW, bound⟩ := state.tracked.windowData nonzero
        exact ⟨w, different, pointer, by rw [views]; exact getW, bound⟩
      let observation := state.tracked.toObservation.advance_word state.tracked.history
        rawEq rawBound cursor finalPacket heldSource observed window
      let rejectedObservation : RejectedObservation p after result := {
        toObservation := observation
        priorWord := state.tracked.word
        badWord := rejectedWord
        wordEq := rfl
        priorCommitted := state.tracked.committed
        rejected := rejected
        broke := broke
        state := ⟨i, badState⟩ }
      refine Or.inr (Or.inr ⟨rejectedObservation, ?_⟩)
      exact WordSource.advance wordState.source rfl rfl rawEq heldSource


#print axioms WordReady.body_with_rejected_word
end Zlib.Inflate.Proofs.FastCommittedLoop
