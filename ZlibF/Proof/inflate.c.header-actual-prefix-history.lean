import ZlibF.Proof.«inflate.c.header-actual-accepted-prefix»
import ZlibF.Math.HeaderConsumedReplay
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem HeaderSourcePrefix.seed
    {s : InflateState} {l : IL} {bs : List UInt8} {alphabet : List Nat}
    {body r1 r2 r3 : List Bool} {hlit hdist hclen : Nat}
    (first : readBits 5 body = some (hlit, r1)) (second : readBits 5 r1 = some (hdist, r2))
    (third : readBits 4 r2 = some (hclen, r3)) (counts : DynamicCountsOK hlit hdist)
    (lit : s.nlen.toNat = hlit + 257) (dist : s.ndist.toNat = hdist + 1)
    (read : readCodeLenLens (hclen + 4) r3 = some (alphabet, stream l bs))
    (valid : Acceptable .codeLength alphabet) (empty : actualLengthPrefix s = []) :
    ∃ data : HeaderSourcePrefix s l bs alphabet, data.bodyInput = body := by
  refine ⟨⟨body, r1, r2, r3, stream l bs, [], hlit, hdist, hclen, first, second, third, counts, lit, dist, read, valid, rfl, ?_⟩, rfl⟩
  rw [empty]
  exact ZlibF.Math.CodeLengthPrefix.Trace.refl _ _ _

/-- Actual ordinary partial reads compose their causal trace. Empty root
is retained as its separate real zero-prefix case, rather than inventing
an independent code-length parse for that malformed path. -/
theorem HeaderSourcePrefix.advance
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (data : HeaderSourcePrefix s l bs alphabet)
    (observation : CodeReadObservation c h r zs z s l bs alphabet)
    (code : observation.state.mode = CODELENS) :
    ((∀ length ∈ alphabet, length = 0) ∧ actualLengthPrefix observation.state = List.replicate observation.state.«have».toNat 0) ∨
    ∃ next : HeaderSourcePrefix observation.state observation.regs (bs.drop observation.used) alphabet,
      next.bodyInput = data.bodyInput ∧ next.codeInput = data.codeInput := by
  rcases observation.format with empty | ordinary
  · exact Or.inl ⟨empty.2.1, empty.2.2.1⟩
  obtain ⟨consumed, source, trace⟩ := ordinary.1 (by rw [code]; decide)
  obtain ⟨state0, _used0, get0, _bound0, _B0, _shape, _bits, frame, _size, _have, _values, _modes, _done⟩ := observation.full.1
  have stateEq : state0 = observation.state := Option.some.inj (get0.symm.trans observation.origin.good.live.hs)
  have savedLit : observation.state.nlen = s.nlen := by rw [← stateEq, frame]
  have savedDist : observation.state.ndist = s.ndist := by rw [← stateEq, frame]
  refine Or.inr ⟨⟨data.bodyInput, data.r1, data.r2, data.r3, data.codeInput, data.consumed ++ consumed,
    data.hlit, data.hdist, data.hclen, data.first, data.second, data.third, data.counts,
    by rw [savedLit]; exact data.literalCount, by rw [savedDist]; exact data.distanceCount,
    data.alphabetRead, data.acceptable, ?_, ?_⟩, rfl, rfl⟩
  · rw [data.source, source, List.append_assoc]
  · rw [savedLit, savedDist]
    exact data.trace.trans trace

/-- The accumulated header words replay before any new current residual.
This supports genuine caller rebuffering; matching the new held word to
actual received bytes remains the physical cursor ledger's obligation. -/
theorem HeaderSourcePrefix.replay
    {s : InflateState} {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (data : HeaderSourcePrefix s l bs alphabet) :
    ∃ word, data.bodyInput = word ++ stream l bs ∧
      ∀ (regs : IL) (input : List UInt8), ∃ next : HeaderSourcePrefix s regs input alphabet,
        next.bodyInput = word ++ stream regs input ∧ next.consumed = data.consumed := by
  obtain ⟨w1, source1, replay1⟩ := ZlibF.Math.HeaderConsumedReplay.readBits_consumed_word data.first
  obtain ⟨w2, source2, replay2⟩ := ZlibF.Math.HeaderConsumedReplay.readBits_consumed_word data.second
  obtain ⟨w3, source3, replay3⟩ := ZlibF.Math.HeaderConsumedReplay.readBits_consumed_word data.third
  obtain ⟨wa, sourceA, replayA⟩ := ZlibF.Math.HeaderConsumedReplay.readCodeLenLens_consumed_word data.alphabetRead
  let word := w1 ++ w2 ++ w3 ++ wa ++ data.consumed
  refine ⟨word, ?_, ?_⟩
  · rw [source1, source2, source3, sourceA, data.source]
    simp only [word, List.append_assoc]
  · intro regs input
    let codeInput := data.consumed ++ stream regs input
    refine ⟨⟨word ++ stream regs input, w2 ++ w3 ++ wa ++ codeInput, w3 ++ wa ++ codeInput, wa ++ codeInput,
      codeInput, data.consumed, data.hlit, data.hdist, data.hclen, ?_, ?_, ?_, data.counts, data.literalCount,
      data.distanceCount, ?_, data.acceptable, rfl, data.trace⟩, rfl, rfl⟩
    · simpa only [word, codeInput, List.append_assoc] using replay1 (w2 ++ w3 ++ wa ++ codeInput)
    · simpa only [List.append_assoc] using replay2 (w3 ++ wa ++ codeInput)
    · simpa only [List.append_assoc] using replay3 (wa ++ codeInput)
    · exact replayA codeInput

#print axioms HeaderSourcePrefix.seed
#print axioms HeaderSourcePrefix.advance
#print axioms HeaderSourcePrefix.replay
end Zlib.Inflate.Proofs.ActualHeader
