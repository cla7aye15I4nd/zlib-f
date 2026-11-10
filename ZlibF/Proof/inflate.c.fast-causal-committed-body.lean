import ZlibF.Proof.«inflate.c.fast-arbitrary-body-causal»
import ZlibF.Math.InflateCommittedTokens
import ZlibF.Proof.«inflate.c.token-retained-history-transport»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open ZlibF.Math.LZ77Copy ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false

/-- One actual arbitrary-input fast body advances the original committed
Symbols context, or reconstructs it at EOB, or really enters BAD. The
retained physical dictionary is expanded to the original logical history.
Every accepted event retains the exact finite consumed word and raw cursor. -/
theorem FastLoopReady.body_committed
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L} {L D : List Nat}
    {dict past start current : List UInt8} {word : List Bool}
    (ready : FastLoopReady ctx h q)
    (lmeaning : ∃ used, Inv LENS ctx.codes ctx.baseOff ctx.rootWidth used L)
    (lstable : StableQuery LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (lflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (dmeaning : ∃ used, Inv DISTS ctx.distCodes ctx.distOff ctx.distWidth used D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (saved : Array UInt8) (woff : Nat)
    (windowData : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + ctx.c.wsize.toNat ≤ saved.size)
    (dictionary : MatchHistory.saved saved ctx.c.wsize.toNat ctx.c.wnext.toNat ctx.c.whave.toNat woff =
      (dict ++ past).drop ((dict ++ past).length - 32768))
    (dictCount : ((dict ++ past).drop ((dict ++ past).length - 32768)).length = ctx.c.whave.toNat)
    (historyView : ∀ j output, q.out = .ref ctx.dest j → Space.get h ctx.dest = some output →
      writtenBytes output j (j - ctx.bg) = current)
    (committed : Committed L D dict start word (past ++ current)) :
    ∃ slow bs output j used result after finalSlow array,
      FastInputPacket h slow bs q ∧ q.out = .ref ctx.dest j ∧
      used ≤ 7 ∧ used ≤ bs.length ∧ result.in_ = inputAdvance q.in_ used ∧
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      FastInputPacket after finalSlow (bs.drop used) result ∧
      DispatchBuffers after ctx.r finalSlow (bs.drop used) ∧ Space.get after ctx.dest = some array ∧
      ((∃ made consumed, made ≤ 258 ∧ after = Space.put h ctx.dest array ∧
          result.out = .ref ctx.dest (j + made) ∧ DefaultStateJ after ctx.r ctx.zs ctx.z ctx.s ∧
          natBits q.bits.toNat q.hold.toNat ++ bytesBits (bs.take used) =
            consumed ++ natBits result.bits.toNat result.hold.toNat ∧
          Committed L D dict start (word ++ consumed)
            (past ++ writtenBytes array (j + made) ((j - ctx.bg) + made))) ∨
       (after = setI h ctx.zs {ctx.s with mode := TYPE} ∧ result.broke = true ∧
          result.out = .ref ctx.dest j ∧ array = output ∧
          ∃ consumed, natBits q.bits.toNat q.hold.toNat ++ bytesBits (bs.take used) =
              consumed ++ natBits result.bits.toNat result.hold.toNat ∧
            Symbols L D dict start (word ++ consumed) [] (past ++ current)) ∨
       (∃ i, after = badHeap h ctx.r ctx.zs ctx.z ctx.s i ∧ result.broke = true ∧
          result.out = .ref ctx.dest j ∧ array = output ∧
          DefaultStateJ after ctx.r ctx.zs {ctx.z with msg := .ref (.str i) 0} {ctx.s with mode := BAD})) := by
  obtain ⟨slow, bs, output, _off, j, packet, _buffers, _next, _put, out, get, body⟩ :=
    FastArbitraryBody.ready_body_arbitrary_causal ready lmeaning lstable lflags dmeaning dflags
      saved woff windowData dictionary dictCount
  have history := historyView j output out get
  obtain ⟨used, result, after, finalSlow, array, usedBound, rawBound, cursor, actual,
    finalPacket, finalBuffers, finalGet, event⟩ := body
  refine ⟨slow, bs, output, j, used, result, after, finalSlow, array, packet, out,
    usedBound, rawBound, cursor, actual, finalPacket, finalBuffers, finalGet, ?_⟩
  rcases event with ⟨made, madeBound, heap, resultOut, currentJ, token⟩ | eob | bad
  · have original := FunctionalEpoch.token_expand_retained_context token
    rw [history] at original
    obtain ⟨consumed, source, grammar⟩ := committed.advance
      (by obtain ⟨_, inv⟩ := lmeaning; exact inv.acceptable)
      (by obtain ⟨_, inv⟩ := dmeaning; exact inv.acceptable) original
    left
    refine ⟨made, consumed, madeBound, heap, resultOut, currentJ, ?_, grammar⟩
    simpa only [← packet.bits, ← packet.hold, ← finalPacket.bits, ← finalPacket.hold] using source
  · obtain ⟨heap, broke, resultOut, sameArray, _currentJ, token⟩ := eob
    have original := FunctionalEpoch.token_expand_retained_context token
    rw [history] at original
    obtain ⟨consumed, source, _same, grammar⟩ := committed.finish
      (by obtain ⟨_, inv⟩ := lmeaning; exact inv.acceptable)
      (by obtain ⟨_, inv⟩ := dmeaning; exact inv.acceptable) original
    right; left
    refine ⟨heap, broke, resultOut, sameArray, consumed, ?_, grammar⟩
    simpa only [← packet.bits, ← packet.hold, ← finalPacket.bits, ← finalPacket.hold] using source
  · exact Or.inr (Or.inr bad)

end Zlib.Inflate.Proofs
