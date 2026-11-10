import ZlibF.Proof.«inflate.c.fast-causal-loop-ready»

namespace ZlibF.Math.InflateFastSource
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A source-generated finite token word advances Origin. No complete
future parse, expected output, or scalar bit-count guess is needed. -/
theorem Origin.advance_word
    {initialHold initialBits hold bits pulled consumed nextHold nextBits used : Nat}
    {input : List UInt8} {word : List Bool}
    (origin : Origin initialHold initialBits input hold bits pulled consumed)
    (usedBound : used ≤ (input.drop pulled).length)
    (source : natBits bits hold ++ bytesBits ((input.drop pulled).take used) =
      word ++ natBits nextBits nextHold) :
    Origin initialHold initialBits input nextHold nextBits (pulled + used) (consumed + word.length) := by
  have split : natBits bits hold ++ bytesBits (input.drop pulled) =
      word ++ (natBits nextBits nextHold ++ bytesBits ((input.drop pulled).drop used)) := by
    calc
      _ = (natBits bits hold ++ bytesBits ((input.drop pulled).take used)) ++
          bytesBits ((input.drop pulled).drop used) := by
        rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
      _ = _ := by rw [source, List.append_assoc]
  apply origin.advance usedBound
  · rw [split, List.length_append]
    omega
  · rw [split, List.drop_left]

end ZlibF.Math.InflateFastSource

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Math.InflateFastSource
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- Package actual per-body source/cursor frames into the next tracked
origin. All segment observations are supplied by the real body producer. -/
def Observation.advance_word
    {ctx : FastLoopContext} {p : Parameters ctx} {h after : Heap} {q result : Zlib.Inffast.L}
    (before : Observation p h q) {bs : List UInt8} {used : Nat} {finalSlow : IL}
    {consumed : List Bool} (history : List UInt8)
    (rawEq : bs = p.input.drop before.pulled)
    (rawBound : used ≤ bs.length)
    (cursor : result.in_ = inputAdvance q.in_ used)
    (packet : FastInputPacket after finalSlow (bs.drop used) result)
    (source : natBits q.bits.toNat q.hold.toNat ++ bytesBits (bs.take used) =
      consumed ++ natBits result.bits.toNat result.hold.toNat)
    (observed : ∀ j output, result.out = .ref ctx.dest j → Space.get after ctx.dest = some output →
      writtenBytes output j (j - ctx.bg) = history)
    (windowData : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window p.woff ∧
      Space.get after window = some p.saved ∧ p.woff + ctx.c.wsize.toNat ≤ p.saved.size) :
    Observation p after result := by
  refine {
    pulled := before.pulled + used
    word := before.word ++ consumed
    history := history
    slow := finalSlow
    packet := ?_
    origin := ?_
    physical := ?_
    historyView := observed
    windowData := windowData }
  · simpa only [rawEq, List.drop_drop] using packet
  · have next := before.origin.advance_word (by simpa only [← rawEq] using rawBound)
      (by simpa only [← rawEq] using source)
    simpa only [List.length_append] using next
  · rw [cursor, before.physical, inputAdvance_add]

end Zlib.Inflate.Proofs.FastCommittedLoop
