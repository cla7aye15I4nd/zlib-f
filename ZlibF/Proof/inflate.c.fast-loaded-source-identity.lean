import ZlibF.Math.InflateFastSource
import ZlibF.Proof.«inflate.c.fast-entry»

namespace ZlibF.Math.InflateFastSource
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The bytes retained as consumed after rollback contain exactly the
committed bits and the residual held word. Unconsumed caller bytes are
absent, so this equation remains usable across a later buffer replacement. -/
theorem Origin.rollback_consumed_prefix
    {initialHold initialBits hold bits pulled consumed : Nat} {input : List UInt8}
    (origin : Origin initialHold initialBits input hold bits pulled consumed)
    (smallEntry : initialBits < 8) :
    ∃ committed : List Bool, committed.length = consumed ∧
      natBits initialBits initialHold ++ bytesBits (input.take (pulled - bits / 8)) =
        committed ++ natBits (bits % 8) (hold % 2 ^ (bits % 8)) := by
  have rolled := (origin.rollback smallEntry).2.2
  let seen := natBits initialBits initialHold ++ bytesBits (input.take (pulled - bits / 8))
  have size : seen.length = initialBits + 8 * (pulled - bits / 8) := by
    simp only [seen, List.length_append, natBits_length, bytesBits_length, List.length_take,
      Nat.min_eq_left rolled.pulledBound]
  have fits : consumed ≤ seen.length := by
    rw [size]
    have account := rolled.accounting
    omega
  have split : natBits initialBits initialHold ++ bytesBits input =
      seen ++ bytesBits (input.drop (pulled - bits / 8)) := by
    dsimp only [seen]
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
  have remaining : seen.drop consumed = natBits (bits % 8) (hold % 2 ^ (bits % 8)) := by
    have source := rolled.source
    rw [split, List.drop_append_of_le_length fits] at source
    exact List.append_cancel_right source.symm
  refine ⟨seen.take consumed, by simp only [List.length_take, Nat.min_eq_left fits], ?_⟩
  change seen = seen.take consumed ++ natBits (bits % 8) (hold % 2 ^ (bits % 8))
  rw [← remaining, List.take_append_drop]

#print axioms Origin.rollback_consumed_prefix
end ZlibF.Math.InflateFastSource

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
open ZlibF.Math.InflateFastSource
set_option autoImplicit false

/-- The source-origin result and actual suffix scalar equations identify
the post-LOAD stream with the same exact token residual. Physical input
accounting determines the returned raw-byte count, including rollback. -/
theorem FastInputPacket.loaded_source_identity
    {h : Heap} {before loaded : IL} {q : Zlib.Inffast.L}
    {input : List UInt8} {initialHold initialBits pulled consumed used : Nat}
    (packet : FastInputPacket h before (input.drop pulled) q)
    (origin : Origin initialHold initialBits input q.hold.toNat q.bits.toNat pulled consumed)
    (smallEntry : initialBits < 8)
    (loadedBits : loaded.bits.toNat = q.bits.toNat % 8)
    (loadedHold : loaded.hold.toNat = q.hold.toNat % 2 ^ (q.bits.toNat % 8))
    (accounting : loaded.have_.toNat + used = input.length)
    (inputRemaining : loaded.have_.toNat = input.length - (pulled - q.bits.toNat / 8)) :
    used = pulled - q.bits.toNat / 8 ∧
      stream loaded (input.drop used) = stream before (input.drop pulled) ∧
      ∃ committed : List Bool, committed.length = consumed ∧
        natBits initialBits initialHold ++ bytesBits (input.take used) =
          committed ++ natBits loaded.bits.toNat loaded.hold.toNat := by
  have rawBound : pulled - q.bits.toNat / 8 ≤ input.length := by
    have prior := origin.pulledBound
    omega
  have count : used = pulled - q.bits.toNat / 8 := by omega
  refine ⟨count, ?_, ?_⟩
  · rw [stream, loadedBits, loadedHold, count]
    have source := (origin.rollback smallEntry).2.1
    simpa only [stream, packet.bits, packet.hold] using source
  · obtain ⟨committed, length, inputEquation⟩ := origin.rollback_consumed_prefix smallEntry
    exact ⟨committed, length, by simpa only [count, loadedBits, loadedHold] using inputEquation⟩

#print axioms FastInputPacket.loaded_source_identity
end Zlib.Inflate.Proofs
