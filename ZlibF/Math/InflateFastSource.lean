import ZlibF.Proof.«inflate.c.main.bits»

namespace ZlibF.Math.InflateFastSource
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Exact remaining source during one call, with the actual count of
pulled bytes. No valid token or valid unread suffix is assumed. -/
structure Origin (initialHold initialBits : Nat) (input : List UInt8)
    (hold bits pulled consumed : Nat) : Prop where
  pulledBound : pulled ≤ input.length
  consumedBound : consumed ≤ initialBits + 8 * input.length
  source : natBits bits hold ++ bytesBits (input.drop pulled) =
    (natBits initialBits initialHold ++ bytesBits input).drop consumed

theorem Origin.initial (initialHold initialBits : Nat) (input : List UInt8) :
    Origin initialHold initialBits input initialHold initialBits 0 0 := by
  exact ⟨by omega, by omega, by simp⟩

/-- Physical byte counts and an exact source suffix determine the bit
budget. Repeated byte values cannot alter this length equation. -/
theorem Origin.accounting
    {initialHold initialBits hold bits pulled consumed : Nat} {input : List UInt8}
    (origin : Origin initialHold initialBits input hold bits pulled consumed) :
    consumed + bits = initialBits + 8 * pulled := by
  have lengths := congrArg List.length origin.source
  simp only [List.length_append, List.length_drop, natBits_length, bytesBits_length] at lengths
  have pulledBound := origin.pulledBound
  have consumedBound := origin.consumedBound
  omega

/-- Exact body-source transport composes over actual pulled bytes and
consumed bits. It does not assert existence of any future token. -/
theorem Origin.advance
    {initialHold initialBits hold bits pulled consumed nextHold nextBits used taken : Nat}
    {input : List UInt8}
    (origin : Origin initialHold initialBits input hold bits pulled consumed)
    (usedBound : used ≤ (input.drop pulled).length)
    (takenBound : taken ≤ (natBits bits hold ++ bytesBits (input.drop pulled)).length)
    (step : natBits nextBits nextHold ++ bytesBits ((input.drop pulled).drop used) =
      (natBits bits hold ++ bytesBits (input.drop pulled)).drop taken) :
    Origin initialHold initialBits input nextHold nextBits (pulled + used) (consumed + taken) := by
  constructor
  · simp only [List.length_drop] at usedBound
    have prior := origin.pulledBound
    omega
  · have sizes := congrArg List.length origin.source
    simp only [List.length_append, List.length_drop, natBits_length, bytesBits_length] at sizes
    simp only [List.length_append, List.length_drop, natBits_length, bytesBits_length] at takenBound
    have prior := origin.consumedBound
    omega
  · rw [List.drop_drop] at step
    rw [step, origin.source, List.drop_drop]

/-- A drop trace can always be represented by its actual bounded source
consumption, even if a coarser operational theorem exported a loose bound. -/
theorem Origin.advance_drop
    {initialHold initialBits hold bits pulled consumed nextHold nextBits used taken : Nat}
    {input : List UInt8}
    (origin : Origin initialHold initialBits input hold bits pulled consumed)
    (usedBound : used ≤ (input.drop pulled).length)
    (step : natBits nextBits nextHold ++ bytesBits ((input.drop pulled).drop used) =
      (natBits bits hold ++ bytesBits (input.drop pulled)).drop taken) :
    Origin initialHold initialBits input nextHold nextBits (pulled + used)
      (consumed + min taken (natBits bits hold ++ bytesBits (input.drop pulled)).length) := by
  apply origin.advance usedBound (Nat.min_le_right _ _)
  by_cases fits : taken ≤ (natBits bits hold ++ bytesBits (input.drop pulled)).length
  · simpa only [Nat.min_eq_left fits] using step
  · have whole : (natBits bits hold ++ bytesBits (input.drop pulled)).length ≤ taken := by omega
    simpa only [Nat.min_eq_right whole, List.drop_length,
      List.drop_eq_nil_of_le whole] using step

/-- Returning whole unused bytes preserves every remaining bit. The
returned bytes are identified by exact source origin, not just a bound. -/
theorem Origin.rollback
    {initialHold initialBits hold bits pulled consumed : Nat} {input : List UInt8}
    (origin : Origin initialHold initialBits input hold bits pulled consumed)
    (smallEntry : initialBits < 8) :
    bits / 8 ≤ pulled ∧
      (natBits (bits % 8) (hold % 2 ^ (bits % 8)) ++
        bytesBits (input.drop (pulled - bits / 8))) =
      natBits bits hold ++ bytesBits (input.drop pulled) ∧
      Origin initialHold initialBits input (hold % 2 ^ (bits % 8)) (bits % 8)
        (pulled - bits / 8) consumed := by
  let returned := bits / 8
  let residual := bits % 8
  have decomposition : residual + 8 * returned = bits := Nat.mod_add_div bits 8
  have residualBound : residual < 8 := Nat.mod_lt _ (by decide)
  have accounting := origin.accounting
  have rollbackBound : returned ≤ pulled := by omega
  have residualAvailable : residual ≤ bits := by omega
  have nextAccounting : consumed + residual = initialBits + 8 * (pulled - returned) := by omega
  have originDrop : (natBits initialBits initialHold ++ bytesBits input).drop
      (consumed + residual) = bytesBits (input.drop (pulled - returned)) := by
    rw [nextAccounting, List.drop_append]
    have removed : (natBits initialBits initialHold).drop
        (initialBits + 8 * (pulled - returned)) = [] :=
      List.drop_eq_nil_of_le (by rw [natBits_length]; omega)
    rw [removed, List.nil_append, natBits_length, Nat.add_sub_cancel_left, bytesBits_drop]
  have tail : (natBits bits hold ++ bytesBits (input.drop pulled)).drop residual =
      bytesBits (input.drop (pulled - returned)) := by
    rw [origin.source, List.drop_drop]
    exact originDrop
  have head : (natBits bits hold ++ bytesBits (input.drop pulled)).take residual =
      natBits residual hold := by
    rw [List.take_append_of_le_length (by rw [natBits_length]; exact residualAvailable)]
    exact natBits_take bits hold residual residualAvailable
  have same : natBits residual (hold % 2 ^ residual) ++
      bytesBits (input.drop (pulled - returned)) =
      natBits bits hold ++ bytesBits (input.drop pulled) := by
    rw [natBits_mod, ← head, ← tail, List.take_append_drop]
  refine ⟨rollbackBound, same, ?_⟩
  exact ⟨by have previous := origin.pulledBound; omega,
    origin.consumedBound, same.trans origin.source⟩

#print axioms Origin.initial
#print axioms Origin.accounting
#print axioms Origin.advance
#print axioms Origin.advance_drop
#print axioms Origin.rollback
end ZlibF.Math.InflateFastSource
