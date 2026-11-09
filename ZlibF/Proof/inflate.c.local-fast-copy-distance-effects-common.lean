import ZlibF.Proof.«inflate.c.local-fast-effect»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Transport established suffix metadata through an observed register-only
prefix. The two bit bounds account for input pulls and the loop's held-bit
limit separately. No execution or callee contract is assumed here. -/
theorem FastExecEffect.prefix
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow middleSlow : IL} {dest : BRef} {start : Nat}
    {initial middle result : Zlib.Inffast.L} {pulled suffixPulls maxPulls suffixMade maxMade : Nat}
    (effect : FastExecEffect h after r zs z s middleSlow dest start middle result suffixPulls suffixMade)
    (put : middleSlow.put = slow.put) (left : middleSlow.left = slow.left)
    (broke : middle.broke = initial.broke)
    (cursor : middle.in_ = inputAdvance initial.in_ pulled)
    (budget : middle.bits.toNat ≤ initial.bits.toNat + 8 * pulled)
    (held : middle.bits.toNat ≤ max initial.bits.toNat 30)
    (pulls : pulled + suffixPulls ≤ maxPulls) (made : suffixMade ≤ maxMade) :
    FastExecEffect h after r zs z s slow dest start initial result maxPulls maxMade := by
  constructor
  · rcases effect.heap with ⟨array, heapEq, frame, same⟩ | bad | endBlock
    · exact Or.inl ⟨array, heapEq, by simpa only [put, left] using frame, same.trans broke⟩
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr endBlock)
  · obtain ⟨finish, pointer, lower, upper⟩ := effect.output
    exact ⟨finish, pointer, lower, by omega⟩
  · exact effect.progress
  · obtain ⟨used, bound, pointer, bits⟩ := effect.input
    refine ⟨pulled + used, by omega, ?_, by omega⟩
    rw [pointer, cursor, inputAdvance_add]
  · intro notBroken
    have suffix := effect.held notBroken
    have thirty : 30 ≤ max initial.bits.toNat 30 := Nat.le_max_right _ _
    have next : max middle.bits.toNat 30 ≤ max initial.bits.toNat 30 := by omega
    omega

#print axioms FastExecEffect.prefix
end Zlib.Inflate.Local
