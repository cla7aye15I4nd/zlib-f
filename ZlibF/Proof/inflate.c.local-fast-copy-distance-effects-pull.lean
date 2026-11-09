import ZlibF.Proof.«inflate.c.local-fast-copy-distance-effects-common»
import ZlibF.Proof.«inflate.c.local-fast-parser-pull»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The exact register expressions returned by a guarded input pull
transport already established suffix metadata without changing its heap. -/
theorem FastExecEffect.pull_prefix
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow middleSlow : IL} {dest : BRef} {start : Nat} {byte : UInt8} {next : BPtr}
    {initial middle result : Zlib.Inffast.L} {maxPulls maxMade : Nat}
    (effect : FastExecEffect h after r zs z s middleSlow dest start middle result maxPulls maxMade)
    (cursor : initial.in_ = slow.next) (bits : initial.bits = slow.bits)
    (small : slow.bits.toNat ≤ 22)
    (nextEq : next = inputAdvance slow.next 1)
    (slowEq : middleSlow = pulled slow byte next)
    (fastEq : middle = Zlib.Inffast.Proofs.pullL initial byte next) :
    FastExecEffect h after r zs z s slow dest start initial result (1 + maxPulls) maxMade := by
  have count : middle.bits.toNat = initial.bits.toNat + 8 := by
    rw [fastEq]
    apply Zlib.Inffast.Proofs.pullL_bits
    rw [bits]
    omega
  apply effect.prefix (pulled := 1)
  · rw [slowEq]; rfl
  · rw [slowEq]; rfl
  · rw [fastEq]; rfl
  · rw [fastEq]
    change next = inputAdvance initial.in_ 1
    rw [cursor]
    exact nextEq
  · omega
  · rw [bits] at count
    have thirty : 30 ≤ max initial.bits.toNat 30 := Nat.le_max_right _ _
    omega
  · omega
  · omega

theorem FastExecEffect.widen
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {slow : IL} {dest : BRef} {start : Nat} {initial result : Zlib.Inffast.L}
    {pulls pullsNext made madeNext : Nat}
    (effect : FastExecEffect h after r zs z s slow dest start initial result pulls made)
    (pullBound : pulls ≤ pullsNext) (madeBound : made ≤ madeNext) :
    FastExecEffect h after r zs z s slow dest start initial result pullsNext madeNext := by
  exact effect.prefix (pulled := 0) rfl rfl rfl (inputAdvance_zero _).symm
    (by omega) (Nat.le_max_left _ _) (by omega) madeBound

#print axioms FastExecEffect.widen
#print axioms FastExecEffect.pull_prefix
end Zlib.Inflate.Local
