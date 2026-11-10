import ZlibF.Proof.«inflate.c.prime-default-state»
import ZlibF.Proof.«workspace-inflate.c.reset-default-state»
import ZlibF.Proof.«public-inflate-prime»
import ZlibF.Math.«bit-buffer»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual signed long-width mask has fewer than the requested bits,
for every accepted positive count and every signed value. -/
theorem primeBits_bound (bits value : Int32) (positive : 0 < bits.toInt) (small : bits.toInt ≤ 16) :
    (primeBits bits value).toNat < 2 ^ bits.toInt.toNat := by
  have mask := ZlibF.Spec.Public.InflatePrimeProof.primeBits_public bits value positive small
  change primeBits bits value = _ at mask
  have count : bits.toUInt32.toNat = bits.toInt.toNat := i2u_toNat (by omega)
  have countBound : bits.toUInt32.toNat < 32 := by rw [count]; omega
  rw [mask, UInt32.toNat_toUInt64, UInt32.toNat_and, mask_toNat _ countBound, count]
  have le : value.toUInt32.toNat &&& (2 ^ bits.toInt.toNat - 1) ≤ 2 ^ bits.toInt.toNat - 1 := Nat.and_le_right
  have power := Nat.two_pow_pos bits.toInt.toNat
  omega


/-- A real private bit-buffer update retains every other default invariant
clause. Its held-bit bound is proved separately from the source arithmetic. -/
theorem DefaultStateJ.set_bits {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (hold : UInt64) (bits : UInt32)
    (good : Good (setI h zs { s with hold := hold, bits := bits }) r zs z { s with hold := hold, bits := bits })
    (held : hold.toNat < 2 ^ bits.toNat) :
    DefaultStateJ (setI h zs { s with hold := hold, bits := bits }) r zs z { s with hold := hold, bits := bits } := by
  obtain ⟨tables, lengths⟩ := table_clauses_set_bits invariant.good.live.hs hold bits invariant.tables invariant.lengths
  exact ⟨⟨good, tables, ⟨invariant.pending.sane, invariant.pending.lenext,
    invariant.pending.dist, invariant.pending.distext, invariant.pending.matching⟩, lengths, invariant.headerLengths, held,
    invariant.window, invariant.wrapper, invariant.header, invariant.modes, invariant.trailer,
    invariant.globals, invariant.platform.with_istates _⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩


end Zlib.Inflate.Proofs
