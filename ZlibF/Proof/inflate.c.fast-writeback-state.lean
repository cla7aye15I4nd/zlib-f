import ZlibF.Proof.«inflate.c.fast-view-epilogue-bridge»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The source whole-byte rollback leaves exactly the residual bit count,
for every machine-width input count. -/
theorem fastResidualBits_eq_mod (bits : UInt32) :
    (bits - ((bits >>> 3) <<< 3)).toNat = bits.toNat % 8 := by
  have shifted : ((bits >>> 3) <<< 3).toNat = bits.toNat / 8 * 8 := by
    rw [UInt32.toNat_shiftLeft, bits_whole, Nat.shiftLeft_eq]
    change (bits.toNat / 8 * 8) % 4294967296 = bits.toNat / 8 * 8
    exact Nat.mod_eq_of_lt (by have := UInt32.toNat_lt bits; omega)
  rw [u32_toNat_sub (by rw [shifted]; omega), shifted]
  omega

/-- The exact stream/state records written by the fast suffix retain
`Good` and establish a normalized, sub-byte bit buffer. -/
theorem fastWriteback_normalized_good {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s)
    (l : Zlib.Inffast.L) (input output : BPtr) (ai ao : UInt32) :
    let bits := l.bits - ((l.bits >>> 3) <<< 3)
    let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
    let z' := { z with next_in := input, next_out := output, avail_in := ai, avail_out := ao }
    let s' := { s with hold, bits }
    Good (setI (r.put h z') zs s') r zs z' s' ∧
      bits.toNat < 8 ∧ hold.toNat < 2 ^ bits.toNat := by
  dsimp only
  have bits := fastResidualBits_eq_mod l.bits
  have small : (l.bits - ((l.bits >>> 3) <<< 3)).toNat < 8 := by omega
  refine ⟨good.setZI rfl good.live.zalloc good.live.zfree rfl good.live.mode ?_,
    small, normalized_hold_lt _ _ (by omega)⟩
  have win := good.inv.win
  refine ⟨good.inv.wf, ⟨win.wbits, win.block, win.nullws, win.ws, win.hv, win.wn, win.eq⟩,
    good.inv.reqbits, ?_, good.inv.ptr⟩
  change (l.bits - ((l.bits >>> 3) <<< 3)).toNat ≤ 39
  omega

#print axioms fastWriteback_normalized_good
end Zlib.Inflate.Proofs
