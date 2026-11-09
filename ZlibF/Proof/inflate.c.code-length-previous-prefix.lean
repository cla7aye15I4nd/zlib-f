import ZlibF.Proof.«inflate.c.code-length-repeat-outcome»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- A completed actual NEEDBITS/drop prefix consumes exactly the code's
bits and retains the requested extra bits. A waiting prefix cannot satisfy
this normal execution observation. -/
theorem clNeedDrop_stream_of_run {h : Heap} {l regs : IL} {bs : List UInt8}
    (B : BitInv h l bs) (here : Code) (extra : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (actual : runX (clNeedDrop here extra) l h = .ok ((.ok (), regs), h)) :
    ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop here.bits.toNat ∧ extra.toNat ≤ regs.bits.toNat := by
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, prepared, used, run, bound, inv, sameStream, _count, _shape, _budget,
    _identity, enough, _same, _short, _cursor⟩ :=
    NEEDBITS_run_cursor B (here.bits.toUInt32 + extra) (by rw [total]; omega)
  unfold clNeedDrop at actual
  rw [runX_bind, run] at actual
  cases result with
  | error exit => cases actual
  | ok done =>
    cases done
    have available := enough rfl
    rw [total] at available
    have small : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    obtain ⟨afterInv, afterStream, afterCount⟩ := DROPBITS_inv inv here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; omega) small
    change runX (DROPBITS here.bits.toUInt32) prepared h = .ok ((.ok (), regs), h) at actual
    rw [DROPBITS_run prepared h here.bits.toUInt32 small] at actual
    cases actual
    refine ⟨used, bound, afterInv, ?_, ?_⟩
    · simpa only [UInt8.toNat_toUInt32, sameStream] using afterStream
    · rw [afterCount, UInt8.toNat_toUInt32]
      omega

#print axioms clNeedDrop_stream_of_run
end Zlib.Inflate.Proofs
