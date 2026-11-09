import ZlibF.Proof.«inflate.c.code-length-previous-prefix»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- A waiting repeat-16 prefix has not dropped the code word. Refilling
may advance byte pointers, but the real unconsumed bit stream is unchanged. -/
theorem clNeedDrop_wait_stream {h : Heap} {l regs : IL} {bs : List UInt8} {exit : Ex}
    (B : BitInv h l bs) (here : Code) (extra : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (actual : runX (clNeedDrop here extra) l h = .ok ((.error exit, regs), h)) :
    ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs := by
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, prepared, used, run, bound, inv, sameStream, _count, _shape, _budget,
    _identity, _enough, _same, _short, _cursor⟩ :=
    NEEDBITS_run_cursor B (here.bits.toUInt32 + extra) (by rw [total]; omega)
  unfold clNeedDrop at actual
  rw [runX_bind, run] at actual
  cases result with
  | error fault =>
    cases actual
    exact ⟨used, bound, inv, sameStream⟩
  | ok done =>
    cases done
    change runX (DROPBITS here.bits.toUInt32) prepared h = .ok ((.error exit, regs), h) at actual
    rw [DROPBITS_run prepared h here.bits.toUInt32 (by rw [UInt8.toNat_toUInt32]; omega)] at actual
    cases actual

/-- Zero repeats also test the whole code-plus-extra width before dropping
anything. An actual wait therefore preserves the complete real bit stream. -/
theorem clZeroSetup_wait_stream {h : Heap} {l regs : IL} {bs : List UInt8} {exit : Ex}
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (actual : runX (clZeroSetup here extra base) l h = .ok ((.error exit, regs), h)) :
    ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs := by
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, prepared, used, run, bound, inv, sameStream, _count, _shape, _budget,
    _identity, _enough, _same, _short, _cursor⟩ :=
    NEEDBITS_run_cursor B (here.bits.toUInt32 + extra) (by rw [total]; omega)
  unfold clZeroSetup at actual
  rw [runX_bind, run] at actual
  cases result with
  | error fault =>
    cases actual
    exact ⟨used, bound, inv, sameStream⟩
  | ok done =>
    cases done
    have wordSmall : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    have extraSmall : extra.toNat < 32 := by omega
    let dropped := { prepared with hold := prepared.hold >>> here.bits.toUInt32.toUInt64, bits := prepared.bits - here.bits.toUInt32 }
    let bits := dropped.hold.toUInt32 &&& ((1 : UInt32) <<< extra - 1)
    let ready := { dropped with len := 0, copy := base + bits }
    dsimp only at actual
    rw [runX_bind, DROPBITS_run prepared h here.bits.toUInt32 wordSmall] at actual
    dsimp only at actual
    rw [runX_bind, BITS_run dropped h extra extraSmall] at actual
    dsimp only at actual
    rw [runX_bind, runX_modify] at actual
    dsimp only at actual
    rw [DROPBITS_run ready h extra (by omega)] at actual
    cases actual

#print axioms clNeedDrop_wait_stream
#print axioms clZeroSetup_wait_stream
end Zlib.Inflate.Proofs
