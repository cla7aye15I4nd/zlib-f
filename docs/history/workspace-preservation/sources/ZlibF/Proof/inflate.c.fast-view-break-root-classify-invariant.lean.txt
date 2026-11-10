import ZlibF.Proof.«inflate.c.fast-view-break-refill-invalid-body-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Root code classes that continue decoding after the selected entry:
a second-level link, a literal, or a length base. -/
def FastRootContinues (codes : Array Code) (baseOff : Nat)
    (c : Zlib.Inffast.Ctx) (q : Zlib.Inffast.L) : Prop :=
  let index := baseOff + (q.hold &&& c.lmask.toUInt64).toNat
  let entry := codes.getD index default
  LenLink entry ∨ entry.op = 0 ∨ entry.op &&& 16 ≠ 0

/-- A checked root table exhaustively selects an end code, an invalid
code, or a decoding continuation. These are case facts about the actual
post-refill register, not restrictions on caller input. -/
theorem fast_root_cases
    {codes : Array Code} {baseOff rootWidth : Nat}
    {c : Zlib.Inffast.Ctx} {q : Zlib.Inffast.L}
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1) :
    FastRootEnd codes baseOff c q ∨
    FastRootInvalid codes baseOff c q ∨
    FastRootContinues codes baseOff c q := by
  let rootSlice := (q.hold &&& c.lmask.toUInt64).toNat
  have sliceEq : rootSlice = q.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have root : rootSlice < 2 ^ rootWidth := by
    rw [sliceEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  obtain ⟨bound, classes⟩ :=
    len_table_root_source_cases safe root
  rcases classes with ⟨link, _⟩ |
    ⟨_, width, literal | base | terminal | invalid⟩
  · exact Or.inr (Or.inr (Or.inl link))
  · exact Or.inr (Or.inr (Or.inr (Or.inl literal)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr base.1)))
  · exact Or.inl ⟨bound, width, terminal.1,
      terminal.2.1, terminal.2.2.1,
      terminal.2.2.2⟩
  · exact Or.inr (Or.inl ⟨bound, width, invalid.1,
      invalid.2.1, invalid.2.2.1,
      invalid.2.2.2⟩)

end Zlib.Inflate.Proofs
