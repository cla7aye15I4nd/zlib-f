import ZlibF.Proof.«infback.c.safety-lookup2»
import ZlibF.Proof.«inflate.c.meaning-lookup»
import ZlibF.Proof.«inflate.c.meaning-fixed-tables»

/-!
# infback.c: a symbol read leaves fewer than 8 bits

`inflate_fast` assumes `state->bits < 8` on entry; `infback.c` takes the fast path without
checking it, so the proof shows that a round of the dispatch starts with fewer than 8 bits held.
The lookups pull a byte only while the entry the held bits select needs more bits. For a table
with prefix-code query stability (`StableQuery`, `PrefixQuery`), the symbol finally read then
consumes more bits than were held before the last byte (`consumed_gt`): fewer than 8 bits are
left once the symbol is dropped.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics (tableRead)
open Zlib.Inftrees.Spec.DecodeTableStability (StableQuery)
open Zlib.Inftrees.Proofs (PrefixQuery)
open Zlib.Inflate.Proofs.MeaningLookup (padded_natBits readBits_natBits_prefix)
set_option autoImplicit false

/-- A query of `B` bits `H` on a table with the decode invariant consumes at least the bits of the
root entry they select. -/
theorem tableRead_ge {type : UInt32} {ca : Array Code} {off R used : Nat} {lens : List Nat}
    (inv : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca off R used lens) {B H : Nat} (lt : H < 2 ^ B)
    {e : Code} {c : Nat}
    (read : tableRead type ca off R (Zlib.Inftrees.Spec.DecodeShort.padded (natBits B H)) = some (e, c)) :
    (ca.getD (off + H % 2 ^ R) default).bits.toNat ≤ c := by
  obtain ⟨-, R15, room, -⟩ := inv.rootTable
  have idx : H % 2 ^ R < 2 ^ R := Nat.mod_lt _ (Nat.two_pow_pos R)
  have inside : off + H % 2 ^ R < ca.size := by omega
  have get : ca[off + H % 2 ^ R]? = some (ca.getD (off + H % 2 ^ R) default) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside]; rfl
  cases hl : Zlib.Inftrees.Spec.Subtable.IsLink type (ca.getD (off + H % 2 ^ R) default) with
  | false =>
    rw [Zlib.Inflate.Proofs.MeaningLookup.tableRead_root lt R15 inside hl] at read
    injection read with read
    injection read with _ e2
    omega
  | true =>
    obtain ⟨-, safe⟩ := inv.subtables _ _ idx get hl
    obtain ⟨-, -, width, cap, -⟩ := safe
    have sub := ZlibF.Math.InflateLookup.slice_lt H (ca.getD (off + H % 2 ^ R) default).bits.toNat
      (ca.getD (off + H % 2 ^ R) default).op.toNat
    rw [Zlib.Inflate.Proofs.MeaningLookup.tableRead_link lt R15 inside hl width (by
      unfold Zlib.Inflate.Proofs.MeaningLookup.subLookupIndexNat; omega)] at read
    injection read with read
    injection read with _ e2
    omega

/-- **After the last pull, the symbol consumes more than the bits held before it.** If the query
of `bp` bits `hp` needs more than `bp` bits, every query that extends those bits and fits the
`B` bits held consumes more than `bp`. -/
theorem consumed_gt {type : UInt32} {ca : Array Code} {off R : Nat}
    (stable : StableQuery type ca off R) (pfx : PrefixQuery type ca off R)
    {bp hp B H : Nat} (bpB : bp ≤ B) (keep : H % 2 ^ bp = hp % 2 ^ bp)
    (needs : ∀ e c, tableRead type ca off R (Zlib.Inftrees.Spec.DecodeShort.padded (natBits bp hp)) =
      some (e, c) → bp < c)
    {e : Code} {c : Nat}
    (read : tableRead type ca off R (Zlib.Inftrees.Spec.DecodeShort.padded (natBits B H)) = some (e, c))
    (fits : c ≤ B) : bp < c := by
  apply Nat.lt_of_not_le
  intro hc
  have r1 := pfx (natBits B H) e c read (by rw [natBits_length]; exact fits)
  rw [natBits_take B H c fits] at r1
  have r2 := stable (natBits c H) e c r1 (by rw [natBits_length]; exact Nat.le_refl _)
    (natBits (bp - c) (H / 2 ^ c))
  rw [← natBits_add, show c + (bp - c) = bp by omega, ← natBits_mod bp H, keep, natBits_mod] at r2
  have := needs e c r2
  omega

end Zlib.Infback.Safety
