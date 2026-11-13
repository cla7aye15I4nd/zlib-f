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

theorem mod_mod_of_le {a b H : Nat} (le : a ≤ b) : H % 2 ^ b % 2 ^ a = H % 2 ^ a :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 le)

/-- The bits the root lookup pulled for are needed: a query of the held bits at a pull consumes
more than they hold. -/
theorem needs_root {type : UInt32} {ca : Array Code} {off R used : Nat} {lens : List Nat}
    (inv : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca off R used lens) {bp hp : Nat}
    (hp_lt : hp < 2 ^ bp) (need : bp < (ca.getD (off + hp % 2 ^ R) default).bits.toNat) :
    ∀ e c, tableRead type ca off R (Zlib.Inftrees.Spec.DecodeShort.padded (natBits bp hp)) = some (e, c) →
      bp < c := fun _ _ read => Nat.lt_of_lt_of_le need (tableRead_ge inv hp_lt read)

/-- **A root leaf leaves fewer than 8 bits** once its bits are dropped, from fewer than 8. -/
theorem bits_after_root {type : UInt32} {ca : Array Code} {off R used : Nat} {lens : List Nat}
    (inv : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca off R used lens)
    (stable : StableQuery type ca off R) (pfx : PrefixQuery type ca off R) {l l1 : IL}
    (short : l.bits.toNat < 8) (hl1 : l1.hold.toNat < 2 ^ l1.bits.toNat)
    (leaf : Zlib.Inftrees.Spec.Subtable.IsLink type (ca.getD (off + l1.hold.toNat % 2 ^ R) default) = false)
    (fit : (ca.getD (off + l1.hold.toNat % 2 ^ R) default).bits.toNat ≤ l1.bits.toNat)
    (pull : Pulled ca off R l l1) :
    l1.bits.toNat - (ca.getD (off + l1.hold.toNat % 2 ^ R) default).bits.toNat < 8 := by
  rcases pull with ⟨e1, -⟩ | ⟨bp, hp, -, hp_lt, need, b1, keep⟩
  · rw [e1]; omega
  · obtain ⟨-, R15, room, -⟩ := inv.rootTable
    have inside : off + l1.hold.toNat % 2 ^ R < ca.size := by
      have := Nat.mod_lt l1.hold.toNat (Nat.two_pow_pos R); omega
    have read := Zlib.Inflate.Proofs.MeaningLookup.tableRead_root hl1 R15 inside leaf
    have := consumed_gt stable pfx (bp := bp) (hp := hp) (by omega)
      (by rw [keep, Nat.mod_eq_of_lt hp_lt]) (needs_root inv hp_lt need) read fit
    omega

/-- **A link and its second-level leaf leave fewer than 8 bits** once both are dropped. -/
theorem bits_after_link {type : UInt32} {ca : Array Code} {off R used : Nat} {lens : List Nat}
    (inv : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca off R used lens)
    (stable : StableQuery type ca off R) (pfx : PrefixQuery type ca off R) {l l1 l3 : IL}
    (short : l.bits.toNat < 8) (hl3 : l3.hold.toNat < 2 ^ l3.bits.toNat)
    (isl : Zlib.Inftrees.Spec.Subtable.IsLink type (ca.getD (off + l1.hold.toNat % 2 ^ R) default) = true)
    (fitR : R ≤ l1.bits.toNat) (ext : Ext l1 l3)
    (fit3 : (ca.getD (off + l1.hold.toNat % 2 ^ R) default).bits.toNat +
      (subVal ca off (ca.getD (off + l1.hold.toNat % 2 ^ R) default) l3.hold.toNat).bits.toNat ≤ l3.bits.toNat)
    (pull1 : Pulled ca off R l l1) (pull2 : Pulled2 ca off (ca.getD (off + l1.hold.toNat % 2 ^ R) default) l1 l3) :
    l3.bits.toNat - ((ca.getD (off + l1.hold.toNat % 2 ^ R) default).bits.toNat +
      (subVal ca off (ca.getD (off + l1.hold.toNat % 2 ^ R) default) l3.hold.toNat).bits.toNat) < 8 := by
  obtain ⟨-, R15, room, -⟩ := inv.rootTable
  generalize hlink : ca.getD (off + l1.hold.toNat % 2 ^ R) default = link at isl fit3 pull2 ⊢
  have idx1 : l1.hold.toNat % 2 ^ R < 2 ^ R := Nat.mod_lt _ (Nat.two_pow_pos R)
  have get1 : ca[off + l1.hold.toNat % 2 ^ R]? = some link := by
    rw [← hlink, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]; rfl
  obtain ⟨-, safe⟩ := inv.subtables _ _ idx1 get1 isl
  obtain ⟨-, -, width, cap, -⟩ := safe
  -- every query whose low `l1.bits` bits are those of `l1` reads the link, then its second level
  have viaLink : ∀ B H, l1.bits.toNat ≤ B → H < 2 ^ B → H % 2 ^ l1.bits.toNat = l1.hold.toNat →
      tableRead type ca off R (Zlib.Inftrees.Spec.DecodeShort.padded (natBits B H)) =
        some (subVal ca off link H, link.bits.toNat + (subVal ca off link H).bits.toNat) := by
    intro B H le lt keep
    have root : H % 2 ^ R = l1.hold.toNat % 2 ^ R := by rw [← keep, mod_mod_of_le fitR]
    have inside : off + H % 2 ^ R < ca.size := by rw [root]; omega
    have isl' : Zlib.Inftrees.Spec.Subtable.IsLink type (ca.getD (off + H % 2 ^ R) default) = true := by
      rw [root, hlink]; exact isl
    have sub := ZlibF.Math.InflateLookup.slice_lt H link.bits.toNat link.op.toNat
    have r := Zlib.Inflate.Proofs.MeaningLookup.tableRead_link lt R15 inside isl'
      (by rw [root, hlink]; exact width)
      (by rw [root, hlink]; unfold Zlib.Inflate.Proofs.MeaningLookup.subLookupIndexNat; omega)
    rw [root, hlink] at r
    exact r
  have read3 := viaLink l3.bits.toNat l3.hold.toNat ext.1 hl3 ext.2
  rcases pull2 with ⟨e3, h3⟩ | ⟨bq, hq, bq1, hq_lt, need, b3, keep3⟩
  · -- no byte for the second level: the last pull, if any, was the root's
    rcases pull1 with ⟨e1, -⟩ | ⟨bp, hp, -, hp_lt, needp, b1, keep1⟩
    · rw [e3, e1]; omega
    · have keep : l3.hold.toNat % 2 ^ bp = hp % 2 ^ bp := by
        rw [h3, keep1, Nat.mod_eq_of_lt hp_lt]
      have := consumed_gt stable pfx (bp := bp) (hp := hp) (by rw [e3]; omega) keep
        (needs_root inv hp_lt needp) read3 fit3
      rw [e3]; omega
  · have needq : ∀ e c, tableRead type ca off R (Zlib.Inftrees.Spec.DecodeShort.padded (natBits bq hq)) =
        some (e, c) → bq < c := by
      intro e c rd
      have hkeep : hq % 2 ^ l1.bits.toNat = l1.hold.toNat := by
        rw [← keep3, mod_mod_of_le bq1, ext.2]
      rw [viaLink bq hq bq1 hq_lt hkeep] at rd
      injection rd with rd
      injection rd with _ e2
      omega
    have := consumed_gt stable pfx (bp := bq) (hp := hq) (by omega)
      (by rw [keep3, Nat.mod_eq_of_lt hq_lt]) needq read3 fit3
    omega

end Zlib.Infback.Safety
