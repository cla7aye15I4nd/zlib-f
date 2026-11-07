import ZlibF.Spec.InflateDecodeTableStability
import ZlibF.Proof.«inftrees.c.decode.frame»
import ZlibF.Proof.Format.Huffman

/-!
# Stable queries and early invalid-code rejection

The prefix frame transports the exact query, rather than only its bounds.
A hypothetical valid decode after a rejected fitted query is extended to
full width, where classification contradicts stability of the rejection.
-/

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableStability

/-- Preserving every potentially read cell preserves stability under all
future input suffixes, including the rejected leaves. -/
theorem query_stability_of_prefix : Goal.query_stability_of_prefix := by
  intro type before after offset root used ht hext stable cells
  intro inp entry consumed query fit more
  have frame := decode_table_read_preserved type before after offset root used ht hext cells
  rw [frame] at query
  rw [frame]
  exact stable inp entry consumed query fit more

/-- A fitted rejected entry cannot become a valid independent symbol by
adding input. The hypothetical decode extends to a full-width query, where
the invariant's classification and the unchanged entry contradict it. -/
theorem short_rejected_leaf_stays_invalid : Goal.short_rejected_leaf_stays_invalid := by
  intro type ca offset root used lens inv stable inp entry consumed query fit rejected more
  rintro ⟨symbol, rest, decoded, valid⟩
  let padding : List Bool := List.replicate (15 - (inp ++ more).length) false
  let full : List Bool := (inp ++ more) ++ padding
  have long : 15 ≤ full.length := by simp [full, padding]; omega
  have fullPadded : DecodeShort.padded full = full := by
    simp [DecodeShort.padded, Nat.sub_eq_zero_of_le long]
  have extended := ZlibF.Spec.Proofs.ext_acceptable inv.acceptable
    (inp ++ more) symbol rest padding decoded
  have fullQuery : tableRead type ca offset root full = some (entry, consumed) := by
    have stableQuery := stable inp entry consumed query fit (more ++ padding)
    have reassoc : inp ++ (more ++ padding) = full := by
      simp only [full, List.append_assoc]
    rw [reassoc, fullPadded] at stableQuery
    exact stableQuery
  obtain ⟨entry', consumed', classifiedQuery, classification⟩ := inv.classify full long
  rw [fullQuery] at classifiedQuery
  have same := Option.some.inj classifiedQuery
  obtain ⟨sameEntry, sameConsumed⟩ := Prod.mk.inj same
  subst entry' consumed'
  apply rejected
  exact classification.mpr ⟨symbol, rest ++ padding, extended, valid⟩

end Zlib.Inftrees.Proofs
