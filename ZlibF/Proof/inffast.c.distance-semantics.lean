import ZlibF.Spec.InflateFastDistanceSemantics
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»

/-!
# Fast distance lookup and independent decoding

The existing fast lookup relation is tied to the same finite two-level
query as the slow decoder. Constructor-derived flags reconcile acceptance
before the invariant supplies independent symbol meaning or rejection.
-/

set_option autoImplicit false

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Spec.DistanceSemantics

/-- Every selected fast distance leaf has the independent meaning of its
actual table query, including all future-stable rejected prefixes. -/
theorem distance_lookup_matches_format : Goal.distance_lookup_matches_format := by
  intro e hold bits input tableUsed lens entry consumed inv stable flags hhold hbits look
  let root := e.s0.distbits.toNat
  let idx := hold % 2 ^ root
  let stream := Sg e hold bits input
  have rootLe : root ≤ 15 := inv.rootTable.2.1
  have idxLt : idx < 2 ^ root := Nat.mod_lt _ (Nat.two_pow_pos root)
  have rootRead : readBits root stream =
      some (idx, Sg e (hold / 2 ^ root) (bits-root) input) := by
    exact readBits_bitsOfNat root bits hold (inBits e input) (by omega)
  obtain ⟨first, firstCell, firstPos, firstBits⟩ := inv.rootTable.2.2.2 idx idxLt
  have firstGet : e.DCA.getD (e.od + idx) default = first := by
    simp only [Array.getD_eq_getD_getElem?, firstCell, Option.getD_some]
  have maskBits (op : UInt8) (hm : op &&& 0xf0 = 0) : op &&& 16 = 0 ∧ op &&& 64 = 0 := by
    have h16 := congrArg (fun x : UInt8 => x &&& 16) hm
    have h64 := congrArg (fun x : UInt8 => x &&& 64) hm
    rw [UInt8.and_assoc] at h16 h64
    exact ⟨h16, h64⟩
  have smallMask : ∀ op : UInt8, op.toNat ≤ 15 → op &&& 0xf0 = 0 := by
    apply u8_forall
    decide +kernel
  have selected : tableRead DISTS e.DCA e.od root stream = some (entry, consumed) ∧
      1 ≤ consumed ∧ consumed ≤ 15 ∧ DistLeaf 0 entry := by
    rcases look with ⟨hget, hconsumed, noLink⟩ |
      ⟨E0, j, hget, link, jLt, jEq, hleafGet, hconsumed, codeLe, noLink⟩
    · change e.DCA.getD (e.od + idx) default = entry at hget
      have he : first = entry := firstGet.symm.trans hget
      rw [he] at firstCell firstPos firstBits
      have invalidMask : entry.op &&& 0xf0 ≠ 0 := by
        intro hm
        exact noLink (maskBits entry.op hm)
      have leaf := e.hdt.2.2 idx idxLt
      rw [hget, ite_eq_right noLink] at leaf
      refine ⟨?_, ?_, ?_, leaf⟩
      · simp only [tableRead, rootRead, bind, Option.bind, firstCell]
        simp only [show DISTS ≠ LENS by decide, ite_false]
        simp [invalidMask, hconsumed]
      · omega
      · omega
    · change e.DCA.getD (e.od + idx) default = E0 at hget
      have he : first = E0 := firstGet.symm.trans hget
      rw [he] at firstCell firstPos firstBits
      have linkOK := e.hdt.2.2 idx idxLt
      rw [hget, ite_eq_left link] at linkOK
      have opMask : E0.op &&& 0xf0 = 0 := smallMask E0.op linkOK.2.2.1
      have slowLink : Subtable.IsLink DISTS E0 = true := by
        simp [Subtable.IsLink, show DISTS ≠ LENS by decide, opMask]
      obtain ⟨bitsRoot, subSafe⟩ := inv.subtables idx E0 idxLt firstCell slowLink
      have rootFits : E0.bits.toNat ≤ bits := by omega
      have opFits : E0.op.toNat ≤ bits - E0.bits.toNat := by have := subSafe.2.2.1; omega
      have secondRead : readBits E0.op.toNat (stream.drop E0.bits.toNat) =
          some (j, Sg e ((hold / 2 ^ E0.bits.toNat) / 2 ^ E0.op.toNat)
            ((bits-E0.bits.toNat)-E0.op.toNat) input) := by
        rw [show stream.drop E0.bits.toNat = Sg e (hold / 2 ^ E0.bits.toNat) (bits-E0.bits.toNat) input
          from (Sg_drop hold bits input E0.bits.toNat rootFits).symm]
        rw [jEq]
        exact readBits_bitsOfNat E0.op.toNat (bits-E0.bits.toNat) (hold / 2 ^ E0.bits.toNat)
          (inBits e input) opFits
      obtain ⟨second, secondCell, secondPos, secondBits⟩ := subSafe.2.2.2.2 j jLt
      have secondGet : e.DCA.getD (e.od+E0.val.toNat+j) default = second := by
        simp only [Array.getD_eq_getD_getElem?, secondCell, Option.getD_some]
      have he : second = entry := secondGet.symm.trans hleafGet
      rw [he] at secondCell secondPos secondBits
      have leafD := linkOK.2.2.2.2 j jLt
      rw [hleafGet] at leafD
      have leaf : DistLeaf 0 entry := ⟨by have := leafD.1; omega, leafD.2⟩
      refine ⟨?_, ?_, by omega, leaf⟩
      · simp only [tableRead, rootRead, bind, Option.bind, firstCell]
        simp only [show DISTS ≠ LENS by decide, ite_false, opMask, BEq.rfl, ite_true]
        simp only [secondRead, Option.bind_some, secondCell]
        simp [hconsumed]
      · omega
  obtain ⟨query, positive, codeLe, leaf⟩ := selected
  have streamLong : 15 ≤ stream.length := by
    simp only [stream, Sg, List.length_append, bitsOfNat_length]
    omega
  have paddedStream : DecodeShort.padded stream = stream := by
    simp [DecodeShort.padded, Nat.sub_eq_zero_of_le streamLong]
  have queryPadded : tableRead DISTS e.DCA e.od root (DecodeShort.padded stream) = some (entry,consumed) := by
    rw [paddedStream]
    exact query
  have fit : consumed ≤ stream.length := by omega
  have compatible := flags stream entry consumed streamLong query
  refine ⟨query, positive, codeLe, leaf, ?_⟩
  by_cases hasBase : entry.op &&& 16 ≠ 0
  · right
    have accepted : LeafAccepted DISTS entry := by
      simp only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false]
      exact compatible hasBase
    obtain ⟨symbol, valid, meaning, hused, decoded, extended⟩ :=
      inv.short stream entry consumed queryPadded fit accepted
    exact ⟨hasBase, symbol, valid, meaning, hused, decoded, extended⟩
  · left
    have noBase : entry.op &&& 16 = 0 := by simpa using hasBase
    have invalid : entry.op &&& 64 ≠ 0 := by
      rcases leaf.2 with h | h
      · exact False.elim (hasBase h.1)
      · exact h.2
    have rejected : ¬ LeafAccepted DISTS entry := by
      simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false] using invalid
    have noValid := Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid DISTS e.DCA e.od root tableUsed lens
      inv stable stream entry consumed queryPadded fit rejected
    exact ⟨noBase, noValid⟩

end Zlib.Inffast.Proofs
