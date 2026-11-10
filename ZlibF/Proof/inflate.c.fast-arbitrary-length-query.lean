import ZlibF.Proof.«inflate.c.payload-generic-stage»
import ZlibF.Proof.«inflate.c.slow-subtable-path»
import ZlibF.Proof.«inflate.c.accepted-token-soundness»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inftrees.Spec.Subtable Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192

/-- The actual fast root/link selection is the invariant's fitted query
on existing held bits. This classifies every byte pattern, without an
independent decoded-symbol or valid-future premise. -/
theorem length_selected_query
    {h : Heap} {slow : IL} {bs : List UInt8}
    (B : BitInv h slow bs) (held : 15 ≤ slow.bits.toNat)
    {codes : Array Code} {offset root extent : Nat} {L : List Nat}
    (safe : LenTableSafe codes offset root) (inv : Inv LENS codes offset root extent L)
    (stable : StableQuery LENS codes offset root) :
    let first := codes.getD (offset + slow.hold.toNat % 2 ^ root) default
    ∃ index skipped,
      index < codes.size ∧
      LenLeaf skipped (codes.getD index default) ∧
      skipped + (codes.getD index default).bits.toNat ≤ 15 ∧
      tableRead LENS codes offset root
        (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat slow.hold.toNat slow.bits.toNat)) =
          some (codes.getD index default, skipped + (codes.getD index default).bits.toNat) ∧
      ((skipped = 0 ∧ index = offset + slow.hold.toNat % 2 ^ root ∧ ¬ LenLink first) ∨
       (LenLink first ∧ skipped = first.bits.toNat ∧
        index = offset + first.val.toNat + (slow.hold.toNat / 2 ^ first.bits.toNat) % 2 ^ first.op.toNat)) ∧
      ((LeafAccepted LENS (codes.getD index default) ∧
          ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol (codes.getD index default) ∧
            skipped + (codes.getD index default).bits.toNat = L.getD symbol 0 ∧
            decodeSym L (stream slow bs) =
              some (symbol, (stream slow bs).drop (skipped + (codes.getD index default).bits.toNat))) ∨
       (¬ LeafAccepted LENS (codes.getD index default) ∧
        ∀ more : List Bool, ¬ ∃ symbol rest,
          decodeSym L (stream slow bs ++ more) = some (symbol, rest) ∧ ValidSymbol LENS symbol)) := by
  dsimp only
  let rootIndex := slow.hold.toNat % 2 ^ root
  let first := codes.getD (offset + rootIndex) default
  have rootBound : rootIndex < 2 ^ root := Nat.mod_lt _ (Nat.two_pow_pos _)
  have firstBound : offset + rootIndex < codes.size := by have := safe.2.1; omega
  have cell : codes[offset + rootIndex]? = some first := by
    simp [first, Array.getD_eq_getD_getElem?, firstBound]
  have classify (index skipped : Nat) (bound : index < codes.size)
      (leaf : LenLeaf skipped (codes.getD index default))
      (width : skipped + (codes.getD index default).bits.toNat ≤ 15)
      (query : tableRead LENS codes offset root
        (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat slow.hold.toNat slow.bits.toNat)) =
          some (codes.getD index default, skipped + (codes.getD index default).bits.toNat)) :
      (LeafAccepted LENS (codes.getD index default) ∧
          ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol (codes.getD index default) ∧
            skipped + (codes.getD index default).bits.toNat = L.getD symbol 0 ∧
            decodeSym L (stream slow bs) =
              some (symbol, (stream slow bs).drop (skipped + (codes.getD index default).bits.toNat))) ∨
       (¬ LeafAccepted LENS (codes.getD index default) ∧
        ∀ more : List Bool, ¬ ∃ symbol rest,
          decodeSym L (stream slow bs ++ more) = some (symbol, rest) ∧ ValidSymbol LENS symbol) := by
    have fit : skipped + (codes.getD index default).bits.toNat ≤
        (bitsOfNat slow.hold.toNat slow.bits.toNat).length := by rw [bitsOfNat_length]; omega
    have source : bitsOfNat slow.hold.toNat slow.bits.toNat ++ bytesBits bs = stream slow bs := by
      simp only [stream, natBits_testBit, bitsOfNat]
    by_cases accepted : LeafAccepted LENS (codes.getD index default)
    · obtain ⟨symbol, valid, fields, length, _decoded, extend⟩ := inv.short _ _ _ query fit accepted
      have decoded := extend (bytesBits bs)
      have rest : (bitsOfNat slow.hold.toNat slow.bits.toNat).drop
          (skipped + (codes.getD index default).bits.toNat) ++ bytesBits bs =
          (stream slow bs).drop (skipped + (codes.getD index default).bits.toNat) := by
        rw [← source, List.drop_append_of_le_length fit]
      rw [source, rest] at decoded
      exact Or.inl ⟨accepted, symbol, valid, fields, length, decoded⟩
    · have rejected := Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid
        LENS codes offset root extent L inv stable _ _ _ query fit accepted
      refine Or.inr ⟨accepted, ?_⟩
      intro more
      have extend := rejected (bytesBits bs ++ more)
      simpa only [← List.append_assoc, source] using extend
  by_cases link : LenLink first
  · have linkOK := safe.2.2 rootIndex rootBound
    change (if LenLink first then LinkOK LenLeaf codes offset first else LenLeaf 0 first) at linkOK
    rw [ite_eq_left link] at linkOK
    have maskZero : first.op &&& 0xf0 = 0 := by
      have finite : ∀ op : UInt8, op.toNat ≤ 15 → op &&& 0xf0 = 0 := by
        apply u8_forall
        decide +kernel
      exact finite first.op linkOK.2.2.1
    have mathLink : IsLink LENS first = true := by simp [IsLink, link.1, maskZero]
    let selected := (slow.hold.toNat / 2 ^ first.bits.toNat) % 2 ^ first.op.toNat
    let index := offset + first.val.toNat + selected
    have slice : selected < 2 ^ first.op.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
    obtain ⟨bound, leaf, width⟩ := len_table_link_target safe rootBound link slice
    change index < codes.size at bound
    change LenLeaf first.bits.toNat (codes.getD index default) at leaf
    change (codes.getD index default).bits.toNat + first.bits.toNat ≤ 15 at width
    let regs := {slow with here := codes.getD index default}
    have localB : BitInv h regs bs := ⟨B.have_eq, B.next, B.hold_lt⟩
    have selectedCode : regs.here = subLookupValue codes offset first regs := by
      simp only [regs, index, selected, subLookupValue, subLookupIndex, ZlibF.Math.InflateLookup.slice_eq]
    have query := SlowSubtablePath.subtable_query_read inv localB cell mathLink selectedCode
    change tableRead LENS codes offset root
      (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat slow.hold.toNat slow.bits.toNat)) =
        some (codes.getD index default, first.bits.toNat + (codes.getD index default).bits.toNat) at query
    exact ⟨index, first.bits.toNat, bound, leaf, by omega, query,
      Or.inr ⟨link, rfl, rfl⟩, classify index first.bits.toNat bound leaf (by omega) query⟩
  · have leaf := safe.2.2 rootIndex rootBound
    change (if LenLink first then LinkOK LenLeaf codes offset first else LenLeaf 0 first) at leaf
    rw [ite_eq_right link] at leaf
    have noMathLink : IsLink LENS first = false := by
      by_cases zero : first.op = 0
      · simp [IsLink, zero]
      · have nonzeroMask : first.op &&& 0xf0 ≠ 0 := by
          intro mask
          have masks : first.op &&& 16 = 0 ∧ first.op &&& 64 = 0 := by
            constructor
            · have m := congrArg (fun x : UInt8 => x &&& 16) mask
              rw [UInt8.and_assoc, show (240 : UInt8) &&& 16 = 16 by decide] at m
              exact m
            · have m := congrArg (fun x : UInt8 => x &&& 64) mask
              rw [UInt8.and_assoc, show (240 : UInt8) &&& 64 = 64 by decide] at m
              exact m
          exact link ⟨zero, masks⟩
        simp [IsLink, nonzeroMask]
    obtain ⟨suffix, read⟩ := ZlibF.Math.InflateHeldBits.padded_query B.hold_lt inv.rootTable.2.1
    have noLinkBool : (first.op != 0 && (first.op &&& 0xf0) == 0) = false := by
      simpa only [IsLink, ite_true] using noMathLink
    have cellRoot : codes[offset + slow.hold.toNat % 2 ^ root]? = some first := cell
    have query : tableRead LENS codes offset root
        (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat slow.hold.toNat slow.bits.toNat)) =
          some (first, 0 + first.bits.toNat) := by
      simp only [tableRead, read, bind, Option.bind, cellRoot]
      simp [noLinkBool]
    have width : 0 + (codes.getD (offset + rootIndex) default).bits.toNat ≤ 15 := by
      simpa only [first, Nat.add_zero, Nat.zero_add] using leaf.1
    exact ⟨offset + rootIndex, 0, firstBound, leaf, width, query,
      Or.inl ⟨rfl, rfl, link⟩, classify _ 0 firstBound leaf width query⟩

#print axioms length_selected_query
end Zlib.Inflate.Proofs.FastArbitraryBody
