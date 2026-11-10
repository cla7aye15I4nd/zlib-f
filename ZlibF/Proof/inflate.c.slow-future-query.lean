import ZlibF.Proof.«inflate.c.slow-future-prefix»
import ZlibF.Proof.«inflate.c.slow-subtable-path»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open SlowSubtablePath
set_option autoImplicit false

/-- A fitting real held-bit query has the independently valid future's
exact entry and code width, including rejection cells. No independent
successful read on the current prefix is assumed. -/
theorem fitted_query_future {type : UInt32} {ca : Array Code} {offset root extent : Nat}
    {alphabet : List Nat} {h : Heap} {l : IL} {bs : List UInt8}
    {future input rest : List Bool} {symbol consumed : Nat} {entry : Code}
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca offset root extent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery type ca offset root)
    (_B : BitInv h l bs) (source : FutureSource l bs future input)
    (decoded : decodeSym alphabet input = some (symbol, rest)) (valid : ValidSymbol type symbol)
    (query : tableRead type ca offset root (Zlib.Inftrees.Spec.DecodeShort.padded
      (bitsOfNat l.hold.toNat l.bits.toNat)) = some (entry, consumed))
    (fits : consumed ≤ l.bits.toNat) :
    SymbolEntry type symbol entry ∧ consumed = alphabet.getD symbol 0 ∧
      alphabet.getD symbol 0 ≤ (stream l bs).length := by
  obtain ⟨wanted, width, forward, _accepted, symbolMeaning, codeWidth, _fits, _rest⟩ :=
    Zlib.Inftrees.Proofs.DecodeForward.lookup_of_decode meaning decoded valid
  have extended := stable _ _ _ query (by simpa only [bitsOfNat_length] using fits)
    (bytesBits bs ++ future)
  have whole : bitsOfNat l.hold.toNat l.bits.toNat ++ (bytesBits bs ++ future) = input := by
    simpa only [FutureSource, stream, natBits_testBit, bitsOfNat, List.append_assoc] using source
  rw [whole] at extended
  obtain ⟨entries, widths⟩ := Prod.mk.inj (Option.some.inj (extended.symm.trans forward))
  refine ⟨by rw [entries]; exact symbolMeaning, widths.trans codeWidth, ?_⟩
  rw [← codeWidth, ← widths]
  have inputLength : (stream l bs).length = l.bits.toNat + 8 * bs.length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
  rw [inputLength]
  omega

/-- A linked actual query which fits held bits proves that the full
independent code already fits the current source. -/
theorem fitted_subtable_future {type : UInt32} {ca : Array Code} {offset root extent : Nat}
    {alphabet : List Nat} {h : Heap} {l : IL} {bs : List UInt8} {first : Code}
    {future input rest : List Bool} {symbol : Nat}
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca offset root extent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery type ca offset root)
    (B : BitInv h l bs) (source : FutureSource l bs future input)
    (decoded : decodeSym alphabet input = some (symbol, rest)) (valid : ValidSymbol type symbol)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ root]? = some first)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink type first = true)
    (selected : l.here = subLookupValue ca offset first l)
    (fits : first.bits.toNat + l.here.bits.toNat ≤ l.bits.toNat) :
    SymbolEntry type symbol l.here ∧ first.bits.toNat + l.here.bits.toNat = alphabet.getD symbol 0 ∧
      alphabet.getD symbol 0 ≤ (stream l bs).length := by
  exact fitted_query_future meaning stable B source decoded valid
    (subtable_query_read meaning B rootCell link selected) fits

#print axioms fitted_query_future
#print axioms fitted_subtable_future
end Zlib.Inflate.Proofs.SlowInputFragment
