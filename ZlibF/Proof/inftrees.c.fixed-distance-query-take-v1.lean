import ZlibF.Proof.«inftrees.c.query-take-interface»
import ZlibF.Math.FastTokenPrefix
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»
import ZlibF.Proof.«inftrees.c.decode.stability»
import ZlibF.Zlib.«inffixed.h»

namespace Zlib.Inftrees.Proofs.QueryTakeSource
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
open Zlib.Inffast.Proofs
open DecodeSemantics DecodeSoundness DecodeTableInvariant DecodeTableStability
set_option autoImplicit false

/-- A successful five-bit read indexes the exact static distance table.
Every stored cell consumes five bits and is a leaf, including reserved cells. -/
theorem fixed_distance_query_of_read {input rest : List Bool} {value : Nat}
    (read : readBits 5 input = some (value, rest)) :
    tableRead DISTS Zlib.InffixedH.distfix 0 5 input =
      some (Zlib.InffixedH.distfix.getD value default, 5) := by
  have bound : value < 32 := (ZlibF.Math.CodeLengthPrefix.read_word read).1
  have size : Zlib.InffixedH.distfix.size = 32 := by decide
  have inside : value < Zlib.InffixedH.distfix.size := by omega
  have cell : Zlib.InffixedH.distfix[value]? = some (Zlib.InffixedH.distfix.getD value default) := by
    simp [Array.getD_eq_getD_getElem?, inside]
  have fields : ∀ i : Fin 32,
      (Zlib.InffixedH.distfix.getD i.val default).bits.toNat = 5 ∧
      ((Zlib.InffixedH.distfix.getD i.val default).op &&& 240 == 0) = false := by decide +kernel
  obtain ⟨bits, leaf⟩ := fields ⟨value, bound⟩
  simp only [tableRead, read, bind, Option.bind, Nat.zero_add, cell,
    show DISTS ≠ LENS by decide, ite_false, leaf, Bool.false_eq_true]
  simp only [pure, bits]

/-- The actual fixed distance array retains its rejected cell and consumed
width after truncation to the consumed code word. -/
theorem fixed_distance_query_take : QueryTake DISTS Zlib.InffixedH.distfix 0 5 := by
  intro input entry consumed query fit
  have enough : 5 ≤ (DecodeShort.padded input).length := by have := padded_length input; omega
  obtain ⟨value, tail, read, valueBound, _source⟩ := ZlibF.Math.InflateDecode.read_total 5 _ enough
  have actual := fixed_distance_query_of_read read
  have same := Prod.mk.inj (Option.some.inj (query.symm.trans actual))
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨localRest, localRead, _suffix⟩ := ZlibF.Math.FastTokenPrefix.readBits_restrict
    (available := input) (future := List.replicate (15 - input.length) false) read fit
  have source := (ZlibF.Math.CodeLengthPrefix.read_word localRead).2
  have word : input.take 5 = bitsOfNat value 5 := by
    rw [source, List.take_append_of_le_length (by simp [bitsOfNat_length]),
      List.take_of_length_le (by simp [bitsOfNat_length])]
  have readWord : readBits 5 (DecodeShort.padded (input.take 5)) =
      some (value, List.replicate 10 false) := by
    rw [word]
    have actual := Zlib.Inffast.Proofs.readBits_bitsOfNat 5 5 value (List.replicate 10 false) (Nat.le_refl _)
    simpa only [DecodeShort.padded, bitsOfNat_length, Nat.sub_self, bitsOfNat_zero, List.nil_append,
      Nat.mod_eq_of_lt valueBound] using actual
  exact fixed_distance_query_of_read readWord

/-- An actual rejected fitted query forbids every valid distance decode
from its consumed word followed by arbitrary later bits. -/
theorem rejected_distance_consumed_word
    {codes : Array Code} {offset root extent : Nat} {D : List Nat}
    (inv : Inv DISTS codes offset root extent D)
    (stable : StableQuery DISTS codes offset root)
    (take : QueryTake DISTS codes offset root)
    {input : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead DISTS codes offset root (DecodeShort.padded input) = some (entry, consumed))
    (fit : consumed ≤ input.length) (rejected : ¬ LeafAccepted DISTS entry) :
    tableRead DISTS codes offset root (DecodeShort.padded (input.take consumed)) = some (entry, consumed) ∧
      ∀ future : List Bool, ¬ ∃ symbol rest,
        decodeSym D (input.take consumed ++ future) = some (symbol, rest) ∧ symbol ≤ 29 := by
  have prefixQuery := take input entry consumed query fit
  refine ⟨prefixQuery, ?_⟩
  intro future
  have impossible := short_rejected_leaf_stays_invalid DISTS codes offset root extent D inv stable
    (input.take consumed) entry consumed prefixQuery (by simp [List.length_take, Nat.min_eq_left fit]) rejected future
  simpa only [ValidSymbol, show DISTS ≠ LENS by decide, ite_false] using impossible

#print axioms fixed_distance_query_of_read
#print axioms fixed_distance_query_take
#print axioms rejected_distance_consumed_word
end Zlib.Inftrees.Proofs.QueryTakeSource
