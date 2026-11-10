import ZlibF.Proof.«inffixed.h.fixed-stability»
import ZlibF.Proof.«inftrees.c.query-take-interface»
namespace Zlib.InffixedH.Proofs
open C Zlib.Inftrees ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The actual fixed LENS array repeats each short leaf at all root
lookahead indices. Hence only the consumed code bits determine the query,
including both reserved eight-bit symbols. -/
theorem lenfix_query_take
    (inp : List Bool) (entry : Code) (consumed : Nat)
    (query : tableRead LENS Zlib.InffixedH.lenfix 0 9
      (Zlib.Inftrees.Spec.DecodeShort.padded inp) = some (entry, consumed))
    (fits : consumed ≤ inp.length) :
    tableRead LENS Zlib.InffixedH.lenfix 0 9
      (Zlib.Inftrees.Spec.DecodeShort.padded (inp.take consumed)) = some (entry, consumed) := by
  have enough1 : 9 ≤ (Zlib.Inftrees.Spec.DecodeShort.padded inp).length := by
    have bound := Zlib.Inftrees.Proofs.padded_length inp
    omega
  have enough2 : 9 ≤ (Zlib.Inftrees.Spec.DecodeShort.padded (inp.take consumed)).length := by
    have bound := Zlib.Inftrees.Proofs.padded_length (inp.take consumed)
    omega
  obtain ⟨i, rest1, read1, bound1, _source1⟩ := ZlibF.Math.InflateDecode.read_total 9 _ enough1
  obtain ⟨j, rest2, read2, bound2, _source2⟩ := ZlibF.Math.InflateDecode.read_total 9 _ enough2
  have ib : i < 512 := by simpa using bound1
  have jb : j < 512 := by simpa using bound2
  have first := lenfix_query_index i ib _ rest1 read1
  have second := lenfix_query_index j jb _ rest2 read2
  have equal := Option.some.inj (query.symm.trans first)
  have entryEq : entry = Zlib.InffixedH.lenfix[i]! := congrArg Prod.fst equal
  have consumedEq : consumed = (Zlib.InffixedH.lenfix[i]!).bits.toNat := congrArg Prod.snd equal
  have usedBound : consumed ≤ 9 := by rw [consumedEq]; exact (lenfix_widths ⟨i, ib⟩).2
  have shortFits : consumed ≤ (inp.take consumed).length := by
    simp only [List.length_take, Nat.min_eq_left fits]
    omega
  have originalRead : readBits 9 (Zlib.Inftrees.Spec.DecodeShort.padded ((inp.take consumed) ++ inp.drop consumed)) = some (i, rest1) := by
    rw [List.take_append_drop]
    exact read1
  have residue := padded_index_residue 9 consumed (inp.take consumed) (inp.drop consumed)
    (by decide) usedBound shortFits j i rest2 rest1 read2 originalRead
  rw [consumedEq] at residue
  have sameCells := lenfix_same_of_residue i j ib jb residue.symm
  rw [sameCells, ← entryEq] at second
  have width : consumed = entry.bits.toNat := by rw [entryEq]; exact consumedEq
  simpa only [width] using second

#print axioms lenfix_query_take
end Zlib.InffixedH.Proofs
