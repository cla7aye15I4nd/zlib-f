import ZlibF.Proof.Format.Deflate

import ZlibF.Proof.«inffixed.h.input-meaning»
import ZlibF.Spec.InflateDecodeTableStability

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Zlib.InffixedH.Proofs
open C Zlib.Inftrees

private instance : DecidableEq Code := fun a b =>
  decidable_of_iff (a.op = b.op ∧ a.bits = b.bits ∧ a.val = b.val) (by cases a; cases b; simp)

theorem lenfix_widths : ∀ i : Fin 512,
    7 ≤ (Zlib.InffixedH.lenfix[i.val]!).bits.toNat ∧
    (Zlib.InffixedH.lenfix[i.val]!).bits.toNat ≤ 9 := by
  decide +kernel

theorem lenfix_replicated : ∀ i : Fin 512,
    let e := Zlib.InffixedH.lenfix[i.val]!
    (e.bits.toNat = 7 →
      Zlib.InffixedH.lenfix[i.val % 128]? = some e ∧
      Zlib.InffixedH.lenfix[i.val % 128 + 128]? = some e ∧
      Zlib.InffixedH.lenfix[i.val % 128 + 256]? = some e ∧
      Zlib.InffixedH.lenfix[i.val % 128 + 384]? = some e) ∧
    (e.bits.toNat = 8 →
      Zlib.InffixedH.lenfix[i.val % 256]? = some e ∧
      Zlib.InffixedH.lenfix[i.val % 256 + 256]? = some e) := by
  decide +kernel

theorem distfix_widths : ∀ i : Fin 32,
    (Zlib.InffixedH.distfix[i.val]!).bits.toNat = 5 := by
  decide +kernel


open ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeTableStability

theorem padded_index_residue (root used : Nat) (inp more : List Bool)
    (rootBound : root ≤ 15) (usedBound : used ≤ root) (fit : used ≤ inp.length)
    (i j : Nat) (rest1 rest2 : List Bool)
    (read1 : readBits root (Zlib.Inftrees.Spec.DecodeShort.padded inp) = some (i, rest1))
    (read2 : readBits root (Zlib.Inftrees.Spec.DecodeShort.padded (inp ++ more)) = some (j, rest2)) :
    i % 2 ^ used = j % 2 ^ used := by
  have len1 : root ≤ (Zlib.Inftrees.Spec.DecodeShort.padded inp).length := by
    have h := Zlib.Inftrees.Proofs.padded_length inp
    omega
  have len2 : root ≤ (Zlib.Inftrees.Spec.DecodeShort.padded (inp ++ more)).length := by
    have h := Zlib.Inftrees.Proofs.padded_length (inp ++ more)
    omega
  obtain ⟨v1, t1, got1, _, src1⟩ := ZlibF.Math.InflateDecode.read_total root _ len1
  obtain ⟨v2, t2, got2, _, src2⟩ := ZlibF.Math.InflateDecode.read_total root _ len2
  have iEq : i = v1 := congrArg Prod.fst (Option.some.inj (read1.symm.trans got1))
  have jEq : j = v2 := congrArg Prod.fst (Option.some.inj (read2.symm.trans got2))
  subst i; subst j
  obtain ⟨small, rem, smallRun, _, _⟩ := ZlibF.Math.InflateDecode.read_total used inp fit
  have low1 : readBits used (Zlib.Inftrees.Spec.DecodeShort.padded inp) =
      some (v1 % 2 ^ used, (bitsOfNat (v1 / 2 ^ used) (root - used)) ++ t1) := by
    rw [src1]
    exact readBits_bitsOfNat used root v1 t1 usedBound
  have low2 : readBits used (Zlib.Inftrees.Spec.DecodeShort.padded (inp ++ more)) =
      some (v2 % 2 ^ used, (bitsOfNat (v2 / 2 ^ used) (root - used)) ++ t2) := by
    rw [src2]
    exact readBits_bitsOfNat used root v2 t2 usedBound
  have fromInp1 := ZlibF.Spec.Proofs.readBits_append used inp small rem
      (List.replicate (15 - inp.length) false) smallRun
  have fromInp2 := ZlibF.Spec.Proofs.readBits_append used inp small rem
      (more ++ List.replicate (15 - (inp ++ more).length) false) smallRun
  have lowVal1 : v1 % 2 ^ used = small := by
    exact congrArg Prod.fst (Option.some.inj
      (low1.symm.trans (by simpa only [Zlib.Inftrees.Spec.DecodeShort.padded] using fromInp1)))
  have lowVal2 : v2 % 2 ^ used = small := by
    exact congrArg Prod.fst (Option.some.inj
      (low2.symm.trans (by simpa only [Zlib.Inftrees.Spec.DecodeShort.padded, List.append_assoc] using fromInp2)))
  exact lowVal1.trans lowVal2.symm

theorem lenfix_size : Zlib.InffixedH.lenfix.size = 512 := by decide +kernel
theorem distfix_size : Zlib.InffixedH.distfix.size = 32 := by decide +kernel

theorem lenfix_query_index (i : Nat) (inside : i < 512)
    (inp : List Bool) (rest : List Bool)
    (read : readBits 9 inp = some (i, rest)) :
    tableRead LENS Zlib.InffixedH.lenfix 0 9 inp =
      some (Zlib.InffixedH.lenfix[i]!, (Zlib.InffixedH.lenfix[i]!).bits.toNat) := by
  have selected : Zlib.InffixedH.lenfix[i]? = some (Zlib.InffixedH.lenfix[i]!) := by
    simp [lenfix_size, inside]
  have noLink := lenfix_no_links ⟨i, inside⟩
  have noLinkProp : ¬ ((Zlib.InffixedH.lenfix[i]!).op ≠ 0 ∧
      (Zlib.InffixedH.lenfix[i]!).op &&& 0xf0 = 0) := by
    simpa using (Bool.eq_false_iff.mpr noLink)
  simp [tableRead, read, selected, noLinkProp]

theorem distfix_query_index (i : Nat) (inside : i < 32)
    (inp : List Bool) (rest : List Bool)
    (read : readBits 5 inp = some (i, rest)) :
    tableRead DISTS Zlib.InffixedH.distfix 0 5 inp =
      some (Zlib.InffixedH.distfix[i]!, (Zlib.InffixedH.distfix[i]!).bits.toNat) := by
  have selected : Zlib.InffixedH.distfix[i]? = some (Zlib.InffixedH.distfix[i]!) := by
    simp [distfix_size, inside]
  have noLink := distfix_no_links ⟨i, inside⟩
  have noLinkProp : (Zlib.InffixedH.distfix[i]!).op &&& 0xf0 ≠ 0 := by
    simpa using noLink
  simp [tableRead, read, selected, noLinkProp, DISTS, LENS]

theorem lenfix_same_of_residue (i j : Nat) (ib : i < 512) (jb : j < 512)
    (same : i % 2 ^ (Zlib.InffixedH.lenfix[i]!).bits.toNat =
      j % 2 ^ (Zlib.InffixedH.lenfix[i]!).bits.toNat) :
    Zlib.InffixedH.lenfix[j]! = Zlib.InffixedH.lenfix[i]! := by
  let e := Zlib.InffixedH.lenfix[i]!
  have width := lenfix_widths ⟨i, ib⟩
  change 7 ≤ e.bits.toNat ∧ e.bits.toNat ≤ 9 at width
  change i % 2 ^ e.bits.toNat = j % 2 ^ e.bits.toNat at same
  have casesWidth : e.bits.toNat = 7 ∨ e.bits.toNat = 8 ∨ e.bits.toNat = 9 := by omega
  rcases casesWidth with w7 | w8 | w9
  · have rep := (lenfix_replicated ⟨i, ib⟩).1 w7
    have residue : i % 128 = j % 128 := by simpa [w7] using same
    have quotient : j / 128 < 4 := by omega
    have h : Zlib.InffixedH.lenfix[j]? = some e := by
      rcases rep with ⟨r0,r1,r2,r3⟩
      have qcases : j / 128 = 0 ∨ j / 128 = 1 ∨ j / 128 = 2 ∨ j / 128 = 3 := by omega
      rcases qcases with q | q | q | q
      · have eqj : j = i % 128 := by omega
        simpa [eqj] using r0
      · have eqj : j = i % 128 + 128 := by omega
        simpa [eqj] using r1
      · have eqj : j = i % 128 + 256 := by omega
        simpa [eqj] using r2
      · have eqj : j = i % 128 + 384 := by omega
        simpa [eqj] using r3
    change Zlib.InffixedH.lenfix[j]! = e
    simp [getElem!_def, h]
  · have rep := (lenfix_replicated ⟨i, ib⟩).2 w8
    have residue : i % 256 = j % 256 := by simpa [w8] using same
    have quotient : j / 256 < 2 := by omega
    have h : Zlib.InffixedH.lenfix[j]? = some e := by
      rcases rep with ⟨r0,r1⟩
      have qcases : j / 256 = 0 ∨ j / 256 = 1 := by omega
      rcases qcases with q | q
      · have eqj : j = i % 256 := by omega
        simpa [eqj] using r0
      · have eqj : j = i % 256 + 256 := by omega
        simpa [eqj] using r1
    change Zlib.InffixedH.lenfix[j]! = e
    simp [getElem!_def, h]
  · have eqij : i = j := by simpa [w9, Nat.mod_eq_of_lt ib, Nat.mod_eq_of_lt jb] using same
    subst j
    rfl

theorem lenfix_stable_query :
    StableQuery LENS Zlib.InffixedH.lenfix 0 9 := by
  intro inp entry consumed query fits more
  have enough1 : 9 ≤ (Zlib.Inftrees.Spec.DecodeShort.padded inp).length := by
    have h := Zlib.Inftrees.Proofs.padded_length inp
    omega
  have enough2 : 9 ≤ (Zlib.Inftrees.Spec.DecodeShort.padded (inp ++ more)).length := by
    have h := Zlib.Inftrees.Proofs.padded_length (inp ++ more)
    omega
  obtain ⟨i, rest1, read1, bound1, _⟩ :=
    ZlibF.Math.InflateDecode.read_total 9 _ enough1
  obtain ⟨j, rest2, read2, bound2, _⟩ :=
    ZlibF.Math.InflateDecode.read_total 9 _ enough2
  have ib : i < 512 := by simpa using bound1
  have jb : j < 512 := by simpa using bound2
  have first := lenfix_query_index i ib _ rest1 read1
  have second := lenfix_query_index j jb _ rest2 read2
  have pairEq := Option.some.inj (query.symm.trans first)
  have entryEq : entry = Zlib.InffixedH.lenfix[i]! := congrArg Prod.fst pairEq
  have consumedEq : consumed = (Zlib.InffixedH.lenfix[i]!).bits.toNat :=
    congrArg Prod.snd pairEq
  have usedBound : consumed ≤ 9 := by
    rw [consumedEq]
    exact (lenfix_widths ⟨i, ib⟩).2
  have residue := padded_index_residue 9 consumed inp more (by decide) usedBound
    fits i j rest1 rest2 read1 read2
  rw [consumedEq] at residue
  have cells := lenfix_same_of_residue i j ib jb residue
  rw [cells] at second
  rw [←entryEq] at second
  have usedEq : consumed = entry.bits.toNat := by rw [entryEq]; exact consumedEq
  rw [usedEq]
  exact second

theorem distfix_stable_query :
    StableQuery DISTS Zlib.InffixedH.distfix 0 5 := by
  intro inp entry consumed query fits more
  have enough1 : 5 ≤ (Zlib.Inftrees.Spec.DecodeShort.padded inp).length := by
    have h := Zlib.Inftrees.Proofs.padded_length inp
    omega
  have enough2 : 5 ≤ (Zlib.Inftrees.Spec.DecodeShort.padded (inp ++ more)).length := by
    have h := Zlib.Inftrees.Proofs.padded_length (inp ++ more)
    omega
  obtain ⟨i, rest1, read1, bound1, _⟩ :=
    ZlibF.Math.InflateDecode.read_total 5 _ enough1
  obtain ⟨j, rest2, read2, bound2, _⟩ :=
    ZlibF.Math.InflateDecode.read_total 5 _ enough2
  have ib : i < 32 := by simpa using bound1
  have jb : j < 32 := by simpa using bound2
  have first := distfix_query_index i ib _ rest1 read1
  have second := distfix_query_index j jb _ rest2 read2
  have pairEq := Option.some.inj (query.symm.trans first)
  have entryEq : entry = Zlib.InffixedH.distfix[i]! := congrArg Prod.fst pairEq
  have consumedEq : consumed = (Zlib.InffixedH.distfix[i]!).bits.toNat :=
    congrArg Prod.snd pairEq
  have rootUsed : consumed = 5 := by
    rw [consumedEq]
    exact distfix_widths ⟨i, ib⟩
  have residue := padded_index_residue 5 consumed inp more (by decide)
    (by omega) fits i j rest1 rest2 read1 read2
  have ij : i = j := by
    rw [rootUsed] at residue
    simpa [Nat.mod_eq_of_lt ib, Nat.mod_eq_of_lt jb] using residue
  subst j
  rw [←entryEq] at second
  have usedEq : consumed = entry.bits.toNat := by rw [entryEq]; exact consumedEq
  rw [usedEq]
  exact second

#print axioms lenfix_widths
#print axioms lenfix_replicated
#print axioms distfix_widths
#print axioms lenfix_size
#print axioms distfix_size
#print axioms lenfix_query_index
#print axioms distfix_query_index
#print axioms padded_index_residue
#print axioms lenfix_same_of_residue
#print axioms lenfix_stable_query
#print axioms distfix_stable_query
end Zlib.InffixedH.Proofs
