import ZlibF.Proof.«inflate.c.slow-distance-extra-semantic»
import ZlibF.Proof.«inflate.c.slow-distance-semantic»

namespace Zlib.Inflate.Proofs.SlowExtraSemanticPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inflate.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The complete actual slow distance decoding source, including both table
levels and independent extra bits, reaches the real MATCH continuation with
its exact distance. No desired callee result is assumed. -/
theorem DIST_to_MATCH_read_semantics
    (before : Nat) {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol value : Nat} {codeRest rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, codeRest)) (valid : symbol ≤ 29)
    (read : readBits (distExtras.getD symbol 0) codeRest = some (value, rest)) :
    ∃ regs after state used,
      runX (inflate_DIST c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = rest ∧
      state.offset.toNat = distBases.getD symbol 0 + value ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 32768 ∧
      distBases.getD symbol 0 + value < 2 ^ 32 ∧
      state.back = Int32.ofNat (before + alphabet.getD symbol 0 + distExtras.getD symbol 0) ∧
      after = setI h zs state ∧ regs.next = inputAdvance l.next used := by
  obtain ⟨middle, firstUsed, firstHeap, firstState, firstRun, _four, firstBound,
    firstGood, firstTables, firstB, firstRest, firstMode, base, width,
    firstBack, firstFrame, firstShape, firstCursor, firstHeapEq⟩ :=
    SlowDistanceSemanticPath.inflate_DIST_symbol_fields before E good tables pointer tableGet meaning stable B back backBound decoded valid
  have codeBound : alphabet.getD symbol 0 ≤ 15 := by
    by_cases inside : symbol < alphabet.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact meaning.acceptable.1 _ (List.getElem_mem inside)
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : alphabet.length ≤ symbol), Option.getD_none]
      decide
  have readCurrent : readBits (distExtras.getD symbol 0) (stream middle (bs.drop firstUsed)) = some (value, rest) := by
    simpa only [← firstRest] using read
  obtain ⟨regs, after, state, secondUsed, secondRun, secondBound, finalGood,
    finalTables, finalB, finalMode, secondFrame, secondShape, finalRest,
    exactOffset, stateEq, lower, upper, noWrap, finalHeapEq, finalCursor, _bits⟩ :=
    DISTEXT_symbol_read_semantics (before + alphabet.getD symbol 0) E.strm E.st
      firstGood firstTables firstB valid base width firstBack (by omega) readCurrent
  have dropEq : (bs.drop firstUsed).drop secondUsed = bs.drop (firstUsed + secondUsed) := by
    rw [List.drop_drop, Nat.add_comm]
  have finalBack : state.back = Int32.ofNat (before + alphabet.getD symbol 0 + distExtras.getD symbol 0) := by
    rw [stateEq]
    simp only [width]
  refine ⟨regs, after, state, firstUsed + secondUsed, firstRun.trans secondRun, ?_,
    finalGood, finalTables, ?_, finalMode, firstFrame.trans secondFrame,
    firstShape.trans secondShape, ?_, exactOffset, lower, upper, noWrap,
    finalBack, ?_, ?_⟩
  · have bound := secondBound
    simp only [List.length_drop] at bound
    omega
  · simpa only [dropEq] using finalB
  · simpa only [dropEq] using finalRest
  · rw [finalHeapEq, firstHeapEq, setI_setI]
  · rw [finalCursor, firstCursor, inputAdvance_add]

#print axioms DIST_to_MATCH_read_semantics
end Zlib.Inflate.Proofs.SlowExtraSemanticPath
