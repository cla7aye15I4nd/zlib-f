import ZlibF.Proof.«inflate.c.slow-distance-extra-semantic»
import ZlibF.Proof.«inflate.c.slow-input-fragment»

namespace Zlib.Inflate.Proofs.SlowArbitrarySource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowExtraSemanticPath
set_option autoImplicit false

/-- On arbitrary current input LENEXT either really waits without committing
its scalar fields or reads exactly the independent prefix and reaches DIST.
No valid token or future-source parse is assumed. -/
theorem LENEXT_current_source {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 5)
    (lower : 3 ≤ s.length.toNat) (budget : s.length.toNat + 2 ^ s.extra.toNat ≤ 259)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 15) :
    (∃ regs, InputWait (inflate_LENEXT c) h h l bs [] (stream l bs) regs) ∨
    (∃ value rest regs after state used,
      readBits s.extra.toNat (stream l bs) = some (value, rest) ∧
      value < 2 ^ s.extra.toNat ∧
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DIST ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = rest ∧
      state.was = state.length ∧ state.length.toNat = s.length.toNat + value ∧
      3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ after = setI h zs state ∧
      regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 12) := by
  have size : (stream l bs).length = l.bits.toNat + 8 * bs.length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
  by_cases enough : s.extra.toNat ≤ (stream l bs).length
  · obtain ⟨value, rest, read, bound, _exactSource⟩ := ZlibF.Math.InflateDecode.read_total _ _ enough
    obtain ⟨regs, after, state, used, actual, usedBound, current, currentTables,
      currentBits, mode, frame, shape, _drop, was, length, restEq, lo, hi,
      nextBack, heap, cursor, bitBound⟩ := LENEXT_read_semantics before E.strm E.st good tables B
        extra lower budget back backBound read
    exact Or.inr ⟨value, rest, regs, after, state, used, read, bound, actual, usedBound,
      current, currentTables, currentBits, mode, frame, shape, restEq, was, length,
      lo, hi, nextBack, heap, cursor, bitBound⟩
  · left
    exact LENEXT_fragment E B (by omega) (by omega)
      (by simp only [FutureSource, List.append_nil])

/-- DISTEXT has the corresponding arbitrary-input dichotomy and records
the actual independent extra value and exact MATCH distance. -/
theorem DISTEXT_current_source {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 13)
    (lower : 1 ≤ s.offset.toNat) (budget : s.offset.toNat + 2 ^ s.extra.toNat ≤ 32769)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 35) :
    (∃ regs, InputWait (inflate_DISTEXT c) h h l bs [] (stream l bs) regs) ∨
    (∃ value rest regs after state used,
      readBits s.extra.toNat (stream l bs) = some (value, rest) ∧
      value < 2 ^ s.extra.toNat ∧
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = rest ∧
      state.offset.toNat = s.offset.toNat + value ∧
      state = { s with offset := state.offset, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 32768 ∧
      after = setI h zs state ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ max l.bits.toNat 20) := by
  have size : (stream l bs).length = l.bits.toNat + 8 * bs.length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
  by_cases enough : s.extra.toNat ≤ (stream l bs).length
  · obtain ⟨value, rest, read, bound, _exactSource⟩ := ZlibF.Math.InflateDecode.read_total _ _ enough
    obtain ⟨regs, after, state, used, actual, usedBound, current, currentTables,
      currentBits, mode, frame, shape, restEq, offset, stateEq, lo, _hi,
      heap, cursor, bitBound⟩ := DISTEXT_read_semantics before E.strm E.st good tables B
        extra lower (by omega) back backBound read
    exact Or.inr ⟨value, rest, regs, after, state, used, read, bound, actual, usedBound,
      current, currentTables, currentBits, mode, frame, shape, restEq, offset, stateEq,
      lo, by omega, heap, cursor, bitBound⟩
  · left
    exact DISTEXT_fragment E B (by omega) (by omega)
      (by simp only [FutureSource, List.append_nil])

#print axioms LENEXT_current_source
#print axioms DISTEXT_current_source
end Zlib.Inflate.Proofs.SlowArbitrarySource
