import ZlibF.Proof.«inflate.c.whole-epoch-block-transitions»
import ZlibF.Math.«committed-token-segment-join»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs
open ZlibF.Math.InflateHuffmanBodyContext ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false

/-- A finite actual non-EOB fast/slow segment extends the enclosing block
word. Starting a new fast call never resets the earlier block grammar. -/
def Compressed.advance_segment {dictionary history next : List UInt8} {wire word : List Bool}
    (before : Compressed dictionary wire history)
    (segment : Committed before.L before.D before.block.wrapper.dictionary history word next) :
    Compressed dictionary (wire ++ word) next := {
  block := before.block
  L := before.L
  D := before.D
  headerWord := before.headerWord
  header := before.header
  validL := before.validL
  validD := before.validD
  tokenWord := before.tokenWord ++ word
  committed := before.committed.trans segment
  anchor := by simpa only [List.append_assoc] using congrArg (fun prior => prior ++ word) before.anchor
}

/-- A multi-token segment ending in EOB closes the original block. It is
Symbols, not one Token.Step: previous accepted tokens remain explicit. -/
theorem Compressed.finish_segment {dictionary history next : List UInt8} {wire word : List Bool}
    (before : Compressed dictionary wire history)
    (segment : Symbols before.L before.D before.block.wrapper.dictionary history word [] next) :
    ∀ tail, Body before.block.wrapper.dictionary before.block.kind before.block.before
      ((before.headerWord ++ before.tokenWord ++ word) ++ tail) tail next := by
  intro tail
  have symbols := before.committed.complete_segment segment
  have extended := symbols.append (ext_acceptable before.validL) (ext_acceptable before.validD) tail
  have header := before.header.append ((before.tokenWord ++ word) ++ tail)
  simpa only [List.append_assoc, List.nil_append] using header.body_iff.mpr extended

/-- Actual EOB from a later finite segment updates the finite epoch phase,
including a transition to another block in this same call. -/
def Compressed.ended_phase {log : DataLog} {s : InflateState} {history : List UInt8} {wire word : List Bool}
    (before : Compressed log.dictionary wire history)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = Int32.ofNat before.block.last)
    (segment : Symbols before.L before.D before.block.wrapper.dictionary history word [] log.output) :
    SourcePhase log s (wire ++ word) := by
  let bodyWord := before.headerWord ++ before.tokenWord ++ word
  let blockWord := before.block.previous ++ before.block.tag ++ bodyWord
  have body := before.finish_segment segment
  by_cases final : before.block.last = 0
  · refine .tag before.block.wrapper blockWord mode ?_
      (before.block.advance final (fun tail _alignment => body tail)) ?_
    · rw [last, final]; rfl
    · simpa only [BlockStart.prefix, bodyWord, blockWord, List.append_assoc] using
        congrArg (fun prior => prior ++ word) before.anchor
  · have one : before.block.last = 1 := by have bound := before.block.finalBound; omega
    refine .afterBlocks mode ?_ ⟨before.block.wrapper, blockWord,
      before.block.finish one (fun tail _alignment => body tail), ?_⟩
    · rw [last, one]; decide
    · simpa only [BlockStart.prefix, bodyWord, blockWord, List.append_assoc] using
        congrArg (fun prior => prior ++ word) before.anchor

#print axioms Compressed.advance_segment
#print axioms Compressed.finish_segment
#print axioms Compressed.ended_phase
end Zlib.Inflate.Proofs.WholeEpoch
