import ZlibF.Proof.«inflate.c.whole-epoch-source-spine»
import ZlibF.Math.HeaderConsumedReplay
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs
open ZlibF.Math.InflateHuffmanBodyContext ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false

/-- A source-produced complete nonfinal block advances the same finite
prefix context. Stored-byte alignment is stated at the complete source. -/
theorem BlockStart.advance {dictionary output : List UInt8} (block : BlockStart dictionary)
    {word : List Bool} (last : block.last = 0)
    (body : ∀ tail, (block.previous.length + block.tag.length + word.length + tail.length) % 8 = 0 →
      Body block.wrapper.dictionary block.kind block.before (word ++ tail) tail output) :
    BlocksPrefix block.wrapper.dictionary (block.previous ++ block.tag ++ word) output := by
  intro future rest decoded alignment
  have lengths : (block.previous.length + block.tag.length + word.length + future.length) % 8 = 0 := by
    simpa only [List.length_append] using alignment
  have first := readBits_append 1 block.tag block.last block.middle (word ++ future) block.finalRead
  have second := readBits_append 2 block.middle block.kind [] (word ++ future) block.typeRead
  rw [last] at first
  have tail := body future lengths
  have accepted := ZlibF.Math.InflateBlockContext.nonfinal_body_iff (rest := rest) (output := decoded) first
    (by simpa only [List.nil_append] using second) tail
  have original := block.context (block.tag ++ word ++ future) rest decoded
    (by simpa only [List.length_append, Nat.add_assoc] using lengths)
  simp only [List.append_assoc] at original
  simpa only [List.append_assoc] using original.trans accepted

/-- A source-produced final block closes the original Blocks grammar,
retaining arbitrary byte-position-compatible suffixes. -/
theorem BlockStart.finish {dictionary output : List UInt8} (block : BlockStart dictionary)
    {word : List Bool} (last : block.last = 1)
    (body : ∀ tail, (block.previous.length + block.tag.length + word.length + tail.length) % 8 = 0 →
      Body block.wrapper.dictionary block.kind block.before (word ++ tail) tail output) :
    ∀ tail, ((block.previous ++ block.tag ++ word).length + tail.length) % 8 = 0 →
      Blocks block.wrapper.dictionary [] ((block.previous ++ block.tag ++ word) ++ tail) tail output := by
  intro future alignment
  have lengths : (block.previous.length + block.tag.length + word.length + future.length) % 8 = 0 := by
    simpa only [List.length_append] using alignment
  have first := readBits_append 1 block.tag block.last block.middle (word ++ future) block.finalRead
  have second := readBits_append 2 block.middle block.kind [] (word ++ future) block.typeRead
  rw [last] at first
  have final : Blocks block.wrapper.dictionary block.before (block.tag ++ (word ++ future)) future output :=
    .last first (by simpa only [List.nil_append] using second) (body future lengths)
  have original := (block.context (block.tag ++ word ++ future) future output
    (by simpa only [List.length_append, Nat.add_assoc] using lengths)).mpr
      (by simpa only [List.append_assoc] using final)
  simpa only [List.append_assoc] using original

/-- The actual finite EOB token closes the accepted compressed body.
Future bits remain arbitrary; neither validity nor target output is assumed. -/
theorem Compressed.finish {dictionary history next : List UInt8} {wire input rest : List Bool}
    (boundary : Compressed dictionary wire history)
    (eob : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary history input rest next true) :
    ∃ word, input = word ++ rest ∧ next = history ∧
      ∀ tail, Body boundary.block.wrapper.dictionary boundary.block.kind boundary.block.before
        ((boundary.headerWord ++ boundary.tokenWord ++ word) ++ tail) tail history := by
  obtain ⟨word, source, same, symbols⟩ := boundary.committed.finish boundary.validL boundary.validD eob
  subst next
  refine ⟨word, source, rfl, ?_⟩
  intro tail
  have parsed := symbols.append (ext_acceptable boundary.validL) (ext_acceptable boundary.validD) tail
  have header := boundary.header.append ((boundary.tokenWord ++ word) ++ tail)
  simpa only [List.nil_append, List.append_nil, List.append_assoc] using header.body_iff.mpr parsed

/-- The same accepted EOB routes the finite global spine by the actual
BFINAL bit. Only the consumed token word is added to the credited source. -/
theorem Compressed.eob_phase {log : DataLog} {s : InflateState} {wire input rest : List Bool}
    (boundary : Compressed log.dictionary wire log.output)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (last : s.last = Int32.ofNat boundary.block.last)
    (eob : Token.Step boundary.L boundary.D boundary.block.wrapper.dictionary log.output input rest log.output true) :
    ∃ word, input = word ++ rest ∧ Nonempty (SourcePhase log s (wire ++ word)) := by
  obtain ⟨word, source, _same, body⟩ := boundary.finish eob
  let bodyWord := boundary.headerWord ++ boundary.tokenWord ++ word
  let blockWord := boundary.block.previous ++ boundary.block.tag ++ bodyWord
  by_cases final : boundary.block.last = 0
  · have next := boundary.block.advance final (fun tail _alignment => body tail)
    refine ⟨word, source, ⟨.tag boundary.block.wrapper blockWord mode ?_ next ?_⟩⟩
    · rw [last, final]
      rfl
    · simpa only [BlockStart.prefix, bodyWord, blockWord, List.append_assoc] using
        congrArg (fun prior => prior ++ word) boundary.anchor
  · have one : boundary.block.last = 1 := by have bound := boundary.block.finalBound; omega
    have closed := boundary.block.finish one (fun tail _alignment => body tail)
    let complete : CompletedBody log (wire ++ word) :=
      ⟨boundary.block.wrapper, blockWord, closed,
        by simpa only [BlockStart.prefix, bodyWord, blockWord, List.append_assoc] using
          congrArg (fun prior => prior ++ word) boundary.anchor⟩
    refine ⟨word, source, ⟨.afterBlocks mode ?_ complete⟩⟩
    rw [last, one]
    decide

#print axioms BlockStart.advance
#print axioms BlockStart.finish
#print axioms Compressed.finish
#print axioms Compressed.eob_phase
end Zlib.Inflate.Proofs.WholeEpoch
