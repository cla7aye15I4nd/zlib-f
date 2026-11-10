import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface»
import ZlibF.Proof.«inflate.c.whole-epoch-block-transitions»
import ZlibF.Proof.«inflate.c.stored-causal-resume»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.StoredCausal
set_option autoImplicit false

/-- The actual stored phase is the only source constructor at COPY entry. -/
theorem SourcePhase.stored_copy_fields {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = COPY_ ∨ s.mode = COPY) :
    Nonempty (StoredCopy log s wire) := by
  rcases mode with mode | mode <;> cases phase <;>
    simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
      STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH,
      CHECK, LENGTH, BAD, MEM, DONE]
  all_goals exact ⟨by assumption⟩

/-- Accepted actual LEN/NLEN and observed copied bytes replay a stored
body for every byte-position-compatible suffix, without valid-source input. -/
theorem StoredCopy.completed_body_bits
    {log : DataLog} {s : InflateState} {wire tail : List Bool}
    (stored : StoredCopy log s wire) (zero : s.length = 0) (aligned : tail.length % 8 = 0) :
    Body stored.block.wrapper.dictionary 0 stored.block.before
      ((stored.padding ++ stored.word ++ bytesBits stored.copied) ++ tail) tail log.output := by
  have count : stored.copied.length = stored.len := by
    have debt := stored.debt
    rw [zero] at debt
    simpa only [UInt32.toNat_zero, Nat.zero_add] using debt
  have alignment : ((stored.padding ++ stored.word ++ bytesBits stored.copied) ++ tail).length % 8 = stored.padding.length := by
    have wordSize := stored.size
    have short := stored.shortPadding
    simp only [List.length_append, bytesBits_length]
    omega
  have drop : ((stored.padding ++ stored.word ++ bytesBits stored.copied) ++ tail).drop stored.padding.length =
      stored.word ++ (bytesBits stored.copied ++ tail) := by
    rw [List.append_assoc, List.append_assoc, List.drop_left]
  have first := stored_readBits_append stored.first (bytesBits stored.copied ++ tail)
  have second := stored_readBits_append stored.second (bytesBits stored.copied ++ tail)
  simp only [List.nil_append] at second
  have payload : readBytes stored.len (bytesBits stored.copied ++ tail) = some (stored.copied, tail) := by
    rw [← count]
    simpa only [bytesBits_eq_bytesToBits] using Zlib.Trees.Proofs.Out.readBytes_encoded stored.copied tail
  rw [stored.output]
  apply Body.stored (len := stored.len) (nlen := stored.nlen)
    (r1 := stored.middle ++ (bytesBits stored.copied ++ tail))
    (r2 := bytesBits stored.copied ++ tail)
  · rw [alignment, drop]
    exact first
  · exact second
  · exact stored.complement
  · exact payload

/-- The zero COPY dispatch selects the causal next-block or final-block
constructor from its observed BFINAL, never an expected END outcome. -/
theorem StoredCopy.completed_phase
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (stored : StoredCopy log s wire) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (zero : s.length = 0) (credit : CausalInput.Credited log.input wire s.bits s.hold) :
    Nonempty (SourcePhase log s wire) := by
  have wireAligned : wire.length % 8 = 0 := by
    have source := congrArg List.length credit
    change (bytesBits log.input).length = (wire ++ natBits s.bits.toNat s.hold.toNat).length at source
    simp only [List.length_append, bytesBits_length, natBits_length, stored.bits, UInt32.toNat_zero] at source
    omega
  let bodyWord := stored.padding ++ stored.word ++ bytesBits stored.copied
  let blockWord := stored.block.previous ++ stored.block.tag ++ bodyWord
  have currentAligned : blockWord.length % 8 = 0 := by
    have counts := congrArg List.length stored.anchor
    simp only [BlockStart.prefix, List.length_append, bytesBits_length] at counts
    change (stored.block.previous ++ stored.block.tag ++ (stored.padding ++ stored.word ++ bytesBits stored.copied)).length % 8 = 0
    simp only [List.length_append, bytesBits_length]
    omega
  have body : ∀ tail, (stored.block.previous.length + stored.block.tag.length + bodyWord.length + tail.length) % 8 = 0 →
      Body stored.block.wrapper.dictionary stored.block.kind stored.block.before (bodyWord ++ tail) tail log.output := by
    intro tail alignment
    have tailAligned : tail.length % 8 = 0 := by
      simp only [blockWord, List.length_append] at currentAligned
      omega
    rw [stored.stored]
    exact stored.completed_body_bits zero tailAligned
  have anchor : wire = bytesBits stored.block.wrapper.bytes ++ blockWord := by
    simpa only [blockWord, bodyWord, BlockStart.prefix, List.append_assoc] using stored.anchor
  by_cases final : stored.block.last = 0
  · have context := stored.block.advance final body
    exact ⟨.tag stored.block.wrapper blockWord mode (by rw [stored.last, final]; rfl) context anchor⟩
  · have one : stored.block.last = 1 := by have bound := stored.block.finalBound; omega
    have closed := stored.block.finish one body
    exact ⟨.afterBlocks mode (by rw [stored.last, one]; decide)
      ⟨stored.block.wrapper, blockWord, closed, anchor⟩⟩

#print axioms SourcePhase.stored_copy_fields
#print axioms StoredCopy.completed_body_bits
#print axioms StoredCopy.completed_phase
end Zlib.Inflate.Proofs.WholeEpoch
