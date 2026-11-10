import ZlibF.Math.«whole-epoch-wrapper-prefix»
import ZlibF.Math.«whole-epoch-original-valid-body»
import ZlibF.Proof.Format.Token

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs
open ZlibF.Math.InflateHuffmanBodyContext ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- A rejected residual token is replayed through the real accepted
header and all already committed tokens. The committed word itself need
not be a single token and is never asserted to be rejected. -/
theorem Compressed.no_body_extension
    {dictionary history : List UInt8} {wire badCredit : List Bool}
    (boundary : Compressed dictionary wire history)
    (rejected : ∀ future rest output,
      ¬ Symbols boundary.L boundary.D boundary.block.wrapper.dictionary
        history (badCredit ++ future) rest output)
    (future rest : List Bool) (output : List UInt8) :
    ¬ Body boundary.block.wrapper.dictionary boundary.block.kind boundary.block.before
      ((boundary.headerWord ++ boundary.tokenWord ++ badCredit) ++ future) rest output := by
  intro body
  have parsed := (boundary.header.append
    (boundary.tokenWord ++ (badCredit ++ future))).body_iff.mp
      (by simpa only [List.append_assoc] using body)
  simp only [List.nil_append] at parsed
  exact rejected future rest output
    ((boundary.committed.future (badCredit ++ future) rest output).mp parsed)

/-- Credited bytes, including retained lookahead, rule out every later
RFC input extension when the current residual token cannot parse.
The accepted wrapper, previous blocks, header and committed tokens are
replayed from their source contexts. No valid future is assumed. -/
theorem Compressed.rejects_credited
    {log : DataLog} {history : List UInt8} {wire badCredit : List Bool}
    (boundary : Compressed log.dictionary wire history)
    (source : bytesBits log.input = wire ++ badCredit)
    (rejected : ∀ future rest output,
      ¬ Symbols boundary.L boundary.D boundary.block.wrapper.dictionary
        history (badCredit ++ future) rest output) : Rejects log := by
  let block := boundary.block
  let word := boundary.headerWord ++ boundary.tokenWord ++ badCredit
  have anchor : bytesBits log.input = bytesBits block.wrapper.bytes ++
      (block.previous ++ block.tag ++ word) := by
    rw [boundary.anchor] at source
    simpa only [block, word, BlockStart.prefix, List.append_assoc] using source
  intro future output valid
  obtain ⟨bodyBytes, original, bodySource⟩ :=
    block.wrapper.source_bytes (future := future) anchor
  rw [original] at valid
  obtain ⟨rest, blocks, _trailer⟩ := block.wrapper.original_valid_body valid
  have bitSource : bytesToBits bodyBytes =
      block.previous ++ (block.tag ++ (word ++ bytesBits future)) := by
    simpa only [bytesBits_eq_bytesToBits, List.append_assoc] using bodySource
  rw [bitSource] at blocks
  have aligned :
      (block.previous.length + (block.tag ++ (word ++ bytesBits future)).length) % 8 = 0 := by
    have sizes := congrArg List.length bitSource
    simp only [bytesBits_eq_bytesToBits, bytesBits_length, List.length_append] at sizes
    simp only [List.length_append]
    have futureSize := bytesBits_length future
    omega
  have remaining :=
    (block.context (block.tag ++ (word ++ bytesBits future)) rest output aligned).mp blocks
  have finalRead := readBits_append _ _ _ _ (word ++ bytesBits future) block.finalRead
  have typeRead := readBits_append _ _ _ _ (word ++ bytesBits future) block.typeRead
  have noBody {tail : List Bool} {decoded : List UInt8}
      (body : Body block.wrapper.dictionary block.kind block.before
        (word ++ bytesBits future) tail decoded) : False := by
    exact boundary.no_body_extension rejected (bytesBits future) tail decoded body
  cases remaining with
  | last actualFinal actualType body =>
    obtain ⟨_last, inputEq⟩ :=
      Prod.mk.inj (Option.some.inj (finalRead.symm.trans actualFinal))
    rw [← inputEq] at actualType
    have typeRead0 : readBits 2 (block.middle ++ (word ++ bytesBits future)) =
        some (block.kind, word ++ bytesBits future) := by
      simpa only [List.nil_append] using typeRead
    obtain ⟨kindEq, bodyEq⟩ :=
      Prod.mk.inj (Option.some.inj (typeRead0.symm.trans actualType))
    rw [← kindEq, ← bodyEq] at body
    exact noBody body
  | more actualFinal actualType body _tail =>
    obtain ⟨_last, inputEq⟩ :=
      Prod.mk.inj (Option.some.inj (finalRead.symm.trans actualFinal))
    rw [← inputEq] at actualType
    have typeRead0 : readBits 2 (block.middle ++ (word ++ bytesBits future)) =
        some (block.kind, word ++ bytesBits future) := by
      simpa only [List.nil_append] using typeRead
    obtain ⟨kindEq, bodyEq⟩ :=
      Prod.mk.inj (Option.some.inj (typeRead0.symm.trans actualType))
    rw [← kindEq, ← bodyEq] at body
    exact noBody body

/-- An independently rejected current token on every extension supplies
the residual premise. Previously committed tokens remain a context. -/
theorem Compressed.rejected_token_rejects_credited
    {log : DataLog} {history : List UInt8} {wire badCredit : List Bool}
    (boundary : Compressed log.dictionary wire history)
    (source : bytesBits log.input = wire ++ badCredit)
    (rejected : ∀ future, Token.Rejected boundary.L boundary.D
      boundary.block.wrapper.dictionary history (badCredit ++ future)) : Rejects log := by
  apply boundary.rejects_credited source
  intro future rest output
  exact Token.rejected_has_no_symbols _ _ _ _ _ (rejected future) rest output

#print axioms Compressed.no_body_extension
#print axioms Compressed.rejects_credited
#print axioms Compressed.rejected_token_rejects_credited
end Zlib.Inflate.Proofs.WholeEpoch
