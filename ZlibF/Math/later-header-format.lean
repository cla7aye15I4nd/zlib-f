import ZlibF.Math.InflateHuffmanBodyContext
namespace Zlib.Inflate.Proofs.LaterHeader
open ZlibF.Spec ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false

theorem dynamic_header_fields {input payload : List Bool} {L D : List Nat}
    (header : Header 2 input L D payload) :
    ∃ hlit hdist hclen firstRest secondRest thirdRest alphabet alphabetRest decoded,
      readBits 5 input = some (hlit, firstRest) ∧ readBits 5 firstRest = some (hdist, secondRest) ∧
      readBits 4 secondRest = some (hclen, thirdRest) ∧ DynamicCountsOK hlit hdist ∧
      readCodeLenLens (hclen + 4) thirdRest = some (alphabet, alphabetRest) ∧ Acceptable .codeLength alphabet ∧
      CodeLens alphabet (hlit + 257 + (hdist + 1)) [] alphabetRest payload decoded ∧
      HasEndOfBlock (decoded.take (hlit + 257)) ∧ Acceptable .litLen (decoded.take (hlit + 257)) ∧
      Acceptable .dist (decoded.drop (hlit + 257)) ∧ L = decoded.take (hlit + 257) ∧ D = decoded.drop (hlit + 257) := by
  cases header with
  | dynamic first second third counts alphabet valid parsed eob validL validD =>
    exact ⟨_, _, _, _, _, _, _, _, _, first, second, third, counts, alphabet, valid, parsed, eob, validL, validD, rfl, rfl⟩

#print axioms dynamic_header_fields
end Zlib.Inflate.Proofs.LaterHeader
