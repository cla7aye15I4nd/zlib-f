import ZlibF.Proof.«inflate.c.dynamic-tail-reject-anchored»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.ActualHeader Zlib.Inflate.Proofs.WholeEpoch
open ZlibF.Math.InflateHuffmanBodyContext ZlibF.Math.HeaderConsumedReplay
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem zero_alphabet_decode_impossible {alphabet : List Nat} {input rest : List Bool} {symbol : Nat}
    (zero : ∀ length∈alphabet,length=0)
    (read : decodeSym alphabet input=some (symbol,rest)) : False := by
  obtain ⟨inside,nonzero,_source,_tail⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix read
  have member : alphabet.getD symbol 0∈alphabet := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]
    exact List.getElem_mem inside
  exact nonzero (zero _ member)

theorem zero_alphabet_codelens_impossible {alphabet : List Nat} {input rest : List Bool} {decoded : List Nat} {total : Nat}
    (zero : ∀ length∈alphabet,length=0) (positive : 0<total)
    (parsed : CodeLens alphabet total [] input rest decoded) : False := by
  cases parsed with
  | done count => simp only [List.length_nil] at count;omega
  | len _ read _ _ => exact zero_alphabet_decode_impossible zero read
  | rep16 _ read _ _ _ _ => exact zero_alphabet_decode_impossible zero read
  | rep17 _ read _ _ _ => exact zero_alphabet_decode_impossible zero read
  | rep18 _ read _ _ _ => exact zero_alphabet_decode_impossible zero read

/-- CODES refusal and all-zero CODES acceptance both preclude an
independent valid dynamic header. The byte reader may still wait after
installing an empty root, so this is a source rejection certificate rather
than a fabricated BAD execution. -/
theorem alphabet_no_header
    {input r1 r2 r3 codeInput : List Bool} {hlit hdist hclen : Nat} {alphabet : List Nat}
    (first : readBits 5 input=some (hlit,r1)) (second : readBits 5 r1=some (hdist,r2))
    (third : readBits 4 r2=some (hclen,r3))
    (readAlphabet : readCodeLenLens (hclen+4) r3=some (alphabet,codeInput))
    (invalid : (¬Acceptable .codeLength alphabet) ∨ (∀ length∈alphabet,length=0)) :
    ∃ word,input=word++codeInput ∧ NoHeaderExtension word := by
  obtain ⟨w1,source1,replay1⟩ := readBits_consumed_word first
  obtain ⟨w2,source2,replay2⟩ := readBits_consumed_word second
  obtain ⟨w3,source3,replay3⟩ := readBits_consumed_word third
  obtain ⟨wa,sourceA,replayA⟩ := readCodeLenLens_consumed_word readAlphabet
  refine ⟨w1++w2++w3++wa,?_,?_⟩
  · rw [source1,source2,source3,sourceA];simp only [List.append_assoc]
  · intro future L D rest header
    cases header with
    | dynamic a b d _counts ar accepted parsed _eob _vl _vd =>
      simp only [List.append_assoc] at a
      rw [replay1] at a
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj a)
      rw [replay2] at b
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj b)
      rw [replay3] at d
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj d)
      rw [replayA] at ar
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ar)
      rcases invalid with bad | zero
      · exact bad accepted
      · exact zero_alphabet_codelens_impossible zero (by omega) parsed

#print axioms zero_alphabet_decode_impossible
#print axioms zero_alphabet_codelens_impossible
#print axioms alphabet_no_header
end Zlib.Inflate.Proofs.DynamicRejects
