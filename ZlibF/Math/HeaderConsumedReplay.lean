import ZlibF.Math.InflateHuffmanBodyContext
import ZlibF.Math.«code-length-prefix»

namespace ZlibF.Math.HeaderConsumedReplay
open ZlibF.Spec ZlibF.Spec.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false

theorem readBits_consumed_word {width value : Nat} {input rest : List Bool}
    (read : readBits width input = some (value, rest)) :
    ∃ word, input = word ++ rest ∧ ∀ suffix, readBits width (word ++ suffix) = some (value, suffix) := by
  obtain ⟨bound, source⟩ := CodeLengthPrefix.read_word read
  refine ⟨bitsOfNat value width, source, ?_⟩
  intro suffix
  simpa only [Nat.mod_eq_of_lt bound, Nat.sub_self, bitsOfNat_zero, List.nil_append] using
    readBits_bitsOfNat width width value suffix (Nat.le_refl width)

theorem readNats_consumed_word {width count : Nat} {input rest : List Bool} {values : List Nat}
    (read : readNats width count input = some (values, rest)) :
    ∃ word, input = word ++ rest ∧ ∀ suffix, readNats width count (word ++ suffix) = some (values, suffix) := by
  induction count generalizing input values rest with
  | zero =>
    simp only [readNats] at read
    cases read
    exact ⟨[], rfl, fun _ => rfl⟩
  | succ count ih =>
    cases first : readBits width input with
    | none => simp only [readNats, first] at read; cases read
    | some pair =>
      obtain ⟨value, middle⟩ := pair
      cases tail : readNats width count middle with
      | none => simp only [readNats, first, tail] at read; cases read
      | some pair =>
        obtain ⟨suffixValues, final⟩ := pair
        simp only [readNats, first, tail] at read
        cases read
        obtain ⟨firstWord, firstSource, firstReplay⟩ := readBits_consumed_word first
        obtain ⟨tailWord, tailSource, tailReplay⟩ := ih tail
        refine ⟨firstWord ++ tailWord, ?_, ?_⟩
        · rw [firstSource, tailSource, List.append_assoc]
        · intro suffix
          rw [List.append_assoc]
          simp only [readNats, firstReplay (tailWord ++ suffix), tailReplay suffix]

theorem readCodeLenLens_consumed_word {count : Nat} {input rest : List Bool} {alphabet : List Nat}
    (read : readCodeLenLens count input = some (alphabet, rest)) :
    ∃ word, input = word ++ rest ∧ ∀ suffix, readCodeLenLens count (word ++ suffix) = some (alphabet, suffix) := by
  unfold readCodeLenLens at read ⊢
  cases fields : readNats 3 count input with
  | none => simp only [fields] at read; cases read
  | some pair =>
    obtain ⟨values, remaining⟩ := pair
    simp only [fields] at read
    cases read
    obtain ⟨word, source, replay⟩ := readNats_consumed_word fields
    exact ⟨word, source, fun suffix => by rw [replay suffix]⟩

/-- A completed independent code-length parse consumes a fixed word,
including all repeat code and extra bits. It replays before any residual
suffix using only the accepted code-length alphabet. -/
theorem codeLens_consumed_word {alphabet acc decoded : List Nat} {total : Nat} {input rest : List Bool}
    (valid : Acceptable .codeLength alphabet) (parsed : CodeLens alphabet total acc input rest decoded) :
    ∃ word, input = word ++ rest ∧ ∀ suffix, CodeLens alphabet total acc (word ++ suffix) suffix decoded := by
  induction parsed with
  | done finished => exact ⟨[], rfl, fun _ => CodeLens.done finished⟩
  | @len before inp middle final symbol output more read small step ih =>
    obtain ⟨tail, tailSource, replay⟩ := ih
    have source := CodeLengthPrefix.decoded_word read
    obtain ⟨_inside, nonzero, _prefix, _rest⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix read
    have trace := CodeLengthPrefix.Trace.literal valid more nonzero small
    refine ⟨codeOf alphabet symbol ++ tail, ?_, ?_⟩
    · rw [source, tailSource, List.append_assoc]
    · intro suffix
      simpa only [List.append_assoc] using trace (tail ++ suffix) suffix _ (replay suffix)
  | @rep16 before inp middle extraRest final value output more read nonempty extra room step ih =>
    obtain ⟨tail, tailSource, replay⟩ := ih
    have source := CodeLengthPrefix.decoded_word read
    obtain ⟨_inside, nonzero, _prefix, _rest⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix read
    obtain ⟨bound, extraSource⟩ := CodeLengthPrefix.read_word extra
    have trace := CodeLengthPrefix.Trace.previous valid more nonzero nonempty bound room
    refine ⟨(codeOf alphabet 16 ++ bitsOfNat value 2) ++ tail, ?_, ?_⟩
    · rw [source, extraSource, tailSource]
      simp only [List.append_assoc]
    · intro suffix
      simpa only [List.append_assoc] using trace (tail ++ suffix) suffix _ (replay suffix)
  | @rep17 before inp middle extraRest final value output more read extra room step ih =>
    obtain ⟨tail, tailSource, replay⟩ := ih
    have source := CodeLengthPrefix.decoded_word read
    obtain ⟨_inside, nonzero, _prefix, _rest⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix read
    obtain ⟨bound, extraSource⟩ := CodeLengthPrefix.read_word extra
    have trace := CodeLengthPrefix.Trace.zero_short valid more nonzero bound room
    refine ⟨(codeOf alphabet 17 ++ bitsOfNat value 3) ++ tail, ?_, ?_⟩
    · rw [source, extraSource, tailSource]
      simp only [List.append_assoc]
    · intro suffix
      simpa only [List.append_assoc] using trace (tail ++ suffix) suffix _ (replay suffix)
  | @rep18 before inp middle extraRest final value output more read extra room step ih =>
    obtain ⟨tail, tailSource, replay⟩ := ih
    have source := CodeLengthPrefix.decoded_word read
    obtain ⟨_inside, nonzero, _prefix, _rest⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix read
    obtain ⟨bound, extraSource⟩ := CodeLengthPrefix.read_word extra
    have trace := CodeLengthPrefix.Trace.zero_long valid more nonzero bound room
    refine ⟨(codeOf alphabet 18 ++ bitsOfNat value 7) ++ tail, ?_, ?_⟩
    · rw [source, extraSource, tailSource]
      simp only [List.append_assoc]
    · intro suffix
      simpa only [List.append_assoc] using trace (tail ++ suffix) suffix _ (replay suffix)

end ZlibF.Math.HeaderConsumedReplay

namespace ZlibF.Math.InflateHuffmanBodyContext
open ZlibF.Spec ZlibF.Spec.Proofs ZlibF.Math.HeaderConsumedReplay
set_option autoImplicit false

/-- An accepted Huffman header determines its exact consumed word. The
same header replays before arbitrary residual input; no Symbols relation
or complete valid payload/future is assumed. -/
theorem Header.consumed_word {kind : Nat} {input payload : List Bool} {L D : List Nat}
    (header : Header kind input L D payload) :
    ∃ word, input = word ++ payload ∧ ∀ suffix, Header kind (word ++ suffix) L D suffix := by
  cases header with
  | fixed => exact ⟨[], rfl, fun _ => Header.fixed _⟩
  | dynamic first second third counts alphabet valid parsed eob validL validD =>
    obtain ⟨word1, source1, replay1⟩ := readBits_consumed_word first
    obtain ⟨word2, source2, replay2⟩ := readBits_consumed_word second
    obtain ⟨word3, source3, replay3⟩ := readBits_consumed_word third
    obtain ⟨wordA, sourceA, replayA⟩ := readCodeLenLens_consumed_word alphabet
    obtain ⟨wordL, sourceL, replayL⟩ := codeLens_consumed_word valid parsed
    refine ⟨word1 ++ word2 ++ word3 ++ wordA ++ wordL, ?_, ?_⟩
    · rw [source1, source2, source3, sourceA, sourceL]
      simp only [List.append_assoc]
    · intro suffix
      simp only [List.append_assoc]
      exact Header.dynamic (replay1 _) (replay2 _) (replay3 _) counts (replayA _) valid (replayL suffix) eob validL validD

#print axioms ZlibF.Math.HeaderConsumedReplay.readBits_consumed_word
#print axioms ZlibF.Math.HeaderConsumedReplay.readNats_consumed_word
#print axioms ZlibF.Math.HeaderConsumedReplay.readCodeLenLens_consumed_word
#print axioms ZlibF.Math.HeaderConsumedReplay.codeLens_consumed_word
#print axioms Header.consumed_word
end ZlibF.Math.InflateHuffmanBodyContext
