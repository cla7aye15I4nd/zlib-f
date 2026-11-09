import ZlibF.Math.InflateCanonicalDecode
import ZlibF.Proof.«inftrees.c.decode.semantics»

namespace ZlibF.Math.CodeLengthPrefix
open ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- A causal partial parse records only consumed bits. Its meaning holds
for every future suffix, including one supplied by a later caller buffer.
It is an independent format relation, not a program or callee contract. -/
def Trace (alphabet : List Nat) (total : Nat) (before : List Nat)
    (consumed : List Bool) (after : List Nat) : Prop :=
  ∀ future rest lengths, CodeLens alphabet total after future rest lengths →
    CodeLens alphabet total before (consumed ++ future) rest lengths

theorem Trace.refl (alphabet : List Nat) (total : Nat) (before : List Nat) :
    Trace alphabet total before [] before := by
  intro future rest lengths completion
  simpa only [List.nil_append] using completion

theorem Trace.trans {alphabet : List Nat} {total : Nat} {before middle after : List Nat}
    {left right : List Bool} (first : Trace alphabet total before left middle)
    (second : Trace alphabet total middle right after) :
    Trace alphabet total before (left ++ right) after := by
  intro future rest lengths completion
  simpa only [List.append_assoc] using first _ _ _ (second _ _ _ completion)

theorem Trace.complete {alphabet : List Nat} {total : Nat} {before after : List Nat} {consumed future : List Bool}
    (trace : Trace alphabet total before consumed after) (finished : after.length = total) :
    CodeLens alphabet total before (consumed ++ future) future after :=
  trace _ _ _ (CodeLens.done finished)

/-- An actual independent symbol read determines exactly its consumed word. -/
theorem decoded_word {alphabet : List Nat} {input rest : List Bool} {symbol : Nat}
    (read : decodeSym alphabet input = some (symbol, rest)) :
    input = codeOf alphabet symbol ++ rest := by
  obtain ⟨_inside, _nonzero, ⟨tail, source⟩, remaining⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix read
  have length : (codeOf alphabet symbol).length = alphabet.getD symbol 0 := by
    simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]
  rw [← source, ← length, List.drop_left] at remaining
  rw [← remaining] at source
  exact source.symm

private theorem read_length {n : Nat} {input rest : List Bool} {value : Nat}
    (read : readBits n input = some (value, rest)) : n ≤ input.length := by
  induction n generalizing input value rest with
  | zero => omega
  | succ n ih =>
    cases input with
    | nil => simp [readBits] at read
    | cons bit input =>
      cases next : readBits n input with
      | none => simp [readBits, next] at read
      | some pair =>
        have bound := ih next
        simp only [List.length_cons]
        omega

/-- A successful extra-bit reader also supplies the exact consumed word. -/
theorem read_word {n : Nat} {input rest : List Bool} {value : Nat}
    (read : readBits n input = some (value, rest)) :
    value < 2 ^ n ∧ input = bitsOfNat value n ++ rest := by
  obtain ⟨value2, rest2, run, bound, source⟩ := ZlibF.Math.InflateDecode.read_total n input (read_length read)
  rw [read] at run
  cases run
  exact ⟨bound, source⟩

private theorem read_word_append (n value : Nat) (bound : value < 2 ^ n) (future : List Bool) :
    readBits n (bitsOfNat value n ++ future) = some (value, future) := by
  simpa only [Nat.mod_eq_of_lt bound, Nat.sub_self, bitsOfNat_zero, List.nil_append] using
    readBits_bitsOfNat n n value future (Nat.le_refl _)

theorem Trace.literal {alphabet before : List Nat} {total symbol : Nat}
    (acceptable : Acceptable .codeLength alphabet) (more : before.length < total)
    (nonzero : alphabet.getD symbol 0 ≠ 0) (small : symbol < 16) :
    Trace alphabet total before (codeOf alphabet symbol) (before ++ [symbol]) := by
  intro future rest lengths completion
  exact CodeLens.len more (ZlibF.Math.InflateDecode.decode_canonical_word acceptable symbol nonzero future) small completion

theorem Trace.previous {alphabet before : List Nat} {total value : Nat}
    (acceptable : Acceptable .codeLength alphabet) (more : before.length < total)
    (nonzero : alphabet.getD 16 0 ≠ 0) (nonempty : before ≠ []) (bound : value < 4)
    (room : before.length + (3 + value) ≤ total) :
    Trace alphabet total before (codeOf alphabet 16 ++ bitsOfNat value 2)
      (before ++ List.replicate (3 + value) (before.getLastD 0)) := by
  intro future rest lengths completion
  rw [List.append_assoc]
  exact CodeLens.rep16 more (ZlibF.Math.InflateDecode.decode_canonical_word acceptable 16 nonzero _)
    nonempty (read_word_append 2 value bound future) room completion

theorem Trace.zero_short {alphabet before : List Nat} {total value : Nat}
    (acceptable : Acceptable .codeLength alphabet) (more : before.length < total)
    (nonzero : alphabet.getD 17 0 ≠ 0) (bound : value < 8) (room : before.length + (3 + value) ≤ total) :
    Trace alphabet total before (codeOf alphabet 17 ++ bitsOfNat value 3)
      (before ++ List.replicate (3 + value) 0) := by
  intro future rest lengths completion
  rw [List.append_assoc]
  exact CodeLens.rep17 more (ZlibF.Math.InflateDecode.decode_canonical_word acceptable 17 nonzero _)
    (read_word_append 3 value bound future) room completion

theorem Trace.zero_long {alphabet before : List Nat} {total value : Nat}
    (acceptable : Acceptable .codeLength alphabet) (more : before.length < total)
    (nonzero : alphabet.getD 18 0 ≠ 0) (bound : value < 128) (room : before.length + (11 + value) ≤ total) :
    Trace alphabet total before (codeOf alphabet 18 ++ bitsOfNat value 7)
      (before ++ List.replicate (11 + value) 0) := by
  intro future rest lengths completion
  rw [List.append_assoc]
  exact CodeLens.rep18 more (ZlibF.Math.InflateDecode.decode_canonical_word acceptable 18 nonzero _)
    (read_word_append 7 value bound future) room completion

#print axioms Trace.complete
#print axioms read_word
#print axioms Trace.previous
#print axioms Trace.zero_long
end ZlibF.Math.CodeLengthPrefix
