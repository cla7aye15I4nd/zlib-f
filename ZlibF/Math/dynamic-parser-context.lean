import ZlibF.Proof.«inflate.c.dynamic-empty-code-seed»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs
open ZlibF.Math.CodeLengthPrefix
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- A reversible causal parser prefix. Unlike the older forward Trace,
this also interprets actual rejection after the committed prefix. -/
def ParserContext (alphabet : List Nat) (total : Nat) (before : List Nat)
    (word : List Bool) (after : List Nat) : Prop :=
  ∀ future rest decoded, CodeLens alphabet total before (word++future) rest decoded ↔
    CodeLens alphabet total after future rest decoded

theorem ParserContext.refl (alphabet : List Nat) (total : Nat) (before : List Nat) :
    ParserContext alphabet total before [] before := by
  intro future rest decoded;simp only [List.nil_append]

theorem ParserContext.trans {alphabet before middle after : List Nat} {total : Nat} {left right : List Bool}
    (first : ParserContext alphabet total before left middle)
    (second : ParserContext alphabet total middle right after) :
    ParserContext alphabet total before (left++right) after := by
  intro future rest decoded
  simpa only [List.append_assoc] using (first (right++future) rest decoded).trans (second future rest decoded)

theorem ParserContext.literal {alphabet before : List Nat} {total symbol : Nat}
    (valid : Acceptable .codeLength alphabet) (more : before.length<total)
    (nonzero : alphabet.getD symbol 0≠0) (small : symbol<16) :
    ParserContext alphabet total before (codeOf alphabet symbol) (before++[symbol]) := by
  intro future rest decoded
  have code := ZlibF.Math.InflateDecode.decode_canonical_word valid symbol nonzero future
  constructor
  · intro parsed
    cases parsed with
    | done full => omega
    | len _ read _ tail =>
      rw [code] at read
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj read)
      exact tail
    | rep16 _ read _ _ _ _ =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep17 _ read _ _ _ =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep18 _ read _ _ _ =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
  · exact fun parsed=>CodeLens.len more code small parsed

theorem ParserContext.repeat16 {alphabet before : List Nat} {total value : Nat}
    (valid : Acceptable .codeLength alphabet) (more : before.length<total)
    (nonzero : alphabet.getD 16 0≠0) (nonempty : before≠[]) (bound : value<2^2)
    (room : before.length+(3+value)≤total) :
    ParserContext alphabet total before (codeOf alphabet 16++bitsOfNat value 2) (before++List.replicate (3+value) (before.getLastD 0)) := by
  intro future rest decoded
  have code := ZlibF.Math.InflateDecode.decode_canonical_word valid 16 nonzero (bitsOfNat value 2++future)
  have extra : readBits 2 (bitsOfNat value 2++future)=some (value,future) := by
    simpa only [Nat.mod_eq_of_lt bound,Nat.sub_self,bitsOfNat_zero,List.nil_append] using
      readBits_bitsOfNat 2 2 value future (Nat.le_refl _)
  constructor
  · intro parsed
    simp only [List.append_assoc] at parsed
    cases parsed with
    | done full => omega
    | len _ read small _ =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep16 _ read _ readExtra _ tail =>
      rw [code] at read
      obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj read)
      rw [extra] at readExtra
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj readExtra)
      exact tail
    | rep17 _ read readExtra _ tail =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep18 _ read readExtra _ tail =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
  · intro parsed
    simp only [List.append_assoc]
    exact CodeLens.rep16 more code nonempty extra room parsed

theorem ParserContext.repeat17 {alphabet before : List Nat} {total value : Nat}
    (valid : Acceptable .codeLength alphabet) (more : before.length<total)
    (nonzero : alphabet.getD 17 0≠0) (bound : value<2^3)
    (room : before.length+(3+value)≤total) :
    ParserContext alphabet total before (codeOf alphabet 17++bitsOfNat value 3) (before++List.replicate (3+value) 0) := by
  intro future rest decoded
  have code := ZlibF.Math.InflateDecode.decode_canonical_word valid 17 nonzero (bitsOfNat value 3++future)
  have extra : readBits 3 (bitsOfNat value 3++future)=some (value,future) := by
    simpa only [Nat.mod_eq_of_lt bound,Nat.sub_self,bitsOfNat_zero,List.nil_append] using
      readBits_bitsOfNat 3 3 value future (Nat.le_refl _)
  constructor
  · intro parsed
    simp only [List.append_assoc] at parsed
    cases parsed with
    | done full => omega
    | len _ read small _ =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep16 _ read _ readExtra _ tail =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep17 _ read readExtra _ tail =>
      rw [code] at read
      obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj read)
      rw [extra] at readExtra
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj readExtra)
      exact tail
    | rep18 _ read readExtra _ tail =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
  · intro parsed
    simp only [List.append_assoc]
    exact CodeLens.rep17 more code extra room parsed

theorem ParserContext.repeat18 {alphabet before : List Nat} {total value : Nat}
    (valid : Acceptable .codeLength alphabet) (more : before.length<total)
    (nonzero : alphabet.getD 18 0≠0) (bound : value<2^7)
    (room : before.length+(11+value)≤total) :
    ParserContext alphabet total before (codeOf alphabet 18++bitsOfNat value 7) (before++List.replicate (11+value) 0) := by
  intro future rest decoded
  have code := ZlibF.Math.InflateDecode.decode_canonical_word valid 18 nonzero (bitsOfNat value 7++future)
  have extra : readBits 7 (bitsOfNat value 7++future)=some (value,future) := by
    simpa only [Nat.mod_eq_of_lt bound,Nat.sub_self,bitsOfNat_zero,List.nil_append] using
      readBits_bitsOfNat 7 7 value future (Nat.le_refl _)
  constructor
  · intro parsed
    simp only [List.append_assoc] at parsed
    cases parsed with
    | done full => omega
    | len _ read small _ =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep16 _ read _ readExtra _ tail =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep17 _ read readExtra _ tail =>
      rw [code] at read
      have same:=congrArg Prod.fst (Option.some.inj read)
      omega
    | rep18 _ read readExtra _ tail =>
      rw [code] at read
      obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj read)
      rw [extra] at readExtra
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj readExtra)
      exact tail
  · intro parsed
    simp only [List.append_assoc]
    exact CodeLens.rep18 more code extra room parsed

#print axioms ParserContext.refl
#print axioms ParserContext.trans
#print axioms ParserContext.literal
#print axioms ParserContext.repeat16
#print axioms ParserContext.repeat17
#print axioms ParserContext.repeat18
end Zlib.Inflate.Proofs.DynamicRejects
