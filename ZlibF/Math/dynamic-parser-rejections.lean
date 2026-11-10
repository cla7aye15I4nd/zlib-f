import ZlibF.Math.«dynamic-parser-context»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1800000

def NoCodeLensExtension (alphabet : List Nat) (total : Nat) (before : List Nat) (word : List Bool) : Prop :=
  ∀ future rest decoded, ¬CodeLens alphabet total before (word++future) rest decoded

theorem ParserContext.reject {alphabet before after : List Nat} {total : Nat} {left word : List Bool}
    (context : ParserContext alphabet total before left after)
    (rejected : NoCodeLensExtension alphabet total after word) :
    NoCodeLensExtension alphabet total before (left++word) := by
  intro future rest decoded parsed
  simp only [List.append_assoc] at parsed
  exact rejected future rest decoded ((context (word++future) rest decoded).mp parsed)

theorem previous_without_length_no_extension {alphabet : List Nat} {total : Nat}
    (valid : Acceptable .codeLength alphabet) (more : 0<total) (nonzero : alphabet.getD 16 0≠0) :
    NoCodeLensExtension alphabet total [] (codeOf alphabet 16) := by
  intro future rest decoded parsed
  have code:=ZlibF.Math.InflateDecode.decode_canonical_word valid 16 nonzero future
  cases parsed with
  | done count => simp only [List.length_nil] at count;omega
  | len _ read small _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep16 _ _ nonempty _ _ _ => exact nonempty rfl
  | rep17 _ read _ _ _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep18 _ read _ _ _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega

theorem repeat16_overflow_no_extension {alphabet before : List Nat} {total value : Nat}
    (valid : Acceptable .codeLength alphabet) (more : before.length<total)
    (nonzero : alphabet.getD 16 0≠0) (bound : value<2^2)
    (overflow : total<before.length+(3+value)) :
    NoCodeLensExtension alphabet total before (codeOf alphabet 16++bitsOfNat value 2) := by
  intro future rest decoded parsed
  have code:=ZlibF.Math.InflateDecode.decode_canonical_word valid 16 nonzero (bitsOfNat value 2++future)
  have extra : readBits 2 (bitsOfNat value 2++future)=some (value,future) := by
    simpa only [Nat.mod_eq_of_lt bound,Nat.sub_self,bitsOfNat_zero,List.nil_append] using
      readBits_bitsOfNat 2 2 value future (Nat.le_refl _)
  simp only [List.append_assoc] at parsed
  cases parsed with
  | done count => omega
  | len _ read small _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep16 _ read _ readExtra room _ =>
    rw [code] at read
    obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj read)
    rw [extra] at readExtra
    obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj readExtra)
    omega
  | rep17 _ read readExtra room _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep18 _ read readExtra room _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega

theorem repeat17_overflow_no_extension {alphabet before : List Nat} {total value : Nat}
    (valid : Acceptable .codeLength alphabet) (more : before.length<total)
    (nonzero : alphabet.getD 17 0≠0) (bound : value<2^3)
    (overflow : total<before.length+(3+value)) :
    NoCodeLensExtension alphabet total before (codeOf alphabet 17++bitsOfNat value 3) := by
  intro future rest decoded parsed
  have code:=ZlibF.Math.InflateDecode.decode_canonical_word valid 17 nonzero (bitsOfNat value 3++future)
  have extra : readBits 3 (bitsOfNat value 3++future)=some (value,future) := by
    simpa only [Nat.mod_eq_of_lt bound,Nat.sub_self,bitsOfNat_zero,List.nil_append] using
      readBits_bitsOfNat 3 3 value future (Nat.le_refl _)
  simp only [List.append_assoc] at parsed
  cases parsed with
  | done count => omega
  | len _ read small _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep16 _ read _ readExtra room _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep17 _ read readExtra room _ =>
    rw [code] at read
    obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj read)
    rw [extra] at readExtra
    obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj readExtra)
    omega
  | rep18 _ read readExtra room _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega

theorem repeat18_overflow_no_extension {alphabet before : List Nat} {total value : Nat}
    (valid : Acceptable .codeLength alphabet) (more : before.length<total)
    (nonzero : alphabet.getD 18 0≠0) (bound : value<2^7)
    (overflow : total<before.length+(11+value)) :
    NoCodeLensExtension alphabet total before (codeOf alphabet 18++bitsOfNat value 7) := by
  intro future rest decoded parsed
  have code:=ZlibF.Math.InflateDecode.decode_canonical_word valid 18 nonzero (bitsOfNat value 7++future)
  have extra : readBits 7 (bitsOfNat value 7++future)=some (value,future) := by
    simpa only [Nat.mod_eq_of_lt bound,Nat.sub_self,bitsOfNat_zero,List.nil_append] using
      readBits_bitsOfNat 7 7 value future (Nat.le_refl _)
  simp only [List.append_assoc] at parsed
  cases parsed with
  | done count => omega
  | len _ read small _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep16 _ read _ readExtra room _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep17 _ read readExtra room _ =>
    rw [code] at read
    have same:=congrArg Prod.fst (Option.some.inj read)
    omega
  | rep18 _ read readExtra room _ =>
    rw [code] at read
    obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj read)
    rw [extra] at readExtra
    obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj readExtra)
    omega

#print axioms ParserContext.reject
#print axioms previous_without_length_no_extension
#print axioms repeat16_overflow_no_extension
#print axioms repeat17_overflow_no_extension
#print axioms repeat18_overflow_no_extension
end Zlib.Inflate.Proofs.DynamicRejects
