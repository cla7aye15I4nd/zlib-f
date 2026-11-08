import ZlibF.Proof.«inftrees.c.decode.soundness»
import ZlibF.Spec.InflateDecodeTableShort
import ZlibF.Spec.InflateDecodeTableRejection

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness

/-- Appending mathematical zero padding cannot justify consuming a bit
past the original input. A fitted canonical prefix already exists there. -/
theorem decode_unpad {kind : CodeKind} {lens : List Nat} (acceptable : Acceptable kind lens)
    {inp extra rest : List Bool} {symbol used : Nat}
    (decoded : decodeSym lens (inp ++ extra) = some (symbol, rest))
    (length : used = lens.getD symbol 0) (fits : used ≤ inp.length) :
    decodeSym lens inp = some (symbol, inp.drop used) := by
  obtain ⟨_inside, nonzero, codePrefix, _restEq⟩ := decoded_symbol_prefix decoded
  have codeLength : (codeOf lens symbol).length = used := by
    simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length, length]
  have originalPrefix : codeOf lens symbol <+: inp :=
    List.prefix_of_prefix_length_le codePrefix (List.prefix_append inp extra) (by rw [codeLength]; exact fits)
  have reconstruction : codeOf lens symbol ++ inp.drop used = inp := by
    simpa only [codeLength] using List.prefix_iff_eq_append.mp originalPrefix
  have read := ZlibF.Math.InflateDecode.decode_canonical_word acceptable symbol nonzero (inp.drop used)
  rwa [reconstruction] at read

set_option maxHeartbeats 2000000 in
/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)`.
The unchanged short-input semantic target. The code must fit the real input;
zero padding is only a mathematical query and contributes no consumed bits. -/
theorem short_decode_table_leaf_sound : DecodeShort.Goal.short_decode_table_leaf_sound := by
  intro h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨result, after, run, _frame, ret, _construction⟩ :=
    inflate_table_construction h type rl ol codes rc oc bits rw ow pre
  obtain ⟨otherResult, otherHeap, otherRun, sound⟩ :=
    decode_table_leaf_sound h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨results, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans otherRun))
  subst otherResult otherHeap
  refine ⟨result, after, run, ?_⟩
  intro success inp ca entry used get query fits accepted
  have acceptable := (acc_iff type pre.f codes.toNat pre.hf15).mp (ret.1 success)
  have enough : 15 ≤ (DecodeShort.padded inp).length := by
    simp only [DecodeShort.padded, List.length_append, List.length_replicate]
    omega
  obtain ⟨actualArray, actualEntry, actualUsed, actualGet, actualQuery, classification⟩ :=
    sound success (DecodeShort.padded inp) enough
  have arrays : ca = actualArray := Option.some.inj (get.symm.trans actualGet)
  subst actualArray
  obtain ⟨entries, lengths⟩ := Prod.mk.inj (Option.some.inj (query.symm.trans actualQuery))
  subst actualEntry actualUsed
  obtain ⟨symbol, rest, decoded, valid, length, _suffix, meaning⟩ := classification.mp accepted
  have original := decode_unpad acceptable decoded length fits
  refine ⟨symbol, valid, meaning, length, original, ?_⟩
  intro more
  exact ZlibF.Spec.Proofs.ext_acceptable acceptable inp symbol (inp.drop used) more original

set_option maxHeartbeats 2000000 in
/-- Actual full-width queries accept exactly the inputs with a valid
independent symbol. No validity assumption is made about the queried bits. -/
theorem decode_table_classifies_input : DecodeRejection.Goal.decode_table_classifies_input := by
  intro h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨result, after, run, sound⟩ :=
    decode_table_leaf_sound h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨otherResult, otherHeap, otherRun, forward⟩ :=
    decode_table_matches_format h type rl ol codes rc oc bits rw ow pre kind
  obtain ⟨results, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans otherRun))
  subst otherResult otherHeap
  refine ⟨result, after, run, ?_⟩
  intro success inp enough
  obtain ⟨ca, entry, used, get, query, classification⟩ := sound success inp enough
  refine ⟨ca, entry, used, get, query, ?_⟩
  constructor
  · intro accepted
    obtain ⟨symbol, rest, decoded, valid, _length, _suffix, _meaning⟩ := classification.mp accepted
    exact ⟨symbol, rest, decoded, valid⟩
  · rintro ⟨symbol, rest, decoded, valid⟩
    obtain ⟨actualArray, actualEntry, actualUsed, actualGet, actualQuery, length, suffixEq, meaning⟩ :=
      forward success inp symbol rest enough decoded
    have arrays : ca = actualArray := Option.some.inj (get.symm.trans actualGet)
    subst actualArray
    obtain ⟨entries, lengths⟩ := Prod.mk.inj (Option.some.inj (query.symm.trans actualQuery))
    rw [← entries] at meaning
    rw [← lengths] at length suffixEq
    exact classification.mpr ⟨symbol, rest, decoded, valid, length, suffixEq, meaning⟩

#print axioms short_decode_table_leaf_sound
#print axioms decode_table_classifies_input

end Zlib.Inftrees.Proofs
