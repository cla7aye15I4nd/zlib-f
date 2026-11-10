import ZlibF.Proof.«inflate.c.whole-epoch-call-frame»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem head_phase_fields {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = HEAD) :
    wire = [] ∧ log.output = [] ∧ log.dictionary = [] ∧ s.bits.toNat < 16 := by
  cases phase with
  | head _ source output dictionary bits => exact ⟨source, output, dictionary, bits⟩
  | memory prior previous notMemory frame => rw [frame] at mode; cases mode
  | _ => simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
      STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH, CHECK, LENGTH, DONE, BAD]

theorem dictid_phase_fields {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = DICTID) :
    ∃ cmf flg, Zlib.HeaderOK cmf flg ∧ flg.toNat / 32 % 2 = 1 ∧ wire = bytesBits [cmf, flg] ∧
      log.output = [] ∧ log.dictionary = [] ∧ s.bits.toNat < 32 := by
  cases phase with
  | dictid cmf flg _ valid flag source output dictionary bits => exact ⟨cmf, flg, valid, flag, source, output, dictionary, bits⟩
  | memory prior previous notMemory frame => rw [frame] at mode; cases mode
  | _ => simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
      STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH, CHECK, LENGTH, DONE, BAD]

theorem low_materialized {h : Heap} {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (low : s.mode ≤ TYPE) : phase.Materialized h := by
  cases phase with
  | ready boundary modes last =>
    rcases modes with first | second
    · rw [first] at low
      exact False.elim ((by decide : ¬ (LEN_ ≤ TYPE)) low)
    · rw [second] at low
      exact False.elim ((by decide : ¬ (LEN ≤ TYPE)) low)
  | reading modes data =>
    rcases modes with first | second | third | fourth
    · rw [first] at low
      exact False.elim ((by decide : ¬ (LENEXT ≤ TYPE)) low)
    · rw [second] at low
      exact False.elim ((by decide : ¬ (DIST ≤ TYPE)) low)
    · rw [third] at low
      exact False.elim ((by decide : ¬ (DISTEXT ≤ TYPE)) low)
    · rw [fourth] at low
      exact False.elim ((by decide : ¬ (LIT ≤ TYPE)) low)
  | _ => simp_all [SourcePhase.Materialized, MATCH, CODELENS, TYPE]


theorem dictionary_phase_fields {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (mode : s.mode = DICT) :
    ∃ (w : Wrapper log.dictionary) (identifier : UInt32),
      w.flg.toNat / 32 % 2 = 1 ∧ wire = bytesBits ([w.cmf, w.flg] ++ be32 identifier.toNat) ∧
      log.output = [] ∧ s.bits = 0 ∧ s.check = identifier.toUInt64 ∧
      (s.havedict ≠ 0 → identifier = adler32 log.dictionary) := by
  cases phase with
  | dictionary w identifier _ flag source output bits check installed => exact ⟨w, identifier, flag, source, output, bits, check, installed⟩
  | memory prior previous notMemory frame => rw [frame] at mode; cases mode
  | _ => simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
      STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH, CHECK, LENGTH, DONE, BAD]

#print axioms head_phase_fields
#print axioms dictid_phase_fields
#print axioms low_materialized
#print axioms dictionary_phase_fields
end Zlib.Inflate.Proofs.WholeWrapper
