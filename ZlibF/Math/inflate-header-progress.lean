import ZlibF.Math.«inflate-header-chunks»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- Bits actually introduced during the LENLENS phase consist of the
recorded field word followed by the live held word. received is an explicit
trace index; it is not chosen existentially from the returned state. -/
def LenlensProgress (state : InflateState) (hold : UInt64) (bits : UInt32)
    (received : List Bool) : Prop :=
  received = (headerFields state.lens state.«have».toNat).flatMap
    (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) ++ natBits bits.toNat hold.toNat

/-- The actual zero counter establishes the initial phase relation. -/
theorem LenlensProgress.initial {state : InflateState} (start : state.«have» = 0)
    (hold : UInt64) (bits : UInt32) :
    LenlensProgress state hold bits (natBits bits.toNat hold.toNat) := by
  simp [LenlensProgress, headerFields, start]

/-- One actual field-reading prefix extends the trace only by the bits
pulled from this call. Its unused caller-buffer suffix is absent. -/
theorem LenlensProgress.advance {before after : InflateState}
    {hold nextHold : UInt64} {bits nextBits : UInt32} {received pulled : List Bool} {values : List Nat}
    (progress : LenlensProgress before hold bits received)
    (fields : headerFields after.lens after.«have».toNat = headerFields before.lens before.«have».toNat ++ values)
    (ledger : natBits bits.toNat hold.toNat ++ pulled =
      values.flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) ++ natBits nextBits.toNat nextHold.toNat) :
    LenlensProgress after nextHold nextBits (received ++ pulled) := by
  unfold LenlensProgress at progress ⊢
  rw [progress, List.append_assoc, ledger, fields, List.flatMap_append, List.append_assoc]

/-- A completed phase yields the independent alphabet for every future
suffix. The actual zeroing loop supplies the array in this conclusion. -/
theorem LenlensProgress.alphabet {state : InflateState} {hold : UInt64} {bits : UInt32}
    {received : List Bool} (progress : LenlensProgress state hold bits received)
    (size : 19 ≤ state.lens.size) (bound : state.ncode.toNat ≤ 19)
    (complete : state.«have».toNat = state.ncode.toNat) (good : Good3 state.lens state.«have».toNat)
    (future : List Bool) :
    readCodeLenLens state.ncode.toNat (received ++ future) = some
      (Zlib.Inftrees.Proofs.lensOf
        (fun k => ((lensZero state.lens state.«have».toNat (19 - state.«have».toNat)).getD k 0).toNat) 19,
       natBits bits.toNat hold.toNat ++ future) := by
  have parsed := readCodeLenLens_header_fields size state.«have».toNat (by omega) good
    (natBits bits.toNat hold.toNat ++ future)
  unfold LenlensProgress at progress
  rw [progress, List.append_assoc]
  simpa only [complete] using parsed


/-- Only the recorded array and counter affect the field-word part. -/
theorem LenlensProgress.of_fields {before after : InflateState} {hold : UInt64} {bits : UInt32}
    {received : List Bool} (progress : LenlensProgress before hold bits received)
    (lens : after.lens = before.lens) (count : after.«have» = before.«have») :
    LenlensProgress after hold bits received := by
  unfold LenlensProgress at progress ⊢
  rw [lens, count]
  exact progress

#print axioms LenlensProgress.of_fields

#print axioms LenlensProgress.initial
#print axioms LenlensProgress.advance
#print axioms LenlensProgress.alphabet
end Zlib.Inflate.Proofs
