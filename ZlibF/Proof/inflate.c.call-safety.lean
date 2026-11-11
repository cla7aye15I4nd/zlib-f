import ZlibF.Proof.«inflate.c.copy-invariant»
import ZlibF.Spec.Public.Sequences
import ZlibF.Proof.«inflate.c.default-record-resources»

/-!
# inflate.c: frames and ledgers of the stream operations

The safety part of `Goal.inflate_sequence` for one call: from the general
invariant, the call returns, writes only the stream's records, its own
memory and the caller regions it is given, and changes the allocation
ledger exactly by the stream's own window.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- One stream operation returns with an exact frame and ledger. -/
def InflateCallSafe (r : ZStreamRef) (call : Call) : Prop :=
  ∀ (h : Heap) (i : Nat) (z : ZStream) (s : InflateState),
    InflateInv h r i z s → StreamArguments h r call →
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b)

theorem inflateSyncPoint_call_safe (r : ZStreamRef) :
    InflateCallSafe r (.inflateSyncPoint (some r)) := by
  intro h i z s current _
  have run := inflateSyncPoint_spec current.good.live
  exact ⟨_, h, heapCall_of_actual_run run default,
    default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩

theorem inflateMark_call_safe (r : ZStreamRef) : InflateCallSafe r (.inflateMark (some r)) := by
  intro h i z s current _
  obtain ⟨value, run, _⟩ := inflateMark_spec current.good.live
  exact ⟨value, h, heapCall_of_actual_run run default,
    default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩

theorem inflateCodesUsed_call_safe (r : ZStreamRef) :
    InflateCallSafe r (.inflateCodesUsed (some r)) := by
  intro h i z s current _
  obtain ⟨offset, _, _, run⟩ := inflateCodesUsed_spec current.good
  exact ⟨_, h, heapCall_of_actual_run run default,
    default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩

theorem inflateUndermine_call_safe (r : ZStreamRef) (subvert : Int32) :
    InflateCallSafe r (.inflateUndermine (some r) subvert) := by
  intro h i z s current _
  obtain ⟨written, run, heap, _⟩ := inflateUndermine_safe current.good subvert
  have state : { s with sane := 1 } = s := by rw [← current.pending.sane]
  have unchanged : written = h := by rw [heap, state, tcSetI_same current.good.live.hs]
  subst unchanged
  exact ⟨_, written, heapCall_of_actual_run run default,
    default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩

theorem inflateValidate_call_safe (r : ZStreamRef) (check : Int32) :
    InflateCallSafe r (.inflateValidate (some r) check) := by
  intro h i z s current _
  obtain ⟨written, run, heap, good, _⟩ := inflateValidate_safe current.good check
  subst heap
  exact ⟨_, _, heapCall_of_actual_run run default,
    default_record_public_resources current.good good
      (RecordFrame.setI r i current.good.live.hs _) rfl _⟩

theorem inflatePrime_call_safe (r : ZStreamRef) (bits word : Int32) :
    InflateCallSafe r (.inflatePrime (some r) bits word) := by
  intro h i z s current _
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec current.good bits word
  have unchanged : ∀ {rc : Int32}, C.run (inflatePrime (some r) bits word) h = .ok (rc, h) →
      ∃ result after, (Call.inflatePrime (some r) bits word).execute default h =
          .ok ((result, default), after) ∧
        BufferFrame h after
          (fun b => StreamRoot r b ∨ StreamOwned h r b ∨
            StreamHeaderRecord h r (.inflatePrime (some r) bits word) b)
          (StreamWriteRegions h r (.inflatePrime (some r) bits word)) ∧
        LiveChange h after
          (fun b => StreamOwned after r b ∧ ¬ h.live b)
          (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
    intro rc run
    exact ⟨rc, h, heapCall_of_actual_run run default,
      default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩
  by_cases equal : bits = 0
  · exact unchanged (zero equal)
  by_cases negative : bits < 0
  · obtain ⟨run, good⟩ := clear negative
    exact ⟨_, _, heapCall_of_actual_run run default,
      default_record_public_resources current.good good
        (RecordFrame.setI r i current.good.live.hs _) rfl _⟩
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    simp only [Int32.toInt_zero] at negative ⊢
    have nonzero : bits.toInt ≠ 0 := fun zero => equal (Int32.toInt_inj.mp zero)
    omega
  by_cases wide : 16 < bits.toInt
  · exact unchanged (reject positive (Or.inl wide))
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact unchanged (reject positive (Or.inr full))
  obtain ⟨run, good⟩ := insert positive (by omega) (by omega)
  exact ⟨_, _, heapCall_of_actual_run run default,
    default_record_public_resources current.good good
      (RecordFrame.setI r i current.good.live.hs _) rfl _⟩

theorem inflateResetKeep_call_safe (r : ZStreamRef) :
    InflateCallSafe r (.inflateResetKeep (some r)) := by
  intro h i z s current _
  obtain ⟨written, run, heap, good, _⟩ := inflateResetKeep_safe current.good
  subst heap
  exact ⟨_, _, heapCall_of_actual_run run default,
    default_record_public_resources current.good good
      (RecordFrame.stream_state current.good.live.hz current.good.live.hs _ _) rfl _⟩

theorem inflateReset2_call_safe (r : ZStreamRef) (wb : Int32) :
    InflateCallSafe r (.inflateReset2 (some r) wb) := by
  intro h i z s current _
  obtain ⟨code, written, run, result⟩ := inflateReset2_safe current.good current.alloc.2 wb
  cases params : reset2Params wb with
  | none =>
    rw [params] at result
    obtain ⟨_, same⟩ := result
    subst same
    exact ⟨code, written, heapCall_of_actual_run run default,
      default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩
  | some selected =>
    obtain ⟨wrap, width⟩ := selected
    rw [params] at result
    obtain ⟨_, heap, next, ownsFact⟩ := result
    refine ⟨code, written, heapCall_of_actual_run run default,
      reset2_public_resources current.good next heap ownsFact ?_ _ rfl⟩
    simp only [resetKeepState, resetPre, reset2Pre]
    by_cases changes : s.wbits ≠ i2u width
    · simp [changes]
    · simp only [ne_eq, Decidable.not_not] at changes
      simp [changes]

#print axioms inflatePrime_call_safe
#print axioms inflateReset2_call_safe

end Zlib.Inflate.Proofs
