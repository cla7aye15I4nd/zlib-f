import ZlibF.Proof.«inflate.c.copy-source-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every invalid Reset2 request is an actual unchanged-heap refusal.
This adds no valid nondefault configuration to the default invariant. -/
theorem inflateReset2_invalid_default_public_contract
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (bits : Int32) (invalid : reset2Params bits = none) :
    C.run (inflateReset2 (some r) bits) h = .ok (Z_STREAM_ERROR, h) ∧
      BufferFrame h h
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflateReset2 (some r) bits) b)
        (StreamWriteRegions h r (.inflateReset2 (some r) bits)) ∧
      LiveChange h h
        (fun b => StreamOwned h r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned h r b) := by
  obtain ⟨rc, after, run, result⟩ := inflateReset2_safe before.good allocator.2 bits
  rw [invalid] at result
  obtain ⟨rcEq, afterEq⟩ := result
  subst rc after
  exact ⟨run, default_record_public_resources before.good before.good
    (RecordFrame.refl r (some (.tab zs)) h) rfl (.inflateReset2 (some r) bits)⟩

/-- Ordinary default operations, Sync and all invalid Reset2 requests return
from the actual initialized history. Valid nondefault Reset2 requests remain
outside this explicit operation filter. Every resource predicate is the
original public one; refused Reset2 leaves the same history heap. -/
theorem DefaultOriginHistory.operation_with_invalid_reset2_contract
    {h : Heap} {r : ZStreamRef} {call : Call}
    (history : DefaultOriginHistory h r)
    (selected : DefaultHistoryCall r call ∨ call = .inflateSync (some r) ∨
      ∃ bits, call = .inflateReset2 (some r) bits ∧ reset2Params bits = none)
    (arguments : StreamArguments h r call) :
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      DefaultOriginHistory after r ∧ StreamInvariant .inflate after r ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  rcases selected with ordinary | sync | ⟨bits, callEq, invalid⟩
  · exact history.operation_contract (Or.inl ordinary) arguments
  · exact history.operation_contract (Or.inr sync) arguments
  · subst call
    obtain ⟨⟨zs, z, s, before, allocator⟩, _⟩ := history.sound
    obtain ⟨run, frame, ledger⟩ := inflateReset2_invalid_default_public_contract before allocator bits invalid
    exact ⟨Z_STREAM_ERROR, h, heapCall_of_actual_run run default,
      history, ⟨zs, z, s, before.good, allocator⟩, frame, ledger⟩

#print axioms inflateReset2_invalid_default_public_contract
#print axioms DefaultOriginHistory.operation_with_invalid_reset2_contract
end Zlib.Inflate.Proofs
