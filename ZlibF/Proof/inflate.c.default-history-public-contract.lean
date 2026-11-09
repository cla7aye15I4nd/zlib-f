import ZlibF.Proof.«inflate.c.default-call-bundle»
import ZlibF.Proof.«inflate.c.sync-default-history»
import ZlibF.Proof.«public-inflate-end»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual initialized default history supplies every decoder and allocator
premise for all thirteen registered ordinary calls. The next call is total,
retains the same history and satisfies the original exact public resources.
Reset2 is the registered fifteen-bit request; other configurations are open. -/
theorem DefaultOriginHistory.call_contract {h : Heap} {r : ZStreamRef} {call : Call}
    (history : DefaultOriginHistory h r) (selected : DefaultHistoryCall r call)
    (arguments : StreamArguments h r call) :
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      DefaultOriginHistory after r ∧ StreamInvariant .inflate after r ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨⟨zs, z, s, before, allocator⟩, _reachable⟩ := history.sound
  obtain ⟨value, after, stream, state, run, current, finalAllocator, frame, ledger⟩ :=
    selected.total_origin_public_contract before allocator arguments
  exact ⟨value, after, run, .step history selected arguments run,
    ⟨zs, stream, state, current.good, finalAllocator⟩, frame, ledger⟩

/-- The registered default operations and recovery share one exact next-call
contract. This explicit operation filter also includes the genuine Sync
refusal/search-success cases under the original corrected caller arguments. -/
theorem DefaultOriginHistory.operation_contract {h : Heap} {r : ZStreamRef} {call : Call}
    (history : DefaultOriginHistory h r)
    (selected : DefaultHistoryCall r call ∨ call = .inflateSync (some r))
    (arguments : StreamArguments h r call) :
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      DefaultOriginHistory after r ∧ StreamInvariant .inflate after r ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  rcases selected with ordinary | sync
  · exact history.call_contract ordinary arguments
  · subst call
    obtain ⟨rc, after, run, next, invariant, _codes, frame, ledger⟩ := history.sync_contract arguments
    exact ⟨rc, after, heapCall_of_actual_run run default, next, invariant, frame, ledger⟩

/-- End derives its live representation from actual default history and
releases precisely its state and optional window, retaining caller storage. -/
theorem DefaultOriginHistory.end_contract {h : Heap} {r : ZStreamRef}
    (history : DefaultOriginHistory h r) :
    ∃ after stream, C.run (inflateEnd (some r)) h = .ok (Z_OK, after) ∧
      r.get after = some stream ∧ stream.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨⟨zs, z, s, before, allocator⟩, _reachable⟩ := history.sound
  obtain ⟨after, run, streamGet, ledger, frame, allocations, frontier⟩ :=
    ZlibF.Spec.Public.InflateEndProof.inflate_end_public h r zs z s before.good allocator.2
  refine ⟨after, {z with state := none}, run, streamGet, rfl, ?_, ?_, allocations, frontier⟩
  · exact inflate_frame_mono frame (fun b changed => changed.elim Or.inl
      (fun owned => Or.inr ((before.good.streamOwned_iff b).mpr owned)))
  · intro b
    simpa only [before.good.streamOwned_iff b] using ledger b

#print axioms DefaultOriginHistory.call_contract
#print axioms DefaultOriginHistory.operation_contract
#print axioms DefaultOriginHistory.end_contract
end Zlib.Inflate.Proofs
