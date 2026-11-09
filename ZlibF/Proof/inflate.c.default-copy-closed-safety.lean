import ZlibF.Proof.«inflate.c.default-invalid-reset2»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact sequence safety for the announced default history and operation
filter, now closed under source continuation after every actual Copy result.
The existing history representation suffices: the produced source heap is
proved to satisfy its legal environment relation, including on allocation
failure. No new semantic definition or invariant-bearing constructor is used.
The operation filter contains all thirteen registered calls, Sync and every
invalid Reset2 request. Valid nondefault Reset2 configurations remain open.
The original public arguments and resource predicates are unchanged. Copy
success also establishes destination history; End releases exactly the old
owned objects. An actual default-init witness supplies nonempty scope. -/
theorem default_origin_history_copy_closed_safety :
    (∀ h r, DefaultOriginHistory h r → StreamInvariant .inflate h r) ∧
    (∀ h r call, DefaultOriginHistory h r →
      (DefaultHistoryCall r call ∨ call = .inflateSync (some r) ∨
        ∃ bits, call = .inflateReset2 (some r) bits ∧ reset2Params bits = none) →
      StreamArguments h r call →
      ∃ value after, call.execute default h = .ok ((value, default), after) ∧
        DefaultOriginHistory after r ∧ StreamInvariant .inflate after r ∧
        BufferFrame h after
          (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
          (StreamWriteRegions h r call) ∧
        LiveChange h after
          (fun b => StreamOwned after r b ∧ ¬ h.live b)
          (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b)) ∧
    (∀ h r, DefaultOriginHistory h r →
      ∃ rc after stream, C.run (inflateEnd (some r)) h = .ok (rc, after) ∧ rc = Z_OK ∧
        r.get after = some stream ∧ stream.state = none ∧
        Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
        LiveChange h after (fun _ => False) (StreamOwned h r) ∧
        after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk) ∧
    (∀ h source dest oldDest, DefaultOriginHistory h source → source ≠ dest →
      dest.get h = some oldDest →
      ∃ zs z s rc after, DefaultOriginState h source zs z s ∧ DefAlloc z ∧
        C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
        DefaultOriginState after source zs z s ∧ DefAlloc z ∧
        DefaultOriginHistory after source ∧ StreamInvariant .inflate after source ∧
        CopyResource.CopyResult h after source dest zs z oldDest s rc ∧
        (rc = Z_OK → DefaultOriginHistory after dest) ∧
        (rc = Z_OK → ∃ copied,
          DefaultOriginState after dest h.nextBlk {z with state := some (.inflate h.nextBlk)} copied ∧
          DefaultOriginState after source zs z s)) ∧
    (∃ after, DefaultOriginHistory after (.tab 0)) := by
  refine ⟨?_, ?_, ?_, ?_, default_origin_history_initial_witness⟩
  · intro h r history
    obtain ⟨⟨zs, z, s, current, allocator⟩, _⟩ := history.sound
    exact ⟨zs, z, s, current.good, allocator⟩
  · intro h r call history selected arguments
    exact history.operation_with_invalid_reset2_contract selected arguments
  · intro h r history
    obtain ⟨after, stream, run, get, cleared, frame, ledger, allocations, frontier⟩ := history.end_contract
    exact ⟨Z_OK, after, stream, run, rfl, get, cleared, frame, ledger, allocations, frontier⟩
  · intro h source dest oldDest history different get
    exact history.copy_total_contract different get

#print axioms default_origin_history_copy_closed_safety
end Zlib.Inflate.Proofs
