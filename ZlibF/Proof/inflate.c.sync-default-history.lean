import ZlibF.Proof.«inflate.c.sync-default-public»
import ZlibF.Proof.«inflate.c.origin-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default initialization and the admitted history establish all
state premises of the next Sync call. No invariant or run is assumed for
that next call. The resulting call retains the same public history. -/
theorem DefaultOriginHistory.sync_contract {h : Heap} {r : ZStreamRef}
    (history : DefaultOriginHistory h r)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ rc after,
      C.run (inflateSync (some r)) h = .ok (rc, after) ∧
      DefaultOriginHistory after r ∧ StreamInvariant .inflate after r ∧
      (rc = Z_OK ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflateSync (some r)) b)
        (StreamWriteRegions h r (.inflateSync (some r))) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨⟨zs, z, s, before, allocator⟩, _⟩ := history.sound
  obtain ⟨rc, after, stream, state, run, current, nextAllocator, kinds, frame, ledger⟩ :=
    inflateSync_default_public_contract before allocator arguments
  exact ⟨rc, after, run, .sync history arguments run,
    ⟨zs, stream, state, current.good, nextAllocator⟩, kinds, frame, ledger⟩

#print axioms DefaultOriginHistory.sync_contract
end Zlib.Inflate.Proofs
