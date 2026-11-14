import ZlibF.Proof.«inflate.c.reachable»
import ZlibF.Spec.Functional.Streams

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflate(z_streamp strm, int flush)`.
Every reachable inflate stream satisfies the history invariant and the
held-bit bound; one call from them satisfies every clause. -/
theorem inflate_public : ZlibF.Spec.Public.Goal.inflate := by
  intro h r i z s flush reach good platform _allocator buffers header
  obtain ⟨current, held⟩ := inflate_reachable_invariant reach good
  have caller : CallPremises h r := ⟨platform, buffers, header⟩
  have call : InflateCall h r i z s flush := by
    by_cases refused : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC
    · exact inflate_call_refused current caller flush refused
    · refine inflate_call current caller flush held ⟨fun e => refused (Or.inl e), ?_, fun e => refused (Or.inr (Or.inr e))⟩
      intro e
      exact Classical.byContradiction fun pending => refused (Or.inr (Or.inl ⟨e, pending⟩))
  obtain ⟨rc, after, z', s', used, out, run, next, accounting, bytes, codes, progress, stream, streamEq,
    buffer, moving, ended, dict, data, memory, totals, frame, ledger, _⟩ := call
  exact ⟨rc, after, z', s', used, out, run, next.good, accounting, bytes, codes, progress, stream, streamEq,
    buffer, moving, ended, dict, data, memory, totals, frame, ledger⟩

#print axioms inflate_public
end Zlib.Inflate.Proofs
