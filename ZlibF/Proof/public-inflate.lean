import ZlibF.Proof.«inflate.c.reachable»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflate(z_streamp strm, int flush)`.
Every reachable inflate stream satisfies the history invariant; one call
from the invariant satisfies every clause. -/
theorem inflate_public : ZlibF.Spec.Public.Goal.inflate := by
  intro h r i z s flush reach good platform _allocator buffers header
  have current := inflate_reachable_invariant reach good
  obtain ⟨rc, after, z', s', used, out, run, next, rest⟩ := inflate_call current ⟨platform, buffers, header⟩ flush
  exact ⟨rc, after, z', s', used, out, run, next.good, rest⟩

end Zlib.Inflate.Proofs
