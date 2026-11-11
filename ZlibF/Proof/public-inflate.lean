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
  obtain ⟨rc, after, z', s', used, out, run, next, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
    c13, c14, c15, _⟩ := inflate_call current ⟨platform, buffers, header⟩ flush
  exact ⟨rc, after, z', s', used, out, run, next.good, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11,
    c12, c13, c14, c15⟩

end Zlib.Inflate.Proofs
