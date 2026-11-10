import ZlibF.Proof.«inflate.c.default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Caller replacement of public byte buffers extends the actual history
and preserves every decoder clause. The replacement heap must satisfy the
explicit platform byte-object scope of the public inflate target. -/
theorem inflate_default_rebuffer_history {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultStateJ h r zs z s) (edit : Rebuffer h after r)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultStateJ after r zs stream s ∧
      StreamReachable .inflate after r := by
  obtain ⟨stream, current⟩ := rebuffer_default_state invariant edit platform
  exact ⟨stream, current, StreamReachable.rebuffer reachable edit⟩

end Zlib.Inflate.Proofs
