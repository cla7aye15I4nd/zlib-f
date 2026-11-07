import ZlibF.Spec.InflateFastPlatform
import ZlibF.Proof.PlatformMemory
import ZlibF.Proof.«inffast.c.final»

/-!
# inffast.c: discharge size premises from the platform scope

The actual fast call keeps its existing safety and accounting conclusion.
Its returned heap also satisfies the explicit platform size condition.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.PlatformMemory
set_option autoImplicit false

/-- The existing exact fast-call frame establishes preservation of the
platform scope; a post-state size premise is not assumed. -/
theorem PlatformEntry.fit_after (entry : PlatformEntry) {after : Heap}
    (post : FastPost entry.toEnv after) : ByteObjectsFit after := by
  obtain ⟨used, produced, buffered, bytes, msg, mode, bits, hold,
    _, _, _, size, _, _, heap, _⟩ := post
  rw [heap]
  apply ByteObjectsFit.put_stream
  have bound : bytes.size < byteObjectLimit := by
    change bytes.size < 2 ^ 63
    rw [size]
    exact entry.toEnv.hAbig
  exact (entry.platform.with_bytes (block := entry.ob) bound).with_istates _

/-- `void inflate_fast(z_streamp strm, unsigned start)`.
The explicit LP64 platform scope bounds all represented byte objects by
`PTRDIFF_MAX`. The other internal fast-entry restrictions are retained.
Execution, termination, frame and exact writeback follow from the proved
translated callee; no callee contract is a hypothesis. The returned heap
preserves the platform condition. This is not the public inflate goal. -/
theorem inflate_fast_safe_platform (entry : PlatformEntry) :
    ∃ after, C.run (inflate_fast entry.strm entry.start) entry.h0 = .ok ((), after) ∧
      FastPost entry.toEnv after ∧ ByteObjectsFit after := by
  obtain ⟨after, run, post⟩ := inflate_fast_safe entry.toEnv
  exact ⟨after, run, post, PlatformEntry.fit_after entry post⟩

end Zlib.Inffast.Proofs
