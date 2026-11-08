import ZlibF.Proof.«inflate.c.fast-memory-shape-source»
import ZlibF.Spec.Public.History

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every successful execution of the actual fast decoder keeps the set of
live objects and the allocation ledger unchanged. This result inspects the
translated callee itself; it has no caller buffer or callee-contract premise. -/
theorem inflate_fast_live_nalloc_of_run
    {r : ZStreamRef} {start : UInt32} {h after : Heap}
    (run : C.run (Zlib.Inffast.inflate_fast (some r) start) h = .ok ((), after)) :
    LiveChange h after (fun _ => False) (fun _ => False) ∧
    after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
    after.static = h.static ∧ after.allocOk = h.allocOk ∧
    after.garbage = h.garbage ∧ after.ro = h.ro := by
  have frame := fastMemoryMetaFrameM_inflate_fast r start h () after run
  simp only [FastMemoryMetaFrame, fastMemoryMeta, Prod.mk.injEq] at frame
  rcases frame with ⟨ro, nextBlk, nalloc, statics, allocOk, garbage, live⟩
  refine ⟨?_, nalloc, nextBlk, statics, allocOk, garbage, ro⟩
  intro b
  change after.live b ↔ (h.live b ∧ ¬ False) ∨ False
  rw [live]
  simp

#print axioms inflate_fast_live_nalloc_of_run

end Zlib.Inflate.Proofs
