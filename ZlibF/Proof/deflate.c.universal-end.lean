import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Proof.«public-deflate-end»
import ZlibF.Proof.«deflate.c.engine.caller-frame»

/-!
# deflate.c: `deflateEnd` from the universal invariant

Batch C of the deflate skeleton (`end_from_inv`). The invariant gives `DGood` and the default
allocators, so `deflate_end_public` applies. Its ownership clauses are stated with
`DeflateOwned`; under `DGood` that is `StreamOwned` (`stream_owned_deflate`).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- `deflateEnd` from the invariant (reuses `deflate_end_public`). -/
theorem end_from_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) :
    ∃ rc after z', C.run (Zlib.Deflate.deflateEnd (some r)) h = .ok (rc, after) ∧
      (rc = Z_OK ∨ StreamKind.deflate = .deflate ∧ rc = Z_DATA_ERROR) ∧
      r.get after = some z' ∧ z'.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r) := by
  obtain ⟨after, run, get, live, frame, _count, _next⟩ :=
    DeflateEndProof.deflate_end_public h r ds z d inv.dgood inv.defAlloc.2
  have owned : StreamOwned h r = DeflateOwned ds d :=
    funext fun b => propext (stream_owned_deflate inv.dgood b)
  refine ⟨_, after, { z with state := none }, run, ?_, get, rfl, ?_, ?_⟩
  · by_cases busy : d.status = BUSY_STATE
    · exact Or.inr ⟨rfl, by simp [busy]⟩
    · exact Or.inl (by simp [busy])
  · rw [owned]; exact frame
  · rw [owned]; exact live

end Zlib.Deflate.Universal
