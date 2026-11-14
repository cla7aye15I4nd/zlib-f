import ZlibF.Proof.«deflate.c.universal-sequence-safety»
import ZlibF.Spec.Functional.Streams

/-!
# deflate.c: `Goal.deflate` from the invariant of every reachable history

The skeleton lemma `deflate_proof`: a reachable stream satisfies `DInv` (`reachable_inv_of`), the
state the goal names is the invariant's (`DInv.unique`), and one call keeps `DInv` with every clause
of `Goal.deflate` (`deflate_call`). The open lemmas are the fields of `SequenceFacts`; once they
are theorems, `deflate_proof_of` is `Goal.deflate` with no hypothesis.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- **`Goal.deflate`** from the open lemmas of `SequenceFacts`. -/
theorem deflate_proof_of (facts : SequenceFacts) : Goal.deflate := by
  intro h r i z s flush reach good buffers header
  obtain ⟨ds, z₀, d, inv, headerInv, calls⟩ := reachable_inv_of facts reach
  obtain ⟨rfl, rfl, rfl⟩ := inv.unique good
  obtain ⟨rc, after, z', d', used, out, run, invAfter, clauses, -⟩ :=
    facts.deflateCall inv headerInv calls buffers header flush
  exact ⟨rc, after, z', d', used, out, run, invAfter.dgood, clauses⟩

end Zlib.Deflate.Universal
