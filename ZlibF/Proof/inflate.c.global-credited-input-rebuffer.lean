import ZlibF.Proof.«inflate.c.global-credited-input»
namespace Zlib.Inflate.Proofs.CausalInput
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Actual rebuffer preserves the exact private parser index/record and
all non-buffer stream fields alongside the credited source equation. -/
theorem AtPublic.rebuffer_same
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {committed : List Bool}
    (before : AtPublic h r log committed) (edit : Rebuffer h after r) :
    ∃ next : AtPublic after r log committed,
      next.zs = before.zs ∧ next.state = before.state ∧
      next.z = {before.z with next_in := next.z.next_in, avail_in := next.z.avail_in, next_out := next.z.next_out, avail_out := next.z.avail_out} := by
  obtain ⟨stream, fields, good⟩ := rebuffer_inflate_good before.good edit
  exact ⟨⟨before.zs, stream, before.state, good, before.source⟩, rfl, rfl, fields⟩

end Zlib.Inflate.Proofs.CausalInput
