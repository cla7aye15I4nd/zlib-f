import ZlibF.Proof.«deflate.c.init.general-main»
import ZlibF.Proof.«public-inflate-init»
import ZlibF.Spec.Safety.Domains

/-! # `Goal.deflate_initialisation_domain`

Every parameter tuple that `Api.deflInit?` accepts initialises a stream on every caller heap in
`InitDomain` whose next five allocations succeed: `deflateInit2_` returns `Z_OK`, the heap is
`DeflateInitial` for the normalised parameters, and the stream is `StreamReachable .deflate`
through the `deflateInit` rule. The fixed caller heap `witnessHeap` is in the domain, so the
domain is not empty. Composed from `init2_main` (`deflate.c.init.general-main`).
-/

namespace ZlibF.Spec.Public.Proofs.DeflateInitDomain
open C ZlibF.Spec.Public Zlib.Deflate.Proofs.GeneralInit
set_option autoImplicit false

/-- The general clause: a successful run, `DeflateInitial` and reachability. -/
theorem deflate_domain_general :
    ∀ h r version level method wb mem strategy p,
      InitDomain h r version →
      Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
      (∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) →
      ∃ after, C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
        .ok (Z_OK, after) ∧ DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  intro h r version level method wb mem strategy p hd hp alloc
  obtain ⟨hf, hu, hg, hv, z, hz, ha, _⟩ := hd
  obtain ⟨rc, after, run, facts⟩ := init2_main level method wb mem strategy h r z version hf hu hg hz ha hv
  rw [hp] at facts
  have first : h.allocOk h.nalloc = true := by simpa using alloc 0 (by decide)
  have all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true := by
    simpa only [List.all_eq_true, List.mem_range] using alloc
  simp only [first, all, Bool.false_eq_true, if_false, if_true] at facts
  obtain ⟨-, rfl, initial⟩ := facts
  exact ⟨after, run, initial, StreamReachable.deflateInit hf hu hg hz ha hv run⟩

/-- **`Goal.deflate_initialisation_domain`**: the general clause, the fixed caller heap in the
domain, and a successful initialisation of that heap for every accepted parameter tuple. -/
theorem deflate_initialisation_domain_public : Goal.deflate_initialisation_domain := by
  refine ⟨deflate_domain_general, InflateInit.public_witness_domain, ?_⟩
  intro level method wb mem strategy p hp
  obtain ⟨after, hr, hi, _⟩ := deflate_domain_general witnessHeap (.tab 0) (.ref (.blk 1) 0)
    level method wb mem strategy p InflateInit.public_witness_domain hp (fun _ _ => rfl)
  exact ⟨after, hr, hi⟩

end ZlibF.Spec.Public.Proofs.DeflateInitDomain

#print axioms ZlibF.Spec.Public.Proofs.DeflateInitDomain.deflate_initialisation_domain_public
