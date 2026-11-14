import ZlibF.Proof.«gz.inv-queries»
import ZlibF.Proof.«gz.read-close»
import ZlibF.Proof.«gzwrite.c.safety»

/-!
# gz file interface, safety: `gzclose`

The skeleton leaf `gzclose_step` (`skeleton/gz`, `gz.skeleton.lean`): `gzclose` reads the mode
(`gzclose_dispatch_inv`) and runs `gzclose_r` (`GzRead.gzclose_r_step_safe`) or `gzclose_w`
(`gzclose_w_step`). A handle in `GzInv` is a reader or a writer, so `gzclose` never refuses: it
releases the handle. No patch is needed beyond those of the two close lemmas.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- `gzclose` from the dispatch and the two close lemmas. -/
theorem gzclose_step (i : Nat) : GzCloseSafe i (.gzclose (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs
  by_cases hm : s.mode = GZ_READ
  · obtain ⟨v, fs', after, e, hr⟩ := GzRead.gzclose_r_step_safe i h fs s inv hfs
    refine ⟨v, fs', after, ?_, Or.inr ⟨fun hc => hc, ?_⟩⟩
    · show Zlib.Gzclose.gzclose _ fs h = _
      rw [gzclose_dispatch_inv inv fs, if_pos hm]
      exact e
    · rcases hr with ⟨hc, _⟩ | ⟨_, hrel⟩
      · exact absurd hm hc
      · exact hrel
  · have hw : s.mode = GZ_WRITE := by
      rcases inv.common.mode with h1 | h1
      · exact absurd h1 hm
      · exact h1
    obtain ⟨v, fs', after, e, hr⟩ := gzclose_w_step i h fs s inv hfs
    refine ⟨v, fs', after, ?_, Or.inr ⟨fun hc => hc, ?_⟩⟩
    · show Zlib.Gzclose.gzclose _ fs h = _
      rw [gzclose_dispatch_inv inv fs, if_neg hm]
      exact e
    · rcases hr with ⟨hc, _⟩ | ⟨_, hrel⟩
      · exact absurd hw hc
      · exact hrel

#print axioms gzclose_step

end ZlibF.Spec.Public.GzSkeleton
