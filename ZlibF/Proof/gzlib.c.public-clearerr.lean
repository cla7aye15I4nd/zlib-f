import ZlibF.Spec.Public.GzControl
import ZlibF.Proof.«gzlib.c.simple»

namespace ZlibF.Spec.Public.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs

private theorem gzclearerr_record {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE)
    (hmsg : s.msg = .null ∨ ∃ b a, s.msg = .ref (.blk b) 0 ∧
      h.bytes b = some a ∧ h.ro b = false)
    (hmem : s.err = Z_MEM_ERROR → s.msg = .null) :
    C.run (gzclearerr (hnd i)) h =
      .ok ((), setS (freeStr h s.msg) i (errNull (clearRec s) Z_OK)) := by
  unfold C.run gzclearerr
  rcases hmsg with hn | ⟨mb, a, hp, ha, hro⟩
  · rcases hm with hmode | hmode <;>
      gsimp [hs, hn, hmode, gz_error, clearRec, errNull, GZ_READ, GZ_WRITE]
  · have hne : s.err ≠ Z_MEM_ERROR := fun he => by
      have hnull := hmem he
      rw [hp] at hnull
      cases hnull
    rcases hm with hmode | hmode <;>
      gsimp [hs, hp, hne, hmode, freeB_blk_setS ha hro, freeB_blk_run ha hro,
        gz_error, clearRec, errNull, GZ_READ, GZ_WRITE]

/-- `void gzclearerr(gzFile file)` clears the error, frees the message, and
rearms end-of-file reporting for a reader, under the public handle contract. -/
theorem gzclearerr : Goal.gzclearerr := by
  constructor
  · intro h
    exact gzclearerr_null h
  · intro h i s hv
    rcases hv with ⟨hs, hm, _, _, _, _, hmsg, hmem, _⟩
    have hm' : s.msg = .null ∨ ∃ b a, s.msg = .ref (.blk b) 0 ∧
        h.bytes b = some a ∧ h.ro b = false := by
      rcases hmsg with hnull | ⟨_, _, b, a, hp, ha, hro, _⟩
      · exact Or.inl hnull
      · exact Or.inr ⟨b, a, hp, ha, hro⟩
    have heq : freeStr h s.msg = dropWindow h s.msg := by
      rcases hm' with hnull | ⟨b, a, hp, ha, hro⟩
      · simp [hnull, freeStr, dropWindow]
      · simp [hp, freeStr, dropWindow]
    have hr := gzclearerr_record hs hm hm' hmem
    rw [heq] at hr
    rcases hm with hread | hwrite
    · simpa [hnd, putGz, setS, clearRec, errNull, hread] using hr
    · simpa [hnd, putGz, setS, clearRec, errNull, hwrite, GZ_READ, GZ_WRITE] using hr

end ZlibF.Spec.Public.Proofs
