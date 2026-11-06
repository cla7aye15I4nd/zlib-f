import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«deflate.c.life.end»

open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.DeflateEndProof

/-- `int deflateEnd(z_streamp strm)`
The exact public result, state, frame and ownership contract. -/
theorem deflate_end_public : Goal.deflateEnd := by
  intro h r i z s hG hf
  obtain ⟨w,p,q,b,hB,after,hr,he,hz,hd,hw,hb,hp,hq,hdrest,hbrest,hwrest,hro,hgh,hist,hnext,hnalloc,hstream,hgz,hu,hfresh,hown⟩ := deflateEnd_safe hG hf
  refine ⟨after, hr, hz, ?_, ?_, hnalloc, hnext⟩
  · have ho := hown (fun b => h.live b) (fun _ => Iff.rfl)
    intro x
    have hxi : DOwned s i x ↔ DeflateOwned i s x := by
      rw [DOwned_iff hB]
      simp [DeflateOwned, hB.win, hB.prev, hB.head, hB.pbuf, eq_comm]
    simpa [LiveChange, hxi] using ho x
  · have hs : h.static = after.static := by
      rw [he, endHeap_eq hB]
      cases r <;> simp [ZStreamRef.put] <;> split <;> rfl
    have ha : h.allocOk = after.allocOk := by
      rw [he, endHeap_eq hB]
      cases r <;> simp [ZStreamRef.put] <;> split <;> rfl
    have hg : h.garbage = after.garbage := by
      rw [he, endHeap_eq hB]
      cases r <;> simp [ZStreamRef.put] <;> split <;> rfl
    refine ⟨hs,ha,hg,by omega,by omega,?_⟩
    intro x hx hnot
    have hi : x ≠ i := fun e => hnot (Or.inr (Or.inl e))
    have hw' : x ≠ w := fun e => hnot (Or.inr (Or.inr (Or.inl (by simpa [hB.win] using e.symm))))
    have hp' : x ≠ p := fun e => hnot (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [hB.prev] using e.symm)))))
    have hq' : x ≠ q := fun e => hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [hB.head] using e.symm))))))
    have hb' : x ≠ b := fun e => hnot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa [hB.pbuf] using e.symm))))))
    refine ⟨hbrest x hw' hb', hwrest x hp' hq', ?_, by rw [hgh], hdrest x hi, by rw [hist], ?_, by rw [hro]⟩
    · apply hstream x
      intro j h e
      apply hnot
      exact Or.inl (by simpa [StreamRoot, h] using e)
    · apply hgz x
      intro j h e
      apply hnot
      exact Or.inl (by simpa [StreamRoot, h] using e)

#print axioms deflate_end_public

end ZlibF.Spec.Public.DeflateEndProof
