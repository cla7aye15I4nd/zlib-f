import ZlibF.Spec.Public.Back
import ZlibF.Proof.«infback.c.end»
import ZlibF.Spec.Functional.Api.Compress

namespace ZlibF.Spec.Public.InflateBackEndProof
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec Zlib.Infback.Proofs

theorem inflateBackEnd_record {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (hz : r.get h = some z) (hs : h.istates i = some s)
    (hstate : z.state = some (.inflate i)) (hfree : z.zfree = .fn "zcfree") :
    C.run (inflateBackEnd (some r)) h = .ok (Z_OK, backEndHeap h r z i) := by
  show inflateBackEnd (some r) h = _
  unfold inflateBackEnd
  have hz0 : z.zfree ≠ .null := by rw [hfree]; intro c; cases c
  have hs0 : z.state ≠ none := by rw [hstate]; intro c; cases c
  isimp [hz, hs0, hz0, hstate, hfree, zfrees_run hz hfree hs, backEndHeap]


/-- `int inflateBackEnd(z_streamp strm)`
The exact public result, state, frame and ownership contract. -/
theorem back_end_public : Goal.inflateBackEnd := by
  refine ⟨fun h => inflateBackEnd_nullstream h, ?_, ?_⟩
  · intro h r z hz hn
    exact inflateBackEnd_refused hz hn
  · intro h r i z s hv
    rcases hv with ⟨hz, hs, hstate, halloc, hfree, hwf, hwlo, hwhi, hwsize, hwne, hwrite, hfresh, huniq, hglobal⟩
    let after := backEndHeap h r z i
    refine ⟨after, inflateBackEnd_record hz hs hstate hfree, ?_, ?_, ?_, ?_, ?_⟩
    · simp [after, backEndHeap, hz]
    · have ho : h.Owns (fun b => h.live b) := fun _ => Iff.rfl
      have hfreeown := owns_freeIst huniq hs ho
      have hz' : r.get (freeIst h i) = some z := by simpa using hz
      have hafter := (shape_put hz' { z with state := none }).owns hfreeown
      intro b
      simpa [LiveChange, after, backEndHeap] using hafter b
    · cases r with
      | tab j =>
        have hjz : h.streams j = some z := hz
        simp only [Frame, after, backEndHeap, freeIst, ZStreamRef.put, hjz]
        simp only [true_and]
        refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩

        intro b hl hb
        have hi : b ≠ i := fun e => hb (Or.inr e)
        have hj : b ≠ j := fun e => hb (Or.inl (by simpa [StreamRoot] using e))
        simp [upd_ne, hi, hj]
      | in_gzstate_strm j =>
        cases he : h.gzstates j with
        | none => simp [ZStreamRef.get, he] at hz
        | some g =>
          simp only [Frame, after, backEndHeap, freeIst, ZStreamRef.put, he]
          simp only [true_and]
          refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩

          intro b hl hb
          have hi : b ≠ i := fun e => hb (Or.inr e)
          have hj : b ≠ j := fun e => hb (Or.inl (by simpa [StreamRoot] using e))
          simp [upd_ne, hi, hj]
    · cases r with
      | tab j =>
        have hjz : h.streams j = some z := hz
        simp [after, backEndHeap, ZStreamRef.put, freeIst, hjz]
      | in_gzstate_strm j =>
        cases he : h.gzstates j <;> simp [after, backEndHeap, ZStreamRef.put, freeIst, he]
    · cases r with
      | tab j =>
        have hjz : h.streams j = some z := hz
        simp [after, backEndHeap, ZStreamRef.put, freeIst, hjz]
      | in_gzstate_strm j =>
        cases he : h.gzstates j <;> simp [after, backEndHeap, ZStreamRef.put, freeIst, he]


#print axioms back_end_public
end ZlibF.Spec.Public.InflateBackEndProof
