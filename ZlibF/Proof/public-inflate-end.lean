import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«inflate.c.end»

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.InflateEndProof

theorem end_frame {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (hz : r.get h = some z) (hw : s.window = .null ∨ ∃ b a, s.window = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false) :
    Frame h (r.put (endHeap h i s) {z with state := none}) (fun b => StreamRoot r b ∨ InflateOwned i s b) := by
  rcases hw with hnull | ⟨w,a,hwin,ha,hro⟩
  · cases r with
    | tab j =>
      have hjz : h.streams j = some z := hz
      simp only [Frame, endHeap, freeIst, freeWin, hnull, ZStreamRef.put, hjz, true_and]
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro b hl hb
      have hi : b ≠ i := fun e => hb (Or.inr (Or.inl e))
      have hj : b ≠ j := fun e => hb (Or.inl (by simpa [StreamRoot] using e))
      simp [upd_ne, hi, hj]
    | in_gzstate_strm j =>
      cases hg : h.gzstates j with
      | none => simp [ZStreamRef.get, hg] at hz
      | some g =>
        simp only [Frame, endHeap, freeIst, freeWin, hnull, ZStreamRef.put, hg, true_and]
        refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
        intro b hl hb
        have hi : b ≠ i := fun e => hb (Or.inr (Or.inl e))
        have hj : b ≠ j := fun e => hb (Or.inl (by simpa [StreamRoot] using e))
        simp [upd_ne, hi, hj]
  · cases r with
    | tab j =>
      have hjz : h.streams j = some z := hz
      simp only [Frame, endHeap, freeIst, freeWin, hwin, ZStreamRef.put, hjz, true_and]
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro b hl hb
      have hi : b ≠ i := fun e => hb (Or.inr (Or.inl e))
      have hj : b ≠ j := fun e => hb (Or.inl (by simpa [StreamRoot] using e))
      have hw : b ≠ w := fun e => hb (Or.inr (Or.inr (by simpa [hwin] using e.symm)))
      simp [upd_ne, hi, hj, hw]
    | in_gzstate_strm j =>
      cases hg : h.gzstates j with
      | none => simp [ZStreamRef.get, hg] at hz
      | some g =>
        simp only [Frame, endHeap, freeIst, freeWin, hwin, ZStreamRef.put, hg, true_and]
        refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
        intro b hl hb
        have hi : b ≠ i := fun e => hb (Or.inr (Or.inl e))
        have hj : b ≠ j := fun e => hb (Or.inl (by simpa [StreamRoot] using e))
        have hw : b ≠ w := fun e => hb (Or.inr (Or.inr (by simpa [hwin] using e.symm)))
        simp [upd_ne, hi, hj, hw]

/-- `int inflateEnd(z_streamp strm)`
The exact public result, state, frame and ownership contract. -/
theorem inflate_end_public : Goal.inflateEnd := by
  intro h r i z s hG hf
  obtain ⟨after, hr, he, hu, hfr, hz, hown, hc⟩ := inflateEnd_safe hG hf
  refine ⟨after, hr, hz, ?_, ?_, ?_, ?_⟩
  · have ho := hown (fun b => h.live b) (fun _ => Iff.rfl)
    intro b
    simpa [LiveChange, InflateOwned, OwnedBy, WinBlk, and_comm] using ho b
  · rw [he]
    exact end_frame hG.live.hz (windowBlock hG.inv.win)
  · rw [he]
    rcases windowBlock hG.inv.win with hnull | ⟨w,a,hwin,ha,hro⟩
    · cases r <;> simp [endHeap, freeIst, freeWin, ZStreamRef.put, hnull] <;> split <;> rfl
    · cases r <;> simp [endHeap, freeIst, freeWin, ZStreamRef.put, hwin] <;> split <;> rfl
  · rw [he]
    rcases windowBlock hG.inv.win with hnull | ⟨w,a,hwin,ha,hro⟩
    · cases r <;> simp [endHeap, freeIst, freeWin, ZStreamRef.put, hnull] <;> split <;> rfl
    · cases r <;> simp [endHeap, freeIst, freeWin, ZStreamRef.put, hwin] <;> split <;> rfl

#print axioms inflate_end_public

end ZlibF.Spec.Public.InflateEndProof
