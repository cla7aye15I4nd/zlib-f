import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«deflate.c.life.reset»
import ZlibF.Spec.Functional.Lifecycle

open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.DeflateResetKeepProof

private theorem abswrap_properties (d : DeflateState) (hlo : -2 ≤ d.wrap.toInt) (hhi : d.wrap.toInt ≤ 2) :
    (absWrap d.wrap).toInt = d.wrap.toInt.natAbs ∧
    (if absWrap d.wrap == 2 then (0 : UInt64) else 1) =
      if d.wrap = 2 ∨ d.wrap = -2 then 0 else 1 := by
  have hc : d.wrap.toInt = -2 ∨ d.wrap.toInt = -1 ∨ d.wrap.toInt = 0 ∨ d.wrap.toInt = 1 ∨ d.wrap.toInt = 2 := by omega
  have he : d.wrap = Int32.ofInt d.wrap.toInt := (Int32.ofInt_toInt d.wrap).symm
  rcases hc with hh | hh | hh | hh | hh <;> rw [hh] at he <;>
    simp [absWrap, he]

/-- `int deflateResetKeep(z_streamp strm)`; reset progress while retaining the match history.
The exact public result, state, frame and ownership contract. -/
theorem deflate_resetkeep_public : Goal.deflateResetKeep := by
  intro h r i z s hG
  obtain ⟨a1,a2,a3,after,hr,he,ha1,ha2,ha3,hgood,hlive⟩ := deflateResetKeep_safe hG
  let z' := rkZ z s
  let s' := rkPost i (rkMid s) a1 a2 a3
  refine ⟨after,z',s',hr,hgood,?_⟩
  have hw := abswrap_properties s hG.inv.wrap_lo hG.inv.wrap_hi
  have hadler : (if absWrap s.wrap = 2 then (0 : UInt64) else 1) =
      if s.wrap = 2 ∨ s.wrap = -2 then 0 else 1 := by simpa using hw.2
  have hbytes : after.bytes = h.bytes := by rw [he]; simp
  have hwords : after.words = h.words := by rw [he]; simp
  have hnalloc : after.nalloc = h.nalloc := by rw [he]; simp
  have hframe : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) := by
    rw [he]
    cases r with
    | tab j =>
      have hj : h.streams j = some z := hG.live.hz
      simp only [Frame, setD, ZStreamRef.put, hj, true_and]
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro b hb hn
      have hi : b ≠ i := fun e => hn (Or.inr (Or.inl e))
      have hj : b ≠ j := fun e => hn (Or.inl (by simpa [StreamRoot] using e))
      simp [upd_ne, hi, hj]
    | in_gzstate_strm j =>
      cases hj : h.gzstates j with
      | none =>
        have hz := hG.live.hz
        simp [ZStreamRef.get, hj] at hz
      | some g =>
        simp only [Frame, setD, ZStreamRef.put, hj, true_and]
        refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
        intro b hb hn
        have hi : b ≠ i := fun e => hn (Or.inr (Or.inl e))
        have hj : b ≠ j := fun e => hn (Or.inl (by simpa [StreamRoot] using e))
        simp [upd_ne, hi, hj]
  simp [z', s', rkZ, rkPost, rkPost3, rkMid,
    Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec,
    hw.1, hadler, hbytes, hwords, hnalloc, hframe, LiveChange, hlive]

#print axioms deflate_resetkeep_public

end ZlibF.Spec.Public.DeflateResetKeepProof
