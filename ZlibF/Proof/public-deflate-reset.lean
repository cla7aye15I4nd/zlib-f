import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«deflate.c.life.reset»

open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.DeflateResetProof

private theorem abswrap_properties (d : DeflateState) (hlo : -2 ≤ d.wrap.toInt) (hhi : d.wrap.toInt ≤ 2) :
    (absWrap d.wrap).toInt = d.wrap.toInt.natAbs ∧
    (if absWrap d.wrap == 2 then (0 : UInt64) else 1) =
      if d.wrap = 2 ∨ d.wrap = -2 then 0 else 1 := by
  have hc : d.wrap.toInt = -2 ∨ d.wrap.toInt = -1 ∨ d.wrap.toInt = 0 ∨ d.wrap.toInt = 1 ∨ d.wrap.toInt = 2 := by omega
  have he : d.wrap = Int32.ofInt d.wrap.toInt := (Int32.ofInt_toInt d.wrap).symm
  rcases hc with hh | hh | hh | hh | hh <;> rw [hh] at he <;>
    simp [absWrap, he]

private theorem local_fillRange_succ {T : Type} (d : Array T) (off n : Nat) (v : T) :
    fillRange d off (n + 1) v = (fillRange d off n v).set! (off + n) v := by
  unfold fillRange; rw [List.range_succ, List.foldl_append]; rfl


private theorem local_getElem_fillRange {T : Type} (d : Array T) (off n : Nat) (v : T) (i : Nat) (hfit : off + n ≤ d.size) :
    (fillRange d off n v)[i]? = if off ≤ i ∧ i < off + n then some v else d[i]? := by
  induction n generalizing i with
  | zero => simp [fillRange]; intro h1 h2; omega
  | succ n ih =>
    rw [local_fillRange_succ, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ih i (by omega)]
    have hs : (fillRange d off n v).size = d.size := size_fillRange _ _ _ _
    by_cases hi : off + n = i
    · subst hi
      simp [hs, show off + n < d.size by omega]
    · simp [hi]
      by_cases h1 : off ≤ i ∧ i < off + n
      · simp [h1]; omega
      · simp [h1]; intro _ ; omega


private theorem clear_head_get (qa : Array UInt16) (n : Nat) (hn : 1 ≤ n) (hs : n ≤ qa.size)
    (j : Nat) (hj : j < n) : (clearHead qa n)[j]? = some 0 := by
  have hf : 0 + (n - 1) ≤ (qa.set! (n - 1) 0).size := by simp; omega
  have he := local_getElem_fillRange (qa.set! (n - 1) 0) 0 (n - 1) (0 : UInt16) j hf
  unfold clearHead
  rw [he]
  by_cases hp : j < n - 1
  · simp [hp]
  · have hx : j = n - 1 := by omega
    subst j
    simp [Array.set!_eq_setIfInBounds, show n - 1 < qa.size by omega]

/-- `int deflateReset(z_streamp strm)`; reset progress and clear the dictionary hash.
The exact public result, state, frame and ownership contract. -/
theorem deflate_reset_public : Goal.deflateReset := by
  intro h r i z s hG
  obtain ⟨a1,a2,a3,q,qa,after,hr,ha1,ha2,ha3,hq,hqa,he,hgood,hlive⟩ := deflateReset_safe hG
  let z' := rkZ z s
  let s' := lmD (rkPost i (rkMid s) a1 a2 a3)
  refine ⟨after,z',s',hr,hgood,?_⟩
  have hw := abswrap_properties s hG.inv.wrap_lo hG.inv.wrap_hi
  have hadler : (if absWrap s.wrap = 2 then (0 : UInt64) else 1) =
      if s.wrap = 2 ∨ s.wrap = -2 then 0 else 1 := by simpa using hw.2
  have hbytes : after.bytes = h.bytes := by rw [he]; simp [setW]
  have hnalloc : after.nalloc = h.nalloc := by rw [he]; simp [setW]
  have hhashpos : 1 ≤ s.hash_size.toNat := by
    rw [hG.inv.hsize]
    exact Nat.one_le_pow _ _ (by decide)
  obtain ⟨w,p,q',b,hB⟩ := hG.inv.blocks
  have hqq : q = q' := by
    have hh := hB.head
    rw [hq] at hh
    cases hh
    rfl
  subst q'
  obtain ⟨qa',hqa',hsize⟩ := hB.qa
  have haeq : qa = qa' := Option.some.inj (hqa.symm.trans hqa')
  have hbound : s.hash_size.toNat ≤ qa.size := by rw [haeq, hsize]; exact Nat.le_refl _
  have hzero : ∀ ref off a, s.head = .ref ref off → Space.get after ref = some a →
      ∀ j, j < s.hash_size.toNat → a[off+j]? = some 0 := by
    intro ref off a hptr hget j hj
    rw [hq] at hptr
    cases hptr
    have hget' : after.words q = some a := by simpa [Space.get] using hget
    have hz : after.words q = some (clearHead qa s.hash_size.toNat) := by
      rw [he]
      simp [setW]
    have : a = clearHead qa s.hash_size.toNat := Option.some.inj (hget'.symm.trans hz)
    subst a
    simpa using clear_head_get qa s.hash_size.toNat hhashpos hbound j hj
  have hframe : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) := by
    rw [he]
    cases r with
    | tab k =>
      have hk : h.streams k = some z := hG.live.hz
      simp only [Frame, setD, setW, ZStreamRef.put, hk, true_and]
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro x hx hn
      have hi : x ≠ i := fun e => hn (Or.inr (Or.inl e))
      have hk : x ≠ k := fun e => hn (Or.inl (by simpa [StreamRoot] using e))
      have hq' : x ≠ q := fun e => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [hq] using e.symm))))))
      simp [upd_ne, hi, hk, hq']
    | in_gzstate_strm k =>
      cases hk : h.gzstates k with
      | none =>
        have hz := hG.live.hz
        simp [ZStreamRef.get, hk] at hz
      | some g =>
        simp only [Frame, setD, setW, ZStreamRef.put, hk, true_and]
        refine ⟨Nat.le_refl _, Nat.le_refl _, ?_⟩
        intro x hx hn
        have hi : x ≠ i := fun e => hn (Or.inr (Or.inl e))
        have hk : x ≠ k := fun e => hn (Or.inl (by simpa [StreamRoot] using e))
        have hq' : x ≠ q := fun e => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [hq] using e.symm))))))
        simp [upd_ne, hi, hk, hq']
  simp [z', s', rkZ, lmD, rkPost, rkPost3, rkMid,
    Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec,
    hw.1, hadler, hbytes, hnalloc, hframe, LiveChange, hlive]
  exact hzero

#print axioms deflate_reset_public

end ZlibF.Spec.Public.DeflateResetProof
