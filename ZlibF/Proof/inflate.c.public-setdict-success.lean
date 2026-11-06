import ZlibF.Proof.«inflate.c.window-public-mode»
import ZlibF.Proof.«inflate.c.public-setdict»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Adler32.Proofs ZlibF.Spec.Public

private theorem dictionary_set_havedict {h : Heap} {zs : Nat} {st : InflateState} {xs : List UInt8}
    (hd : InflateDictionary h st xs) : InflateDictionary (setI h zs { st with havedict := 1 })
      { st with havedict := 1 } xs := by
  rcases hd with ⟨hz, hxs⟩ | ⟨ref, off, a, hp, ha, hf, hxs⟩
  · exact Or.inl ⟨hz, hxs⟩
  · refine Or.inr ⟨ref, off, a, hp, ?_, hf, hxs⟩
    cases ref <;> simpa [Space.get, setI] using ha

private theorem frame_after_setI {before mid : Heap} {zs : Nat} {changed : Nat → Prop}
    {st : InflateState} (hf : Frame before mid changed) (hc : changed zs) :
    Frame before (setI mid zs st) changed := by
  rcases hf with ⟨hstatic, horacle, hgarbage, hnext, halloc, hframe⟩
  refine ⟨hstatic, horacle, hgarbage, hnext, halloc, ?_⟩
  intro b hl hn
  have hne : b ≠ zs := fun he => hn (he ▸ hc)
  have h := hframe b hl hn
  simpa [setI, upd_ne _ _ _ _ hne] using h

private theorem live_after_setI {before mid : Heap} {zs : Nat} {st : InflateState}
    (hs : mid.istates zs = some st)
    (hl : LiveChange before mid (fun b => InflateOwned zs st b ∧ ¬ before.live b) (fun _ => False)) :
    LiveChange before (setI mid zs { st with havedict := 1 })
      (fun b => InflateOwned zs { st with havedict := 1 } b ∧ ¬ before.live b) (fun _ => False) := by
  have hshape := shape_setI hs { st with havedict := 1 }
  intro b
  simpa [LiveChange, InflateOwned] using (hshape.live b).trans (hl b)

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`
with an accepted checksum appends the exact retained dictionary or returns a
genuine window-allocation error. -/
theorem inflateSetDictionary_success_public {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {off : Nat} {source : BRef} {D : Array UInt8} {L : UInt32} {old xs : List UInt8}
    (hG : Good H r zs z st) (hza : z.zalloc = .fn "zcalloc") (hD : Space.get H source = some D) (hfit : off + L.toNat ≤ D.size)
    (hxs : xs = (D.toList.drop off).take L.toNat) (hold : ZlibF.Spec.Public.InflateDictionary H st old)
    (hsep : ZlibF.Spec.Public.Separate (.ref source off) L.toNat st.window (2 ^ st.wbits.toNat)) (hwrap : st.wrap = 0 ∨ st.mode = DICT)
    (hadler : st.mode = DICT → (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg D off L.toNat)).toUInt64 = st.check) :
    ∃ v H' st', C.run (inflateSetDictionary (some r) (.ref source off) L) H = .ok (v, H') ∧ Good H' r zs z st' ∧
      ((v = Z_OK ∧ st'.havedict = 1 ∧ st'.mode = st.mode ∧
          ZlibF.Spec.Public.InflateDictionary H' st' ((old ++ xs).drop ((old ++ xs).length - 2 ^ st.wbits.toNat)) ∧
          Frame H H' (fun b => StreamRoot r b ∨ InflateOwned zs st b) ∧
          LiveChange H H' (fun b => InflateOwned zs st' b ∧ ¬ H.live b) (fun _ => False)) ∨
       (v = Z_MEM_ERROR ∧ st'.mode = MEM ∧ st.window = .null ∧ H.allocOk H.nalloc = false)) := by
  have hL := hG.live
  obtain ⟨v0, H1, st1, hr1, hG1, hcase⟩ := updatewindow_dictionary_public (copy := L) (source := source) (off := off) (bytes := D)
    hG hza hD hfit hxs hold hsep
  have hadd : OkOn H (Ptr.add (Ptr.ref source off) (L.toNat : Int)) (Ptr.ref source (off + L.toNat)) :=
    Ptr.add_nat_ok (a := D) (by simpa using hD) hfit
  have hadd' : Ptr.add (Ptr.ref source off) (L.toNat : Int) H = .ok (Ptr.ref source (off + L.toNat), H) := hadd
  have hnn : (Ptr.ref source off == (Ptr.null : BPtr)) = false := by simp
  have hr1' : updatewindow (some r) (Ptr.ref source (off + L.toNat)) L H = .ok (v0, H1) := hr1
  have hstate : H.istates zs = some st := hL.hs
  have hrun : inflateSetDictionary (some r) (.ref source off) L H =
      (if v0 = 0 then .ok (Z_OK, setI H1 zs { st1 with havedict := 1 })
       else .ok (Z_MEM_ERROR, setI H1 zs { st1 with mode := MEM })) := by
    have hs1 : H1.istates zs = some st1 := hG1.live.hs
    unfold inflateSetDictionary
    simp only [bind_app, stateCheck_live hL, ldZ_eq, ldI_eq, hL.hz, hL.zst, castI, hL.hs, hnn, bne_self_eq_false,
      Bool.or_self, Bool.false_eq_true, ite_false]
    by_cases hm : st.mode = DICT
    · have hra := adler32_dict_any hD L hfit
      have hck := hadler hm
      have hmb : (st.mode == DICT) = true := by simpa using hm
      simp only [hmb, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1', ite_true, Bool.false_eq_true, ite_false, Bool.and_false, hmb, hm, beq_self_eq_true]
      simp only [bind_app, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1', Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
    · have hw0 : st.wrap = 0 := by rcases hwrap with h | h; exact h; exact absurd h hm
      have hmb : (st.mode == DICT) = false := by simpa using hm
      simp only [hmb, hw0, hadd', hr1', bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false, Bool.and_false]
      simp only [bind_app, hadd', hr1', Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
  have hs1 : H1.istates zs = some st1 := hG1.live.hs
  by_cases hv0 : v0 = 0
  · rcases hcase with ⟨_, hdict⟩ | ⟨h1, _⟩
    · have hmode : st1.mode = st.mode := by
        apply updatewindow_mode_public hG hza hD hfit hsep
        · simpa [hv0] using hr1
        · exact hG1.live.hs
      refine ⟨Z_OK, setI H1 zs { st1 with havedict := 1 }, { st1 with havedict := 1 }, ?_, ?_, Or.inl ⟨rfl, rfl, hmode, ?_, ?_, ?_⟩⟩
      · rw [C.run, hrun, if_pos hv0]
      · exact good_state hG1 rfl hG1.live.mode (hG1.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hG1.inv.bits rfl rfl rfl)
      · exact dictionary_set_havedict hdict
      · have hframe := updatewindow_frame_public hG hza hD hfit hsep (by simpa [hv0] using hr1)
        exact frame_after_setI hframe (Or.inr (Or.inl rfl))
      · have hlive := updatewindow_live_public hG hza hD hfit hsep (by simpa [hv0] using hr1) hG1.live.hs
        exact live_after_setI hG1.live.hs hlive
    · rw [hv0] at h1; exact absurd h1 (by decide)
  · rcases hcase with ⟨h1, _⟩ | ⟨_, hw0, hnok, _, _⟩
    · exact absurd h1 hv0
    · refine ⟨Z_MEM_ERROR, setI H1 zs { st1 with mode := MEM }, { st1 with mode := MEM }, ?_, ?_, Or.inr ⟨rfl, rfl, hw0, hnok⟩⟩
      · rw [C.run, hrun, if_neg hv0]
      · exact good_state hG1 rfl mode_mem (hG1.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl hG1.inv.bits rfl rfl rfl)

#print axioms inflateSetDictionary_success_public
end Zlib.Inflate.Proofs
