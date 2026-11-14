import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«inflate.c.public-getdict»
import ZlibF.Spec.Functional.Lifecycle
import ZlibF.Spec.Functional.Api.Basic

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.InflateDictionaryProof

/-- `int inflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`
The exact public result, state, frame and ownership contract. -/
theorem inflate_getdict_public : Goal.inflateGetDictionary := by
  intro h r i z s dest dl xs hG hdict hdest
  have hwn : s.wnext.toNat ≤ s.whave.toNat := by
    rcases Nat.lt_or_ge s.whave.toNat s.wsize.toNat with h | h
    · have := hG.inv.win.eq h; omega
    · have := hG.inv.win.wn; have := hG.inv.win.hv; omega
  have hsub : (s.whave - s.wnext).toNat = s.whave.toNat - s.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact hwn)
  have hxslen : xs.length = s.whave.toNat := by
    rcases hdict with ⟨hzero,rfl⟩ | ⟨rr,oo,aa,hwin,hget,hfit,hxs⟩
    · simp [hzero]
    · rw [hxs]
      simp only [List.length_append, List.length_take, List.length_drop, Array.length_toList, hsub]
      have hv := hG.inv.win.hv
      omega
  have hlength : UInt32.ofNat xs.length = s.whave := by
    apply UInt32.toNat_inj.mp
    rw [hxslen]
    simp
  by_cases hnone : dest = .null ∨ s.whave = 0
  · refine ⟨h, ?_, Or.inl ⟨?_,rfl⟩⟩
    · unfold C.run inflateGetDictionary
      rcases hnone with hd | hw
      · cases dl <;> simp [stateCheck_live hG.live, ldZ_eq, ldI_eq, hG.live.hz, hG.live.zst, castI, hG.live.hs, hd, hlength]
      · cases dl <;> simp [stateCheck_live hG.live, ldZ_eq, ldI_eq, hG.live.hz, hG.live.zst, castI, hG.live.hs, hw, hlength]
    · rcases hnone with hd | hw
      · simp [hd]
      · have : xs = [] := List.length_eq_zero_iff.mp (by simpa [hw] using hxslen)
        simp [this]
  · have hnon : dest ≠ .null := fun h => hnone (Or.inl h)
    have hpos : s.whave ≠ 0 := fun h => hnone (Or.inr h)
    have hposNat : 0 < s.whave.toNat := by
      have : s.whave.toNat ≠ 0 := fun h => hpos (UInt32.toNat_inj.mp (by simpa using h))
      omega
    obtain ⟨w,a,hwin,ha,hro,hsize⟩ : ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧ a.size = 2 ^ s.wbits.toNat := by
      rcases hG.inv.win.block with hn | hx
      · have := hG.inv.win.nullws hn
        have := hG.inv.win.hv
        simp_all
      · exact hx
    have hwsize : s.wsize.toNat = a.size := by
      rcases hG.inv.win.ws with hz | hz
      · have := hG.inv.win.hv; omega
      · omega
    have hwh : s.whave.toNat ≤ a.size := by have := hG.inv.win.hv; omega
    have hxs : xs = (a.toList.drop s.wnext.toNat).take (s.whave.toNat - s.wnext.toNat) ++
        a.toList.take s.wnext.toNat := by
      rcases hdict with ⟨hz,_⟩ | ⟨rr,oo,aa,hp,hget,hfit,hxs⟩
      · exact (hpos hz).elim
      · rw [hwin] at hp
        cases hp
        have heq : a = aa := Option.some.inj (ha.symm.trans hget)
        subst aa
        simpa [hsub] using hxs
    obtain ⟨hwrite,hsep⟩ := hdest hnon
    rcases hwrite with ⟨hn,_⟩ | ⟨rd,od,D,hd,hD,hroD,hroom⟩
    · exact (hnon hn).elim
    · have hroom' : od + s.whave.toNat ≤ D.size := by simpa [hxslen] using hroom
      have hne : rd ≠ BRef.blk w := by
        intro he
        subst rd
        have hD' : D = a := Option.some.inj (hD.symm.trans ha)
        subst D
        simp [Separate, hd, hwin, hxslen] at hsep
        omega
      have hrun := inflateGetDictionary_copy_general (dl := dl) hG.live hwin ha hD hroD hne hpos hwn hwh hroom'
      refine ⟨Space.put h rd (getDictBytes D a od s.wnext.toNat s.whave.toNat), ?_, ?_⟩
      · simpa [C.run, hd, hlength] using hrun
      · simp only [ite_eq_right hnon]
        right
        have hseg : xs.toArray = a.extract s.wnext.toNat s.whave.toNat ++ a.extract 0 s.wnext.toNat := by
          rw [hxs]
          apply Array.toList_inj.mp
          simp [Array.toList_extract, List.extract_eq_take_drop, hwn]
        refine ⟨rd,od,D,hd,hD,hroD,by simpa [hxslen] using hroom', ?_⟩
        rw [hseg, hxslen]
        congr 1
        exact ring_copy_extract D a od s.wnext.toNat s.whave.toNat hwn hwh hroom'

#print axioms inflate_getdict_public

end ZlibF.Spec.Public.InflateDictionaryProof
