import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«deflate.c.public-getdict»

open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.DeflateDictionaryProof

/-- `int deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`
The exact public result, state, frame and ownership contract. -/
theorem deflate_getdict_public : Goal.deflateGetDictionary := by
  intro h r i z s dest hasLength xs hG hdict hdest
  obtain ⟨w,p,q,b,hB⟩ := hG.inv.blocks
  obtain ⟨wa,hwa,hwaSize⟩ := hB.wa
  obtain ⟨src, off, a, hwindow, hget, hfit, hxs⟩ := hdict
  rw [hB.win] at hwindow
  cases hwindow
  have ha : wa = a := Option.some.inj (hwa.symm.trans hget)
  subst a
  have hfill : s.strstart.toNat + s.lookahead.toNat ≤ s.window_size.toNat := by
    have := hG.inv.wsz
    simp at hfit
    omega
  have hws : s.w_size.toNat ≤ 32768 := by
    have := hG.inv.wsize
    have := hG.inv.wbits_hi
    have := Nat.pow_le_pow_right (n := 2) (by decide) hG.inv.wbits_hi
    omega
  have hlen := dictLen_toNat hG.inv.wsz hws hfill
  let n := (dictLen s).toNat
  let start := s.strstart.toNat + s.lookahead.toNat - n
  have hsource : start + n ≤ wa.size := by
    dsimp [start,n]
    simp at hfit
    omega
  have hxs' : xs = (wa.toList.drop start).take n := by
    simpa [start,n,hlen,Nat.min_comm] using hxs
  have hxslen : xs.length = n := by
    rw [hxs']
    simp only [List.length_take, List.length_drop, Array.length_toList]
    omega
  have hlength : UInt32.ofNat xs.length = dictLen s := by
    apply UInt32.toNat_inj.mp
    rw [hxslen]
    simp [n]
  by_cases hnone : dest = .null ∨ dictLen s = 0
  · refine ⟨h, ?_, Or.inl ⟨?_,rfl⟩⟩
    · simpa [C.run, hlength] using deflateGetDictionary_run_nocopy hG.live dest hasLength hnone
    · rcases hnone with hn | hn
      · simp [hn]
      · have hzero : n = 0 := by simp [n, hn]
        simp [hxs', hzero]
  · have hnon : dest ≠ .null := fun e => hnone (Or.inl e)
    have hnz : dictLen s ≠ 0 := fun e => hnone (Or.inr e)
    obtain ⟨hwrite,hsep⟩ := hdest hnon
    rcases hwrite with ⟨hn,_⟩ | ⟨rd,od,da,hd,hda,hro,hroom⟩
    · exact (hnon hn).elim
    · have hdroom : od + n ≤ da.size := by simpa [hxslen] using hroom
      have hsep' : rd ≠ .blk w ∨ od + n ≤ start ∨ start + n ≤ od := by
        simp [Separate, hd, hB.win, hxslen] at hsep
        rcases hsep with h | h | h | h
        · exact (hnz (UInt32.toNat_inj.mp (by simpa [n] using h))).elim
        · have : s.window_size = 0 := UInt64.toNat_inj.mp (by simpa using h)
          have := hG.inv.wsize
          have := hG.inv.wbits_lo
          have := hG.inv.wsz
          have := Nat.pow_le_pow_right (n := 2) (by decide) hG.inv.wbits_lo
          simp at this
          omega
        · exact Or.inl h
        · exact Or.inr (Or.inr (by dsimp [start,n]; omega))
      have hwaSize' : wa.size = s.window_size.toNat := by have := hG.inv.wsz; omega
      have hrun := deflateGetDictionary_run_copy_general hG.live hB hfill dest hasLength hd hda hro hdroom hwa hlen hnz hsep' hwaSize'
      refine ⟨Space.put h rd (copyRange da wa od start n), ?_, ?_⟩
      · simpa [C.run, hlength] using hrun
      · simp only [if_neg hnon]
        right
        have hseg : xs.toArray = wa.extract start (start+n) := by
          rw [hxs']
          apply Array.toList_inj.mp
          simp [Array.toList_extract, List.extract_eq_take_drop]
        refine ⟨rd,od,da,hd,hda,hro,by simpa [hxslen] using hdroom, ?_⟩
        rw [hseg, hxslen]
        congr 1
        exact copyRange_extract da wa od start n hdroom hsource

#print axioms deflate_getdict_public

end ZlibF.Spec.Public.DeflateDictionaryProof
