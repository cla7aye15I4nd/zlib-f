import ZlibF.Math.UncompressStoredCopy

namespace Zlib.Uncompr.Proof.StoredSliceMath
open C Zlib.Inflate.Proofs
set_option autoImplicit false

theorem copyRange_extract (da wa : Array UInt8) (off src n : Nat)
    (hd : off + n ≤ da.size) (hs : src + n ≤ wa.size) :
    copyRange da wa off src n = da.extract 0 off ++ wa.extract src (src+n) ++ da.extract (off+n) da.size := by
  apply Array.ext_getElem?
  intro i
  rw [copyRange_getElem? da wa off src n hd hs i]
  have hs1 : min off da.size = off := Nat.min_eq_left (by omega)
  have hs2 : min (src+n) wa.size = src+n := Nat.min_eq_left hs
  by_cases h0 : i < off
  · simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs1, hs2, h0, show ¬ off ≤ i by omega, show i < da.size by omega]
  · by_cases h1 : i < off + n
    · have hsrc : src + (i - off) < wa.size := by omega
      simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs1, hs2, h0, h1,
        show off ≤ i by omega, show i - off < n by omega, getElem!_pos wa (src + (i - off)) hsrc]
    · have hshift : off + n + (i - off - n) = i := by omega
      by_cases h2 : i < da.size
      · simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs1, hs2, h0, h1, h2,
          show ¬ i - off < n by omega, show i - off - n < da.size - (off+n) by omega, hshift]
      · have hout : da[i]? = none := Array.getElem?_eq_none (by omega)
        simp [Array.getElem?_append, Array.getElem?_extract, Array.size_extract, hs1, hs2, h0, h1, h2,
          show ¬ i - off < n by omega, show ¬ i - off - n < da.size - (off+n) by omega, hout]


/-- The real copy writes exactly the payload at the requested destination
slice, preserving the entire initial prefix and suffix. -/
theorem copied_array (output input : Array UInt8) (oo io : Nat) (payload : List UInt8)
    (outputRoom : oo+payload.length≤output.size) (inputRoom : io+payload.length≤input.size)
    (slice : payload=(input.toList.drop io).take payload.length) :
    copyRange output input oo io payload.length=
      output.extract 0 oo ++ payload.toArray ++ output.extract (oo+payload.length) output.size := by
  rw [copyRange_extract output input oo io payload.length outputRoom inputRoom]
  have middle : input.extract io (io+payload.length)=payload.toArray := by
    apply Array.toList_inj.mp
    simpa only [Array.toList_extract,List.extract_eq_take_drop,Nat.add_sub_cancel_left,
      List.toList_toArray] using slice.symm
  rw [middle]

theorem copied_slice (output input : Array UInt8) (oo io : Nat) (payload : List UInt8)
    (outputRoom : oo+payload.length≤output.size) (inputRoom : io+payload.length≤input.size)
    (slice : payload=(input.toList.drop io).take payload.length) :
    ((copyRange output input oo io payload.length).toList.drop oo).take payload.length=payload := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,Array.length_toList,size_copyRange]
    omega
  · intro i hi hj
    have bound : i<payload.length := hj
    have actual := copyRange_getElem? output input oo io payload.length outputRoom inputRoom (oo+i)
    simp only [show oo≤oo+i by omega,show oo+i<oo+payload.length by omega,and_self,ite_true,
      Nat.add_sub_cancel_left] at actual
    have physical := congrArg (fun xs : List UInt8 => xs[i]?) slice
    simp only [List.getElem?_take,List.getElem?_drop,bound,ite_true,Array.getElem?_toList] at physical
    have eq := actual.trans physical.symm
    rw [Array.getElem?_eq_getElem (by rw [size_copyRange];omega),List.getElem?_eq_getElem bound] at eq
    simpa only [List.getElem_take,List.getElem_drop,Array.getElem_toList] using Option.some.inj eq

theorem copied_outside (output input : Array UInt8) (oo io : Nat) (payload : List UInt8)
    (outputRoom : oo+payload.length≤output.size) (inputRoom : io+payload.length≤input.size)
    (i : Nat) (outside : i<oo ∨ oo+payload.length≤i) :
    (copyRange output input oo io payload.length)[i]?=output[i]? := by
  rw [copyRange_getElem? output input oo io payload.length outputRoom inputRoom i,if_neg (by omega)]

#print axioms copied_array
#print axioms copied_slice
#print axioms copied_outside
end Zlib.Uncompr.Proof.StoredSliceMath
