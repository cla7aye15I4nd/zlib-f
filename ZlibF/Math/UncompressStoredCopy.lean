import ZlibF.Proof.«inflate.c.ring»

namespace Zlib.Uncompr.Proof.StoredCopyMath
open C Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A stored memcpy filling this complete destination copies exactly the
physical source prefix. Array values, not just the written length, agree. -/
theorem copied_payload (output input : Array UInt8) (off : Nat) (payload : List UInt8)
    (size : output.size = payload.length) (room : off+payload.length ≤ input.size)
    (slice : payload = (input.toList.drop off).take payload.length) :
    copyRange output input 0 off payload.length = payload.toArray := by
  apply Array.ext
  · simp only [size_copyRange,size,List.size_toArray]
  · intro i left right
    have bound : i < payload.length := by simpa only [List.size_toArray] using right
    have copy := copyRange_getElem? output input 0 off payload.length (by omega) room i
    simp only [Nat.zero_le, Nat.zero_add,bound,and_self,ite_true,Nat.sub_zero] at copy
    have fromSlice := congrArg (fun xs : List UInt8 => xs[i]?) slice
    simp only [List.getElem?_take,List.getElem?_drop,bound,ite_true,Array.getElem?_toList] at fromSlice
    have value : input[off+i]? = payload.toArray[i]? := by
      simpa only [List.getElem?_toArray] using fromSlice.symm
    have equal := copy.trans value
    rw [Array.getElem?_eq_getElem left,Array.getElem?_eq_getElem right] at equal
    exact Option.some.inj equal

#print axioms copied_payload
end Zlib.Uncompr.Proof.StoredCopyMath
