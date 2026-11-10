import ZlibF.Math.InflatePrefixes

/-! # Exact byte observations reflected by the independent format encoding -/

namespace ZlibF.Math.DeflateEncoding
open ZlibF.Spec
set_option autoImplicit false

/-- Equality of independent transmission bits fixes the complete byte list. -/
theorem encoded_bytes_injective {left right : List UInt8}
    (bits : bytesToBits left = bytesToBits right) : left = right := by
  have forward : left <+: right := ZlibF.Spec.Api.Proofs.bytesToBits_prefix_reflect (by rw [bits]; exact ⟨[], by simp⟩)
  have backward : right <+: left := ZlibF.Spec.Api.Proofs.bytesToBits_prefix_reflect (by rw [bits]; exact ⟨[], by simp⟩)
  obtain ⟨tail, equal⟩ := forward
  have length := backward.length_le
  have empty : tail = [] := by
    have counts := congrArg List.length equal
    simp only [List.length_append] at counts
    cases tail with
    | nil => rfl
    | cons byte rest => simp only [List.length_cons] at counts; omega
  simpa only [empty, List.append_nil] using equal

/-- One in-bounds observed array byte fixes its exact list slice. -/
theorem array_one_slice {array : Array UInt8} {offset : Nat} {byte : UInt8}
    (bound : offset < array.size) (value : array[offset]? = some byte) :
    (array.toList.drop offset).take 1 = [byte] := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Array.length_toList, List.length_cons, List.length_nil]
    omega
  · intro i hi hj
    have zero : i = 0 := by simp only [List.length_cons, List.length_nil] at hj; omega
    subst i
    have equal : array[offset] = byte :=
      Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans value)
    simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList, Nat.add_zero, List.getElem_cons_zero] using equal

end ZlibF.Math.DeflateEncoding
