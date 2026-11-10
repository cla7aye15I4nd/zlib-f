import ZlibF.Math.LZ77Copy
import ZlibF.Proof.«inflate.c.main.macros»
namespace Zlib.Inflate.Proofs.SlowTokenPath
open C Zlib.Inflate ZlibF.Math.LZ77Copy Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Writing the next literal appends precisely that byte to the current
call's previously produced prefix, leaving its older bytes unchanged. -/
theorem written_literal_append (array : Array UInt8) (off count : Nat) (byte : UInt8)
    (fit : off < array.size) (produced : count ≤ off) :
    writtenBytes (array.set! off byte) (off + 1) (count + 1) = writtenBytes array off count ++ [byte] := by
  have base : off - count + count = off := Nat.sub_add_cancel produced
  have preserved : (((array.set! off byte).toList.drop (off - count)).take count) =
      (array.toList.drop (off - count)).take count := by
    apply List.ext_getElem
    · simp
    · intro i left right
      have short : i < count := by have := right; simp only [List.length_take] at this; omega
      have different : off ≠ off - count + i := by omega
      simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList]
      exact Array.getElem_setIfInBounds_ne (by omega) different
  have last : (((array.set! off byte).toList.drop off).take 1) = [byte] := by
    rw [take_succ_drop (array.set! off byte) off 0 (by simp; omega)]
    simp [Array.set!]
  unfold writtenBytes
  rw [show off + 1 - (count + 1) = off - count by omega]
  rw [List.take_add]
  rw [preserved, List.drop_drop, base, last]

#print axioms written_literal_append
end Zlib.Inflate.Proofs.SlowTokenPath
