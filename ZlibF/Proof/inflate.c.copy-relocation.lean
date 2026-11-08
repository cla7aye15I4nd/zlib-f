import ZlibF.Proof.«inflate.c.copy-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The exact C subtraction and addition relocate any in-bounds dynamic
code cursor, including the one-past `next` cursor. -/
theorem copy_dynamic_code_relocation
    {h : Heap} {old fresh off : Nat} {source target : InflateState}
    (sourceGet : h.istates old = some source)
    (targetGet : h.istates fresh = some target)
    (sourceSize : source.codes.size = 1444)
    (targetSize : target.codes.size = 1444)
    (bound : off ≤ 1444) :
    C.run (do
      let difference ← Ptr.diff (.ref (CodeRef.istate_codes old) off)
        (.ref (CodeRef.istate_codes old) 0)
      Ptr.add (.ref (CodeRef.istate_codes fresh) 0) difference.toInt) h =
      .ok (.ref (CodeRef.istate_codes fresh) off, h) := by
  have oldCodes : Space.get h (CodeRef.istate_codes old) = some source.codes :=
    CodeRef.get_istate_codes sourceGet
  have newCodes : Space.get h (CodeRef.istate_codes fresh) = some target.codes :=
    CodeRef.get_istate_codes targetGet
  have diff : C.run (Ptr.diff (.ref (CodeRef.istate_codes old) off)
      (.ref (CodeRef.istate_codes old) 0)) h =
      .ok (Int64.ofInt (off : Int), h) := by
    have rule := Ptr.diff_ok (r := CodeRef.istate_codes old)
      (a := source.codes) (o1 := off) (o2 := 0) oldCodes
      (by omega) (by omega)
      (by omega : -(2 ^ 63 : Int) ≤ (off : Int) - 0 ∧
        (off : Int) - 0 < 2 ^ 63)
    simpa [C.run, OkOn] using rule
  have toInt : (Int64.ofInt (off : Int)).toInt = off := by
    rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have add : C.run (Ptr.add (.ref (CodeRef.istate_codes fresh) 0) (off : Int)) h =
      .ok (.ref (CodeRef.istate_codes fresh) off, h) := by
    have rule := Ptr.add_nat_ok (r := CodeRef.istate_codes fresh)
      (a := target.codes) (off := 0) (n := off) newCodes (by omega)
    simpa [C.run, OkOn] using rule
  change (Ptr.diff (.ref (CodeRef.istate_codes old) off)
    (.ref (CodeRef.istate_codes old) 0)) h = _ at diff
  change (Ptr.add (.ref (CodeRef.istate_codes fresh) 0) (off : Int)) h = _ at add
  simp [C.run, bind_app, diff, toInt, add]

#print axioms copy_dynamic_code_relocation
end Zlib.Inflate.Proofs
