import ZlibF.Proof.«inflate.c.fast-view-body-condition-heap-bits-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The fixed fast-call beginning and public output count bound the span
at every continuing output cursor. -/
theorem fast_begin_span_after_body
    {slow : IL} {oo bg next : Nat}
    (count : slow.left.toNat ≤ slow.out_.toNat)
    (made : slow.out_.toNat - slow.left.toNat ≤ oo)
    (beginEq : bg = oo -
      (slow.out_.toNat - slow.left.toNat))
    (current : oo ≤ next)
    (within : next ≤ oo + slow.left.toNat) :
    bg ≤ next ∧ next - bg < 2 ^ 32 := by
  have width := UInt32.toNat_lt slow.out_
  omega

/-- A continuing fast step has the same writable output view, the guarded
pointer comparison, and the span needed by the next body. -/
theorem fast_continuing_output_view
    {h after : Heap} {slow : IL}
    {c : Zlib.Inffast.Ctx} {result : Zlib.Inffast.L}
    {dest : BRef} {output array : Array UInt8}
    {oo bg j next : Nat}
    (sizes : ByteViewSizes h after)
    (heapEq : after = Space.put h dest array)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outPtr : result.out = .ref dest next)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (current : oo ≤ j)
    (progress : oo + slow.left.toNat - next <
      oo + slow.left.toNat - j)
    (margin : next + 258 ≤ oo + slow.left.toNat)
    (count : slow.left.toNat ≤ slow.out_.toNat)
    (made : slow.out_.toNat - slow.left.toNat ≤ oo)
    (beginEq : bg = oo -
      (slow.out_.toNat - slow.left.toNat)) :
    ∃ outputNext,
      Space.get after dest = some outputNext ∧
      outputNext.size = output.size ∧
      Space.ro after dest = false ∧
      oo ≤ next ∧ bg ≤ next ∧ next - bg < 2 ^ 32 ∧
      C.run (Ptr.lt result.out c.end_) after =
        .ok (true, after) := by
  obtain ⟨outputNext, nextGet, sizeEq⟩ :=
    sizes.view outputGet
  have nextWrite : Space.ro after dest = false := by
    rw [heapEq, byte_view_ro_write]
    exact outputWrite
  have nextCurrent : oo ≤ next := by omega
  obtain ⟨beginLe, span⟩ :=
    fast_begin_span_after_body count made beginEq
      nextCurrent (by omega)
  have nextBound : next ≤ outputNext.size := by omega
  have endBound : oo + slow.left.toNat - 257 ≤
      outputNext.size := by omega
  have compare := Ptr.lt_ok (r := dest) (a := outputNext)
    nextGet nextBound endBound
  change (Ptr.lt (.ref dest next)
    (.ref dest (oo + slow.left.toNat - 257))) after =
      .ok (decide (next < oo + slow.left.toNat - 257), after)
      at compare
  have guard : C.run (Ptr.lt result.out c.end_) after =
      .ok (true, after) := by
    rw [outPtr, endPtr]
    change (Ptr.lt (.ref dest next)
      (.ref dest (oo + slow.left.toNat - 257))) after =
        .ok (true, after)
    rw [compare]
    simp [show next < oo + slow.left.toNat - 257 by omega]
  exact ⟨outputNext, nextGet, sizeEq, nextWrite,
    nextCurrent, beginLe, span, guard⟩

/-- A byte-only output step leaves both selected decoder table views
available to the next fast iteration. -/
theorem fast_continuing_table_views
    {h after : Heap} {dest : BRef} {array : Array UInt8}
    {lenRef distRef : CodeRef}
    {lenCodes distCodes : Array Code}
    (heapEq : after = Space.put h dest array)
    (lenGet : Space.get h lenRef = some lenCodes)
    (distGet : Space.get h distRef = some distCodes) :
    Space.get after lenRef = some lenCodes ∧
      Space.get after distRef = some distCodes := by
  subst after
  exact ⟨by rw [byte_view_put_code]; exact lenGet,
    by rw [byte_view_put_code]; exact distGet⟩

/-- Output progress is a strict loop measure and the current distance to
the output limit fits the translated loop's fuel budget. -/
theorem fast_remaining_output_measure
    {slow : IL} {oo j next : Nat}
    (current : oo ≤ j)
    (progress : oo + slow.left.toNat - next <
      oo + slow.left.toNat - j) :
    oo + slow.left.toNat - next <
        oo + slow.left.toNat - j ∧
      oo + slow.left.toNat - j < fuel := by
  have width := UInt32.toNat_lt slow.left
  constructor
  · exact progress
  · apply Zlib.Inffast.Proofs.lt_fuel_of
    omega

end Zlib.Inflate.Proofs
