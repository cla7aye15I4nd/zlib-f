import ZlibF.Proof.«inflate.c.fast-view-body-bounded-progress-invariant»
import ZlibF.Proof.«inflate.c.fast-view-geometry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The fast-loop guard reserves all 258 bytes that one body can emit. -/
theorem fast_output_max_room_of_guard
    {h : Heap} {slow : IL} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx} {dest : BRef}
    {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (avail : 258 ≤ slow.left.toNat)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    j + 258 ≤ oo + slow.left.toNat := by
  have room := fast_output_room_of_guard
    (l := { l with len := 258 })
    (by simpa only using outPtr) endPtr outputGet outputSize
    current avail (by simp) (by simpa only using guard)
  exact room.2.2

/-- A nonbreaking fast body strictly decreases the remaining output-space
measure, even when its table entries consume no input bits. -/
theorem fast_body_output_measure_decreases
    {h : Heap} {slow : IL} {l result : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx} {dest : BRef}
    {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (avail : 258 ≤ slow.left.toNat)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (progress : result.broke = true ∨
      ∃ next, result.out = .ref dest next ∧ j < next ∧
        next ≤ j + 258) :
    result.broke = true ∨
      ∃ next, result.out = .ref dest next ∧
        next ≤ oo + slow.left.toNat ∧
        oo + slow.left.toNat - next <
          oo + slow.left.toNat - j := by
  rcases progress with broke | ⟨next, nextPtr, advance, bound⟩
  · exact Or.inl broke
  · have room := fast_output_max_room_of_guard outPtr endPtr
      outputGet outputSize current avail guard
    exact Or.inr ⟨next, nextPtr, by omega, by omega⟩

end Zlib.Inflate.Proofs
