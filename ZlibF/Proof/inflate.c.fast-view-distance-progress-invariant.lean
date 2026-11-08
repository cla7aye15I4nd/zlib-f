import ZlibF.Proof.«inflate.c.fast-view-body-complete-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A checked distance suffix either stops with BAD or advances the output
pointer by its positive match length. -/
theorem FastDistancePost.break_or_output_advance
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {bs : List UInt8} {result : Zlib.Inffast.L}
    {dest : BRef} {output : Array UInt8} {j length : Nat}
    (post : FastDistancePost before after r zs z s slow bs result
      dest output j length)
    (positive : 0 < length) :
    result.broke = true ∨
      ∃ next, result.out = .ref dest next ∧ j < next := by
  rcases post.2.2.2 with bad | good
  · rcases bad with ⟨_, broke, _⟩
    exact Or.inl broke
  · rcases good with ⟨_, _, out, _⟩
    exact Or.inr ⟨j + length, out, by omega⟩

/-- A successful distance copy advances by at most the maximum match length
and preserves the size and writability of the output view. -/
theorem FastDistancePost.break_or_bounded_output_advance
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {bs : List UInt8} {result : Zlib.Inffast.L}
    {dest : BRef} {output : Array UInt8} {j length : Nat}
    (post : FastDistancePost before after r zs z s slow bs result
      dest output j length)
    (positive : 0 < length) (bounded : length ≤ 258) :
    result.broke = true ∨
      ∃ next array,
        result.out = .ref dest next ∧
        j < next ∧ next ≤ j + 258 ∧
        Space.get after dest = some array ∧
        array.size = output.size ∧
        Space.ro after dest = false := by
  rcases post.2.2.2 with bad | good
  · rcases bad with ⟨_, broke, _⟩
    exact Or.inl broke
  · rcases good with ⟨array, _, out, get, size, write, _, _⟩
    exact Or.inr ⟨j + length, array, out, by omega, by omega,
      get, size, write⟩

end Zlib.Inflate.Proofs
