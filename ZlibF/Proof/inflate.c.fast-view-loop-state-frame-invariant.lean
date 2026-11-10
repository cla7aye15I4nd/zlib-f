import ZlibF.Proof.«inflate.c.fast-view-body-condition-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- When a fast step writes only a caller byte view, its retained default
state witnesses denote the same stream and inflate-state records. -/
theorem DefaultStateJ.same_records_of_byte_put
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z zNext : ZStream} {s sNext : InflateState}
    {dest : BRef} {array : Array UInt8}
    (before : DefaultStateJ h r zs z s)
    (afterJ : DefaultStateJ (Space.put h dest array) r zs zNext sNext) :
    zNext = z ∧ sNext = s := by
  have streamBefore := before.good.live.hz
  have streamAfter := afterJ.good.live.hz
  rw [byte_view_put_stream] at streamAfter
  have streamEq : zNext = z :=
    Option.some.inj (streamAfter.symm.trans streamBefore)
  have stateBefore := before.good.live.hs
  have stateAfter := afterJ.good.live.hs
  rw [byte_view_put_istates] at stateAfter
  have stateEq : sNext = s :=
    Option.some.inj (stateAfter.symm.trans stateBefore)
  exact ⟨streamEq, stateEq⟩

/-- A nonbreaking distance copy writes only the caller output byte view and
retains the original stream and inflate-state records. -/
theorem FastDistancePost.nonbreaking_byte_put
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {bs : List UInt8} {result : Zlib.Inffast.L}
    {dest : BRef} {output : Array UInt8} {j length : Nat}
    (post : FastDistancePost before after r zs z s slow bs
      result dest output j length)
    (notBroken : result.broke = false) :
    ∃ array, after = Space.put before dest array ∧
      DefaultStateJ after r zs z s := by
  rcases post.2.2.2 with bad | good
  · rcases bad with ⟨_, broke, _, _, _, _⟩
    rw [notBroken] at broke
    cases broke
  · rcases good with ⟨array, current, _, _, _, _, heapEq, _⟩
    exact ⟨array, heapEq, current⟩

/-- The BAD alternative of the distance result cannot be a continuing fast
step; every other continuing result writes only caller output bytes. -/
theorem fast_distance_outcome_nonbreaking_byte_put
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {bs : List UInt8} {result : Zlib.Inffast.L}
    {dest : BRef} {output : Array UInt8} {j length : Nat}
    (outcome :
      FastDistancePost before after r zs z s slow bs result
        dest output j length ∨
      ∃ i, result.broke = true ∧
        after = badHeap before r zs z s i ∧
        DefaultStateJ after r zs
          { z with msg := .ref (.str i) 0 }
          { s with mode := BAD })
    (notBroken : result.broke = false) :
    ∃ array, after = Space.put before dest array ∧
      DefaultStateJ after r zs z s := by
  rcases outcome with post | bad
  · exact post.nonbreaking_byte_put notBroken
  · rcases bad with ⟨_, broke, _, _⟩
    rw [notBroken] at broke
    cases broke

end Zlib.Inflate.Proofs
