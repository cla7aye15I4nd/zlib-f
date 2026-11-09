import ZlibF.Proof.«deflate.c.engine.generic-byte-output-interval»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Adjacent exact output slices on one heap concatenate through the same real byte view.
No raw-block or foreign-owner condition is needed. -/
theorem generic_published_bytes_append {h : Heap} {ref : BRef} {offset first second : Nat}
    {left right : List UInt8}
    (one : Bytes h (.ref ref offset) first left)
    (two : Bytes h (.ref ref (offset+first)) second right) :
    Bytes h (.ref ref offset) (first+second) (left++right) := by
  rcases one with ⟨impossible,_⟩ | ⟨view,off,before,pointer,get,_bound,value⟩
  · cases impossible
  · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj pointer
    rcases two with ⟨impossible,_⟩ | ⟨view,off,next,pointer,getNext,boundNext,valueNext⟩
    · cases impossible
    · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj pointer
      have arrays : next=before := Option.some.inj (getNext.symm.trans get)
      subst next
      refine Or.inr ⟨ref,offset,before,rfl,get,by omega,?_⟩
      rw [value,valueNext,← List.drop_drop,← List.take_add]

/-- An unchanged byte view supplies the interval invariant at the initial loop heap
and at private-only stages, for any requested output count. -/
theorem ByteOutputInterval.of_same {h g : Heap} {ref : BRef} {offset produced : Nat}
    (same : Space.get g ref = Space.get h ref) : ByteOutputInterval h g ref offset produced := by
  intro before get
  exact ⟨before,same.trans get,rfl,fun _ _ _ => rfl⟩

end Zlib.Deflate.Engine.Proofs
