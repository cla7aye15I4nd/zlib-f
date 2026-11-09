import ZlibF.Proof.«deflate.c.engine.encoding-output-slices»

/-! Internal byte-view output effects. The existing raw interval relation is unchanged. -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An internal effect on a concrete byte view: its extent and every byte outside the
specified output interval are preserved. Existence of that view is not assumed here. -/
def ByteOutputInterval (h g : Heap) (ref : BRef) (offset produced : Nat) : Prop :=
  ∀ before, Space.get h ref = some before →
    ∃ next, Space.get g ref = some next ∧ next.size = before.size ∧
      ∀ j, j < before.size → ¬ (offset ≤ j ∧ j < offset + produced) → next[j]? = before[j]?

/-- The range component of a single-region public frame supplies the generic interval effect.
No ownership or changed-object premise is required for this implication. -/
theorem ByteOutputInterval.of_buffer_frame {h g : Heap} {ref : BRef} {offset produced : Nat}
    {changed : Nat → Prop}
    (frame : BufferFrame h g changed [⟨.ref ref offset,produced⟩]) :
    ByteOutputInterval h g ref offset produced := by
  intro before get
  obtain ⟨next,getNext,size,same⟩ :=
    frame.2 ⟨.ref ref offset,produced⟩ (by simp) ref offset before rfl get
  refine ⟨next,getNext,size,?_⟩
  intro j bound outside
  apply same j bound
  rintro ⟨region,member,off,pointer,lower,upper⟩
  simp only [List.mem_singleton] at member
  subst region
  have equal : offset=off := (Ptr.ref.inj pointer).2
  rw [← equal] at lower upper
  exact outside ⟨lower,upper⟩

/-- Actual adjacent byte-view effects compose at the advanced output cursor. -/
theorem ByteOutputInterval.trans {h g k : Heap} {ref : BRef} {offset first second : Nat}
    (one : ByteOutputInterval h g ref offset first)
    (two : ByteOutputInterval g k ref (offset+first) second) :
    ByteOutputInterval h k ref offset (first+second) := by
  intro before get
  obtain ⟨middle,getMiddle,sizeMiddle,sameMiddle⟩ := one before get
  obtain ⟨next,getNext,sizeNext,sameNext⟩ := two middle getMiddle
  refine ⟨next,getNext,sizeNext.trans sizeMiddle,?_⟩
  intro j bound outside
  have firstOutside : ¬ (offset≤j ∧ j<offset+first) := by omega
  have secondOutside : ¬ (offset+first≤j ∧ j<offset+first+second) := by omega
  exact (sameNext j (by omega) secondOutside).trans (sameMiddle j bound firstOutside)

/-- A later adjacent output write preserves the exact already-published byte prefix
on the final heap, for any concrete byte view. -/
theorem ByteOutputInterval.keep_published_bytes {h after : Heap} {ref : BRef} {offset first second : Nat}
    {written : List UInt8} (bytes : Bytes h (.ref ref offset) first written)
    (effect : ByteOutputInterval h after ref (offset+first) second) :
    Bytes after (.ref ref offset) first written := by
  rcases bytes with ⟨impossible,_⟩ | ⟨view,off,before,pointer,get,bound,value⟩
  · cases impossible
  · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj pointer
    obtain ⟨next,getNext,size,same⟩ := effect before get
    have slice : (next.toList.drop offset).take first = (before.toList.drop offset).take first := by
      apply List.ext_getElem
      · simp only [List.length_take,List.length_drop,Array.length_toList,size]
      · intro i hi hj
        have inside : offset+i<before.size := by
          simp only [List.length_take,List.length_drop,Array.length_toList,size] at hi
          omega
        have insideNext : offset+i<next.size := by omega
        have earlier : ¬ (offset+first≤offset+i ∧ offset+i<offset+first+second) := by
          simp only [List.length_take,List.length_drop,Array.length_toList,size] at hi
          omega
        have equal := same (offset+i) inside earlier
        simpa only [List.getElem_take,List.getElem_drop,Array.getElem_toList,
          Array.getElem?_eq_getElem insideNext,Array.getElem?_eq_getElem inside,Option.some.injEq] using equal
    exact Or.inr ⟨ref,offset,next,rfl,getNext,by omega,value.trans slice.symm⟩

end Zlib.Deflate.Engine.Proofs
