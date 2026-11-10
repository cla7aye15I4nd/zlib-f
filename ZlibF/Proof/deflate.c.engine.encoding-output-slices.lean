import ZlibF.Proof.«deflate.c.engine.raw-output-interval»
import ZlibF.Proof.«deflate.c.engine.flush-block-prefix»

/-! # Earlier actual output bytes survive later adjacent output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A later adjacent output interval preserves the exact bytes already
published by earlier iterations, on the final heap. -/
theorem RawOutputInterval.keep_published_bytes {h after : Heap} {ob offset first second : Nat}
    {written : List UInt8} (bytes : Bytes h (.ref (.blk ob) offset) first written)
    (effect : RawOutputInterval h after ob (offset + first) second) :
    Bytes after (.ref (.blk ob) offset) first written := by
  rcases bytes with ⟨impossible, _⟩ | ⟨ref, off, before, pointer, get, bound, value⟩
  · cases impossible
  · obtain ⟨rfl, rfl⟩ := Ptr.ref.inj pointer
    obtain ⟨next, getNext, size, same⟩ := effect before get
    have slice : (next.toList.drop offset).take first = (before.toList.drop offset).take first := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop, Array.length_toList, size]
      · intro i hi hj
        have inside : offset + i < before.size := by
          simp only [List.length_take, List.length_drop, Array.length_toList, size] at hi
          omega
        have insideNext : offset + i < next.size := by omega
        have earlier : ¬ (offset + first ≤ offset + i ∧ offset + i < offset + first + second) := by
          simp only [List.length_take, List.length_drop, Array.length_toList, size] at hi
          omega
        have equal := same (offset + i) inside earlier
        simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList,
          Array.getElem?_eq_getElem insideNext, Array.getElem?_eq_getElem inside, Option.some.injEq] using equal
    exact Or.inr ⟨.blk ob, offset, next, rfl, getNext, by omega, value.trans slice.symm⟩

/-- Adjacent readable output slices on one heap form their exact combined
byte list. The bound follows from the second actual slice. -/
theorem published_bytes_append {h : Heap} {ob offset first second : Nat}
    {left right : List UInt8}
    (one : Bytes h (.ref (.blk ob) offset) first left)
    (two : Bytes h (.ref (.blk ob) (offset + first)) second right) :
    Bytes h (.ref (.blk ob) offset) (first + second) (left ++ right) := by
  rcases one with ⟨impossible, _⟩ | ⟨ref, off, before, pointer, get, _bound, value⟩
  · cases impossible
  · obtain ⟨rfl, rfl⟩ := Ptr.ref.inj pointer
    rcases two with ⟨impossible, _⟩ | ⟨ref, off, next, pointer, getNext, boundNext, valueNext⟩
    · cases impossible
    · obtain ⟨rfl, rfl⟩ := Ptr.ref.inj pointer
      have arrays : next = before := Option.some.inj (getNext.symm.trans get)
      subst next
      refine Or.inr ⟨.blk ob, offset, before, rfl, get, by omega, ?_⟩
      rw [value, valueNext, ← List.drop_drop, ← List.take_add]

end Zlib.Deflate.Engine.Proofs
