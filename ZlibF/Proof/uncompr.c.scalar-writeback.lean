import ZlibF.Proof.«uncompr.c.writeback-support»

/-!
# Writable scalar stores outside an active decoder

The actual writer initializes any writable eight-byte interval. Its exact Store,
initialized value, shape and disjoint-cell observations need no prior integer
value or decoder invariant. Compatibility wrappers can retain source order.
-/

namespace Zlib.Uncompr.Proof.ScalarWriteback
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Writeback

/-- An actual arbitrary-view scalar store needs no active decoder or initialized old integer. It retains
heap shape and every disjoint scalar cell, including cells sharing its byte
allocation. This supports the outer compatibility-wrapper writebacks. -/
theorem writable_scalar_store (h : Heap) (p : BPtr) (value : UInt64)
    (writable : Writable h p 8) (uniq : Uniq h) (fresh : Fresh h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ∃ after, C.run (store64 p value) h = .ok ((), after) ∧
      Store h p (lengthBytes value) after ∧ LengthCell after p value ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      (∀ q previous, LengthCell h q previous → Separate q 8 p 8 → LengthCell after q previous) := by
  rcases writable with null | ⟨ref, off, a, ptr, get, write, room⟩
  · simp at null
  · subst p
    let array := scalarSlice a off value
    let after := Space.put h ref array
    have newGet : Space.get after ref = some array := byte_view_get_put get write array
    have newWrite : Space.ro after ref = false := by rw [byte_view_ro_write]; exact write
    have size := scalarSlice_size a off value room
    have shape := byte_view_put_shape get write array
    have written : LengthCell after (.ref ref off) value := by
      constructor
      · exact Or.inr ⟨ref, off, array, rfl, newGet, by rw [size]; exact room,
          (scalarSlice_bytes a off value room).symm⟩
      · exact Or.inr ⟨ref, off, array, rfl, newGet, newWrite, by rw [size]; exact room⟩
    refine ⟨after, store64_slice_run h ref a off value get write room,
      Or.inr ⟨ref, off, a, rfl, get, write, ?_, ?_⟩, written, ?_,
      shape.uniq uniq, shape.fresh (byte_view_put_nextBlk h ref array) fresh,
      (byte_view_sizes_put get write array size).platform platform, ?_⟩
    · simpa [lengthBytes] using room
    · simp only [lengthBytes, List.length_map, List.length_range]
      rfl
    · intro x
      simpa only [not_false_eq_true, and_true, or_false] using shape.live x
    · intro q previous previousCell separate
      exact scalarSlice_keep_cell get write room previousCell separate

/-- The exact scalar Store relation changes no library constants. -/
theorem scalar_store_globals {h after : Heap} {p : BPtr} {value : UInt64}
    (store : Store h p (lengthBytes value) after) (globals : LibraryGlobals h) :
    LibraryGlobals after := by
  rcases store with ⟨_, same⟩ | ⟨ref, off, array, _, _, _, _, same⟩
  · rw [same]
    exact globals
  · rw [same]
    change (Space.put h ref _).static = _
    rw [byte_view_put_static]
    exact globals

#print axioms writable_scalar_store
end Zlib.Uncompr.Proof.ScalarWriteback
