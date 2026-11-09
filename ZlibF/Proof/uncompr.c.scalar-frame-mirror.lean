import ZlibF.Proof.«inflate.c.buffer-frame-compose»

/-!
# Mirroring exact byte stores across caller frames

These are heap-relation lemmas. They assume no decoder invariant, global shape
or writability of the expected heap. An actual Store and an old live root outside
the frame footprint supply the exact expected view, mutability and bounds.
-/

namespace ZlibF.Spec.Public
open C Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A frame retains an admitted old byte object's full view and mutability.
Static views use the frame's exact static equality; all represented byte references
and arbitrary offsets are included. -/
theorem Frame.byte_view_eq
    {expected actual : Heap} {changed : Nat → Prop} {ref : BRef} {off : Nat}
    (frame : Frame expected actual changed)
    (outside : ∀ b, ByteRoot (.ref ref off) b → expected.live b ∧ ¬ changed b) :
    Space.get actual ref = Space.get expected ref ∧ Space.ro actual ref = Space.ro expected ref := by
  cases ref with
  | blk b =>
    obtain ⟨live, allowed⟩ := outside b rfl
    have slots := frame.2.2.2.2.2 b live allowed
    exact ⟨slots.1, slots.2.2.2.2.2.2.2⟩
  | dstate_depth b =>
    obtain ⟨live, allowed⟩ := outside b rfl
    have slots := frame.2.2.2.2.2 b live allowed
    constructor
    · simp only [Space.get, slots.2.2.2.2.1]
    · rfl
  | str i => exact ⟨rfl, rfl⟩
  | st_dist_code =>
    constructor
    · simp only [Space.get, ← frame.1]
    · rfl
  | st_length_code =>
    constructor
    · simp only [Space.get, ← frame.1]
    · rfl

/-- Exact Store preserves object presence, including the empty-write branch. -/
theorem Store.shape {h after : Heap} {p : BPtr} {xs : List UInt8}
    (store : Store h p xs after) : Shape h after := by
  rcases store with ⟨_, same⟩ | ⟨ref, off, array, pointer, get, write, room, same⟩
  · rw [same]
    exact Shape.refl h
  · rw [same]
    exact byte_view_put_shape get write _

/-- An empty exact Store leaves the complete heap unchanged. The slice branch
also reduces to the original array, without any table extensionality shortcut. -/
theorem Store.empty_eq {h after : Heap} {p : BPtr} (store : Store h p [] after) : after = h := by
  rcases store with ⟨_, same⟩ | ⟨ref, off, array, pointer, get, write, room, same⟩
  · exact same
  · simp only [List.length_nil, Nat.add_zero] at room same
    simp only [Array.append_empty] at same
    rw [Array.extract_append_extract, Nat.zero_min, Nat.max_eq_right room,
      Array.extract_size, byte_view_put_self get write] at same
    exact same

end ZlibF.Spec.Public

namespace Zlib.Uncompr.Proof.FrameMirror
open C ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Mirror the same exact byte store into the expected heap. Actual Store
supplies the expected readable array, mutability and bounds through the old-live
frame clause. No expected Writable, Shape or decoder contract is assumed. -/
theorem store_mirror
    {expected actual written : Heap} {changed : Nat → Prop} {p : BPtr} {xs : List UInt8}
    (frame : Frame expected actual changed)
    (outside : ∀ b, ByteRoot p b → expected.live b ∧ ¬ changed b)
    (store : Store actual p xs written) :
    ∃ nextExpected, Store expected p xs nextExpected ∧ Frame nextExpected written changed := by
  rcases store with ⟨empty, same⟩ | ⟨ref, off, array, pointer, get, write, room, same⟩
  · refine ⟨expected, Or.inl ⟨empty, rfl⟩, ?_⟩
    rw [same]
    exact frame
  · subst p
    have views := frame.byte_view_eq outside
    have expectedGet : Space.get expected ref = some array := views.1.symm.trans get
    have expectedWrite : Space.ro expected ref = false := views.2.symm.trans write
    let replacement := array.extract 0 off ++ xs.toArray ++ array.extract (off + xs.length) array.size
    refine ⟨Space.put expected ref replacement,
      Or.inr ⟨ref, off, array, rfl, expectedGet, expectedWrite, room, rfl⟩, ?_⟩
    rw [same]
    exact frame_reset_byte_view frame expectedGet expectedWrite replacement

#print axioms store_mirror
#print axioms ZlibF.Spec.Public.Frame.byte_view_eq
#print axioms ZlibF.Spec.Public.Store.shape
#print axioms ZlibF.Spec.Public.Store.empty_eq
end Zlib.Uncompr.Proof.FrameMirror
