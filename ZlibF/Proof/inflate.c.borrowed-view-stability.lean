import ZlibF.Proof.«borrowed-byte-frame»

/-!
# Readable views and exact borrow identity

An external view's encoded index selects one epoch and errno. Readability
of that same index in both heaps therefore implies the borrow is unchanged.
This is derived from actual view observations, not from allocation Frame.
-/
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate.Spec ZlibF.Spec.Public C.LibcBorrow
set_option autoImplicit false

/-- Readability in both heaps preserves the borrow for that byte view.
The arrays need not be equal. Persistent source strings need no borrow fact. -/
theorem readable_view_stable {before after : Heap} {ref : BRef} {a b : Array UInt8}
    (old : Space.get before ref = some a) (current : Space.get after ref = some b) :
    BorrowStable before after ref := by
  cases ref with
  | str i =>
    by_cases source : i < strTable.size
    · exact Or.inl source
    · cases hb : before.libcErrorBorrow with
      | none => simp [BRef.get_str, staticStringBytes, source, hb] at old
      | some pair =>
        obtain ⟨epoch, errno⟩ := pair
        have oldIndex : i = libcErrnoIndex epoch errno := by
          by_cases same : i = libcErrnoIndex epoch errno
          · exact same
          · simp [BRef.get_str, staticStringBytes, source, hb, same] at old
        cases ha : after.libcErrorBorrow with
        | none => simp [BRef.get_str, staticStringBytes, source, ha] at current
        | some pair =>
          obtain ⟨nextEpoch, nextErrno⟩ := pair
          have nextIndex : i = libcErrnoIndex nextEpoch nextErrno := by
            by_cases same : i = libcErrnoIndex nextEpoch nextErrno
            · exact same
            · simp [BRef.get_str, staticStringBytes, source, ha, same] at current
          obtain ⟨sameEpoch, sameErrno⟩ := errno_index_injective (oldIndex.symm.trans nextIndex)
          exact Or.inr (by rw [ha, hb, sameEpoch, sameErrno])
  | _ => trivial

#print axioms readable_view_stable
end Zlib.Inflate.Proofs
