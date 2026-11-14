import ZlibF.Proof.«inflate.c.sync-default-origin»
import ZlibF.Proof.«inflate.c.construction-record-read-tail»
import ZlibF.Proof.«inflate.c.output-frame-local-cleanup»
import ZlibF.Proof.«inflate.c.live-frame-local»
import ZlibF.Spec.Public.Sequences
import ZlibF.Spec.Functional.Api.Goals
import ZlibF.Spec.Functional.Api.InflateAccepted

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Readable public Sync input supplies a total real search for every
search-counter value. No semantic search-history hypothesis is needed. -/
theorem syncsearch_public_readable {h : Heap} {p : BPtr} {len : UInt32}
    (range : p = .null ∨ ∃ xs, Bytes h p len.toNat xs) (nonnull : p = .null → len = 0) (start : UInt32) :
    ∃ used found, syncsearch start p len h = .ok ((used, found), h) ∧ used.toNat ≤ len.toNat := by
  rcases range with null | ⟨xs, bytes⟩
  · subst p
    have zero := nonnull rfl
    subst len
    exact ⟨0, start, syncsearch_null start h, Nat.le_refl _⟩
  · rcases bytes with ⟨null, zero, _⟩ | ⟨ref, off, array, ptr, get, room, _⟩
    · subst p
      have zero := nonnull rfl
      subst len
      exact ⟨0, start, syncsearch_null start h, Nat.le_refl _⟩
    · subst p
      refine ⟨UInt32.ofNat (syncScan start (syncBytes array off len)).2,
        (syncScan start (syncBytes array off len)).1, syncsearch_run start get room, ?_⟩
      have bound := syncScan_le start (syncBytes array off len)
      have length := syncBytes_length room
      have size := len.toNat_lt
      rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
      omega

/-- The pointer advance after a real bounded search is defined on the
same caller byte object. Zero-length null input takes the zero advance. -/
theorem sync_public_input_add {h : Heap} {p : BPtr} {len used : UInt32}
    (range : p = .null ∨ ∃ xs, Bytes h p len.toNat xs) (nonnull : p = .null → len = 0)
    (bound : used.toNat ≤ len.toNat) (zs : Nat) (state : InflateState) :
    ∃ next, Ptr.add p (used.toNat : Int) (setI h zs state) = .ok (next, setI h zs state) := by
  rcases range with null | ⟨xs, bytes⟩
  · subst p
    have zero := nonnull rfl
    have usedZero : used.toNat = 0 := by rw [zero] at bound; simpa using bound
    rw [usedZero]
    exact ⟨.null, rfl⟩
  · rcases bytes with ⟨null, zero, _⟩ | ⟨ref, off, array, ptr, get, room, _⟩
    · subst p
      have zero := nonnull rfl
      have usedZero : used.toNat = 0 := by rw [zero] at bound; simpa using bound
      rw [usedZero]
      exact ⟨.null, rfl⟩
    · subst p
      exact ⟨.ref ref (off + used.toNat), Ptr.add_nat_ok (by simpa only [byte_view_get_setI] using get) (by omega)⟩

/-- Restoring held bytes writes only the fresh local block. Every original
readable input object, including static and embedded byte views, survives. -/
theorem sync_readable_first {h : Heap} {p : BPtr} {len : UInt32} {zs : Nat} {s : InflateState}
    (fresh : Fresh h) (range : p = .null ∨ ∃ xs, Bytes h p len.toNat xs) :
    p = .null ∨ ∃ xs, Bytes (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h)) p len.toNat xs := by
  rcases range with null | ⟨xs, bytes⟩
  · exact Or.inl null
  · right
    refine ⟨xs, ?_⟩
    rcases bytes with null | ⟨ref, off, array, ptr, get, room, values⟩
    · exact Or.inl null
    · refine Or.inr ⟨ref, off, array, ptr, ?_, room, values⟩
      have separate := original_byte_view_not_local fresh get
      have allocated := (byte_view_syncAlloc fresh get).1
      cases ref with
      | blk block =>
        have different : block ≠ h.nextBlk := fun equal => separate (by rw [equal])
        simpa only [syncFirstHeap, Space.get, upd_ne _ _ _ _ different] using allocated
      | str _ | st_dist_code | st_length_code | dstate_depth _ =>
        simpa only [syncFirstHeap, Space.get, C.staticStringBytes] using allocated

/-- The actual local allocation/free retains the entire live-object shape.
Its fresh, now-dead byte slot cannot remove an earlier caller allocation. -/
theorem sync_tmp_freed_shape {h : Heap} (fresh : Fresh h) : Shape h (tmpFreed h) := by
  intro b
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases same : b = h.nextBlk
  · subst b
    have absent := (fresh_dead fresh (Nat.le_refl h.nextBlk)).1
    simp only [tmpFreed, freeWin, syncBuf, upd_same, absent]
  · simp only [tmpFreed, freeWin, syncBuf, syncAlloc, upd_ne _ _ _ _ same]

#print axioms syncsearch_public_readable
#print axioms sync_public_input_add
#print axioms sync_readable_first
#print axioms sync_tmp_freed_shape
end Zlib.Inflate.Proofs
