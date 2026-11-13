import ZlibF.Proof.«public-uncompress-end»

/-!
# uncompr.c: `uncompress2_z`

Lemmas of both runs of `uncompress2_z` (the safety run in `public-uncompress-safe`,
the functional run in `public-uncompress-facts`): argument refusal, initialization
failure, and the heap after the cleanup.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Inflate.Spec Zlib.Uncompr
open Zlib.Inflate (inflate inflateEnd inflateInit_)
set_option autoImplicit false

theorem separate_symm {p q : BPtr} {n m : Nat} (s : Separate p n q m) : Separate q m p n := by
  rcases s with h | h | s
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · right; right
    cases p <;> cases q <;> simp_all
    rename_i r i r' j
    rcases s with ne | lt | lt
    · exact Or.inl (Ne.symm ne)
    · exact Or.inr (Or.inr lt)
    · exact Or.inr (Or.inl lt)

theorem bytes_length {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8} (b : Bytes h p n xs) : xs.length = n := by
  rcases b with ⟨-, rfl, rfl⟩ | ⟨r, i, a, -, -, fit, rfl⟩
  · rfl
  · simp; omega

theorem bytes_bound {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8} (b : Bytes h p n xs)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) : n < 2 ^ 63 := by
  rcases b with ⟨-, rfl, -⟩ | ⟨r, i, a, -, g, hi, -⟩
  · decide
  · have := fit r a g
    simp only [ZlibF.PlatformMemory.byteObjectLimit] at this
    omega

theorem writable_bound {h : Heap} {p : BPtr} {n : Nat} (w : Writable h p n)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) : n < 2 ^ 63 := by
  rcases w with ⟨-, rfl⟩ | ⟨r, i, a, -, g, -, hi⟩
  · decide
  · have := fit r a g
    simp only [ZlibF.PlatformMemory.byteObjectLimit] at this
    omega

/-- Writing back the value a cell holds leaves the heap. -/
theorem cell_self_write {h : Heap} {p : BPtr} {v : UInt64} (cell : LengthCell h p v) :
    writeOut h p (lengthBytes v) = h := by
  obtain ⟨bytes, -⟩ := cell
  rcases bytes with ⟨-, h8, -⟩ | ⟨r, i, a, rfl, g, fit, hx⟩
  · cases h8
  have hx' : lengthBytes v = (a.toList.drop i).take 8 := hx
  have ne : lengthBytes v ≠ [] := by intro e; have := congrArg List.length e; simp [lengthBytes_length] at this
  have arr : a.extract 0 i ++ (lengthBytes v).toArray ++ a.extract (i + (lengthBytes v).length) a.size = a := by
    apply Array.ext_getElem?
    intro j
    rw [written_get? a i (lengthBytes v) (by rw [lengthBytes_length]; exact fit)]
    rw [lengthBytes_length]
    by_cases lo : j < i
    · simp [lo]
    by_cases hi : j < i + 8
    · simp only [lo, hi, ite_true, ite_false]
      rw [hx']
      simp only [List.getElem?_take, List.getElem?_drop, show j - i < 8 by omega, ite_true,
        show i + (j - i) = j by omega, Array.getElem?_toList]
    · simp [lo, hi]
  simp only [writeOut, g, ne, ite_false]
  rw [arr]
  exact put_self_any g

/-- The heap after a failed `inflateInit`. -/
def memHeap (h : Heap) (source : BPtr) : Heap :=
  initMemHeap (preHeap h source) (.tab h.nextBlk) (preStream h source)

theorem memHeap_reserved (h : Heap) (source : BPtr) :
    (memHeap h source).bytes (h.nextBlk + 1) = some (reservedBytes h) ∧
      (memHeap h source).ro (h.nextBlk + 1) = false := by
  simp [memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap]

theorem memHeap_stream (h : Heap) (source : BPtr) :
    (reservedFreed (memHeap h source) h.nextBlk).streams h.nextBlk = some (initStream (preStream h source)) := by
  simp [reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap]

/-- After a failed initialization and the frees, the caller heap is unchanged entry by entry. -/
theorem mem_same {h : Heap} (fresh : Fresh h) (source : BPtr) :
    SameObjectsUpToTableShape h (freedHeap (memHeap h source) h.nextBlk) := by
  have n0 := fresh h.nextBlk (Nat.le_refl _)
  have n1 := fresh (h.nextBlk + 1) (by omega)
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at n0 n1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    simp only [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap,
      streamHeap, upd_apply]
    split <;> simp_all
  · intro b
    simp only [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap,
      streamHeap, upd_apply]
    split <;> simp_all
  · intro b live
    have ne : b ≠ h.nextBlk + 1 := fun e => fresh b (by omega) live
    simp [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap,
      upd_ne _ _ _ _ ne]
  · intro b
    simp only [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap,
      streamHeap, upd_apply]
    split
    · simp_all
    · split <;> simp_all
  all_goals first
    | (intro b; simp [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap])
    | (simp [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap])
    | (simp [freedHeap, reservedFreed, memHeap, initMemHeap, ZStreamRef.put, preHeap, localHeap, streamHeap]; omega)

theorem finalCode_mem {e : Int32} {R : UInt64} (h : finalCode e R = Z_MEM_ERROR) : e = Z_MEM_ERROR := by
  unfold finalCode at h
  split at h
  · exact absurd h (by decide)
  · split at h
    · exact absurd h (by decide)
    · split at h
      · exact absurd h (by decide)
      · exact h

theorem pos_iff (x : UInt64) : (decide (x > 0) = true) ↔ x ≠ 0 := by
  simp only [decide_eq_true_eq, ne_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
  constructor
  · intro hx e; rw [e] at hx; simp at hx
  · intro hx; have : x.toNat ≠ 0 := fun e => hx (UInt64.toNat_inj.mp (by simpa using e)); omega

end ZlibF.Spec.Public.Proofs.Uncompress
