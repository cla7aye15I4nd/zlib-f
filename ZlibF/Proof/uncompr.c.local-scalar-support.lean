import ZlibF.Proof.«uncompr.c.single-length»
import ZlibF.Proof.«inflate.c.local-end»

namespace Zlib.Uncompr.Proof.LocalSingleLength
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength
set_option autoImplicit false

/-- Freshness establishes an empty local uniqueness domain at allocation.
It imposes no condition on any older caller allocation. -/
theorem fresh_uniqueFrom (h : Heap) (fresh : Fresh h) : UniqueFrom h h.nextBlk := by
  intro x lower
  have dead := Heap.not_live.mp (fresh x lower)
  simp [dead.1,dead.2.1,dead.2.2.1,dead.2.2.2.1,dead.2.2.2.2.1,
    dead.2.2.2.2.2.1,dead.2.2.2.2.2.2,cnt]

theorem scalar_uniqueFrom (h : Heap) (cutoff : Nat) (n : UInt64) (uniq : UniqueFrom h cutoff) (fresh : Fresh h) : UniqueFrom (scalarHeap h n) cutoff := by
  intro x lower
  by_cases same : x = h.nextBlk
  · subst x
    have dead := Heap.not_live.mp (fresh h.nextBlk (Nat.le_refl _))
    simp [scalarHeap, dead.2.1, dead.2.2.1, dead.2.2.2.1, dead.2.2.2.2.1,
      dead.2.2.2.2.2.1, dead.2.2.2.2.2.2, cnt]
  · simpa [scalarHeap, same] using uniq x lower

theorem free_scalar_local (h : Heap) (block : Nat) (value : UInt64)
    (cutoff : Nat) (uniq : UniqueFrom h cutoff) (age : cutoff ≤ block) (cell : LengthCell h (.ref (.blk block) 0) value) :
    freeB (.ref (.blk block) 0) h = .ok ((), freedHeap h block) ∧
    LiveChange h (freedHeap h block) (fun _ => False) (fun x => x = block) := by
  obtain ⟨a, get, ro⟩ : ∃ a, h.bytes block = some a ∧ h.ro block = false := by
    rcases cell.2 with null | ⟨ref, off, a, ptr, get, ro, _⟩
    · cases null.1
    · cases ptr
      exact ⟨a, get, ro⟩
  refine ⟨by simp [freeB, get, ro, freedHeap], ?_⟩
  have onlyByte := UniqueFrom.bytes_only uniq age get
  intro x
  by_cases same : x = block
  · subst x
    simp [freedHeap, Heap.live, onlyByte.1, onlyByte.2.1, onlyByte.2.2.1,
      onlyByte.2.2.2.1, onlyByte.2.2.2.2.1, onlyByte.2.2.2.2.2]
  · simp [freedHeap, Heap.live, same]

theorem freed_uniqueFrom (h : Heap) (cutoff block : Nat) (uniq : UniqueFrom h cutoff) : UniqueFrom (freedHeap h block) cutoff := by
  intro x lower
  have count := uniq x lower
  by_cases same : x = block
  · subst x
    simp only [freedHeap, upd_same, cnt_none]
    omega
  · simpa [freedHeap, same] using count


#print axioms fresh_uniqueFrom
#print axioms scalar_uniqueFrom
#print axioms free_scalar_local
#print axioms freed_uniqueFrom
end Zlib.Uncompr.Proof.LocalSingleLength
