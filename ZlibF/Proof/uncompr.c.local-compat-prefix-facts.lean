import ZlibF.Proof.«uncompr.c.local-compat-prefix»

namespace Zlib.Uncompr.Proof.LocalCompatPrefix
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.Cells
set_option autoImplicit false

theorem prepared_fresh (h : Heap) (capacity n : UInt64) (fresh : Fresh h) :
    Fresh (preparedHeap h capacity n) :=
  scalar_fresh (scalarHeap h capacity) n (scalar_fresh h capacity fresh)

theorem prepared_uniqueFrom (h : Heap) (capacity n : UInt64) (fresh : Fresh h) :
    UniqueFrom (preparedHeap h capacity n) h.nextBlk :=
  LocalSingleLength.scalar_uniqueFrom (scalarHeap h capacity) h.nextBlk n
    (LocalSingleLength.scalar_uniqueFrom h h.nextBlk capacity (LocalSingleLength.fresh_uniqueFrom h fresh) fresh)
    (scalar_fresh h capacity fresh)

theorem prepared_platform (h : Heap) (capacity n : UInt64)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit (preparedHeap h capacity n) :=
  scalar_platform (scalarHeap h capacity) n (scalar_platform h capacity fit)

theorem prepared_globals (h : Heap) (capacity n : UInt64) (globals : LibraryGlobals h) :
    LibraryGlobals (preparedHeap h capacity n) := globals

theorem prepared_got_cell (h : Heap) (capacity n : UInt64) (fresh : Fresh h) :
    LengthCell (preparedHeap h capacity n) (.ref (.blk h.nextBlk) 0) capacity :=
  scalar_old_cell (scalarHeap h capacity) n (scalar_fresh h capacity fresh)
    (.ref (.blk h.nextBlk) 0) capacity (scalar_cell h capacity)

theorem prepared_used_cell (h : Heap) (capacity n : UInt64) :
    LengthCell (preparedHeap h capacity n) (.ref (.blk (h.nextBlk + 1)) 0) n :=
  scalar_cell (scalarHeap h capacity) n

theorem prepared_old_bytes (h : Heap) (capacity n : UInt64) (fresh : Fresh h)
    (p : BPtr) (count : Nat) (xs : List UInt8) (bytes : Bytes h p count xs) :
    Bytes (preparedHeap h capacity n) p count xs :=
  scalar_old_bytes (scalarHeap h capacity) n (scalar_fresh h capacity fresh) p count xs
    (scalar_old_bytes h capacity fresh p count xs bytes)

theorem prepared_old_writable (h : Heap) (capacity n : UInt64) (fresh : Fresh h)
    (p : BPtr) (count : Nat) (writable : Writable h p count) :
    Writable (preparedHeap h capacity n) p count :=
  scalar_old_writable (scalarHeap h capacity) n (scalar_fresh h capacity fresh) p count
    (scalar_old_writable h capacity fresh p count writable)

theorem prepared_old_cell (h : Heap) (capacity n : UInt64) (fresh : Fresh h)
    (p : BPtr) (value : UInt64) (cell : LengthCell h p value) :
    LengthCell (preparedHeap h capacity n) p value :=
  ⟨prepared_old_bytes h capacity n fresh p 8 (lengthBytes value) cell.1,
    prepared_old_writable h capacity n fresh p 8 cell.2⟩

theorem prepared_live (h : Heap) (capacity n : UInt64) (x : Nat) :
    (preparedHeap h capacity n).live x ↔ h.live x ∨ x = h.nextBlk ∨ x = h.nextBlk + 1 := by
  change (scalarHeap (scalarHeap h capacity) n).live x ↔ _
  rw [scalar_live, scalar_live]
  exact or_assoc

#print axioms prepared_fresh
#print axioms prepared_uniqueFrom
#print axioms prepared_platform
#print axioms prepared_globals
#print axioms prepared_got_cell
#print axioms prepared_used_cell
#print axioms prepared_old_bytes
#print axioms prepared_old_writable
#print axioms prepared_old_cell
#print axioms prepared_live
end Zlib.Uncompr.Proof.LocalCompatPrefix
