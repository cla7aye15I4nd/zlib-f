import ZlibF.Proof.«uncompr.c.wrapper-shape»

/-!
# The actual single-length uncompress memory path

A fresh scalar is really allocated and written before the counted callee runs.
The same returning callee heap supplies the cell and uniqueness needed to free
that scalar. First and later allocation failures are included. Exact output
format, complete public framing and compatibility wrappers remain separate.
-/

namespace Zlib.Uncompr.Proof.CallerCells
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.InitialRefusal Zlib.Uncompr.Proof.WrapperShape

/-- A returning actual counted wrapper always leaves both scalar cells readable
and writable, including first init refusal. Their values never exceed their
incoming capacities. The actual heap remains fresh, unique and platform-sized. -/
theorem uncompress2_z_caller_cells (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after used made,
      C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after) ∧
      LengthCell after sourceLen used ∧ LengthCell after destLen made ∧
      used.toNat ≤ n.toNat ∧ made.toNat ≤ capacity.toNat ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  obtain ⟨rc, after, run, live, refused, counted⟩ := uncompress2_z_memory h source dest sourceLen destLen
    n capacity xs fresh uniq globals platform inputCell outputCell readable writable separate
    sourceSeparate destSeparate cellSeparate validInput validOutput
  have shape := uncompress2_z_return_shape h after source dest sourceLen destLen n capacity xs rc
    fresh uniq globals platform inputCell outputCell readable writable separate sourceSeparate destSeparate
    cellSeparate validInput validOutput run
  by_cases allocation : h.allocOk h.nalloc = true
  · obtain ⟨used, made, input, output, usedBound, madeBound, _codes⟩ := counted allocation
    refine ⟨rc, after, UInt64.ofNat used, UInt64.ofNat made, run, input, output, ?_, ?_, live, shape⟩
    · simp only [UInt64.toNat_ofNat']
      exact Nat.le_trans (Nat.mod_le _ _) usedBound
    · simp only [UInt64.toNat_ofNat']
      exact Nat.le_trans (Nat.mod_le _ _) madeBound
  · have no : h.allocOk h.nalloc = false := by cases bit : h.allocOk h.nalloc <;> simp_all
    obtain ⟨_code, input, output, _count, _frame⟩ := refused no
    exact ⟨rc, after, n, capacity, run, input, output, Nat.le_refl _, Nat.le_refl _, live, shape⟩

#print axioms uncompress2_z_caller_cells
end Zlib.Uncompr.Proof.CallerCells

namespace Zlib.Uncompr.Proof.SingleLength
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.CallerCells

def initialScalar (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)))
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk + 1 }

def scalarHeap (h : Heap) (n : UInt64) : Heap :=
  { h with
    bytes := upd h.bytes h.nextBlk (some (lengthBytes n).toArray)
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk + 1 }

def freedHeap (h : Heap) (block : Nat) : Heap := { h with bytes := upd h.bytes block none }

theorem scalar_allocate (h : Heap) (fresh : Fresh h) :
    allocLocal 8 h = .ok (.ref (.blk h.nextBlk) 0, initialScalar h) := by
  simp [allocLocal, allocBytes, fresh.slotUsed_next, initialScalar]

theorem scalar_write (h : Heap) (n : UInt64) :
    store64 (.ref (.blk h.nextBlk) 0) n (initialScalar h) = .ok ((), scalarHeap h n) := by
  let junk : Array UInt8 := Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)
  have get : Space.get (initialScalar h) (.blk h.nextBlk : BRef) = some junk := by simp [Space.get, initialScalar, junk]
  have write : Space.ro (initialScalar h) (.blk h.nextBlk : BRef) = false := by simp [Space.ro, initialScalar]
  have actual := store64_slice_run (initialScalar h) (.blk h.nextBlk) junk 0 n get write (by simp [junk])
  simpa [Space.put, initialScalar, scalarHeap, junk, upd_upd, Array.extract_empty_of_stop_le_start (Nat.le_refl 8)] using actual

theorem scalar_fresh (h : Heap) (n : UInt64) (fresh : Fresh h) : Fresh (scalarHeap h n) := by
  apply fresh.mono (by simp [scalarHeap])
  intro x bound
  have different : x ≠ h.nextBlk := by change h.nextBlk + 1 ≤ x at bound; omega
  simp [scalarHeap, different]

theorem scalar_uniq (h : Heap) (n : UInt64) (uniq : Uniq h) (fresh : Fresh h) : Uniq (scalarHeap h n) := by
  intro x
  by_cases same : x = h.nextBlk
  · subst x
    have dead := Heap.not_live.mp (fresh h.nextBlk (Nat.le_refl _))
    simp [scalarHeap, dead.2.1, dead.2.2.1, dead.2.2.2.1, dead.2.2.2.2.1,
      dead.2.2.2.2.2.1, dead.2.2.2.2.2.2, cnt]
  · simpa [scalarHeap, same] using uniq x

theorem scalar_platform (h : Heap) (n : UInt64) (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit (scalarHeap h n) := by
  have bound : (lengthBytes n).toArray.size < ZlibF.PlatformMemory.byteObjectLimit := by
    simp only [List.size_toArray, lengthBytes, List.length_map, List.length_range, ZlibF.PlatformMemory.byteObjectLimit]
    decide
  exact (fit.with_bytes (block := h.nextBlk) bound).of_storage_eq rfl rfl rfl

theorem scalar_cell (h : Heap) (n : UInt64) : LengthCell (scalarHeap h n) (.ref (.blk h.nextBlk) 0) n := by
  have get : Space.get (scalarHeap h n) (.blk h.nextBlk : BRef) = some (lengthBytes n).toArray := by
    simp [Space.get, scalarHeap]
  constructor
  · exact Or.inr ⟨.blk h.nextBlk, 0, (lengthBytes n).toArray, rfl, get,
      by simp [lengthBytes], by change lengthBytes n = (lengthBytes n).take 8; rw [List.take_of_length_le (by simp [lengthBytes])]⟩
  · exact Or.inr ⟨.blk h.nextBlk, 0, (lengthBytes n).toArray, rfl, get,
      by simp [Space.ro, scalarHeap], by simp [lengthBytes]⟩

theorem scalar_old_view (h : Heap) (n : UInt64) (fresh : Fresh h) (ref : BRef) (a : Array UInt8)
    (get : Space.get h ref = some a) :
    Space.get (scalarHeap h n) ref = some a ∧ Space.ro (scalarHeap h n) ref = Space.ro h ref := by
  cases ref with
  | blk b =>
    have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [show h.bytes b = some a from get]))
    constructor
    · simpa [Space.get, scalarHeap, show b ≠ h.nextBlk by omega] using get
    · simp [Space.ro, scalarHeap, show b ≠ h.nextBlk by omega]
  | dstate_depth b => exact ⟨get, rfl⟩
  | str i => exact ⟨get, rfl⟩
  | st_dist_code => exact ⟨get, rfl⟩
  | st_length_code => exact ⟨get, rfl⟩

theorem scalar_old_bytes (h : Heap) (n : UInt64) (fresh : Fresh h) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) : Bytes (scalarHeap h n) p count xs := by
  rcases bytes with null | ⟨ref, off, a, ptr, get, room, values⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, off, a, ptr, (scalar_old_view h n fresh ref a get).1, room, values⟩

theorem scalar_old_writable (h : Heap) (n : UInt64) (fresh : Fresh h) (p : BPtr) (count : Nat)
    (writable : Writable h p count) : Writable (scalarHeap h n) p count := by
  rcases writable with null | ⟨ref, off, a, ptr, get, ro, room⟩
  · exact Or.inl null
  · have view := scalar_old_view h n fresh ref a get
    exact Or.inr ⟨ref, off, a, ptr, view.1, view.2.trans ro, room⟩

theorem scalar_old_cell (h : Heap) (n : UInt64) (fresh : Fresh h) (p : BPtr) (v : UInt64)
    (cell : LengthCell h p v) : LengthCell (scalarHeap h n) p v :=
  ⟨scalar_old_bytes h n fresh p 8 (lengthBytes v) cell.1, scalar_old_writable h n fresh p 8 cell.2⟩

theorem scalar_separate_old (h : Heap) (fresh : Fresh h) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) : Separate (.ref (.blk h.nextBlk) 0) 8 p count := by
  rcases bytes with null | ⟨ref, off, a, ptr, get, _, _⟩
  · simp [Separate, null.1]
  · subst p
    have distinct : (.blk h.nextBlk : BRef) ≠ ref := by
      intro same
      subst ref
      have live : h.live h.nextBlk := Or.inl (by simp [show h.bytes h.nextBlk = some a from get])
      exact fresh h.nextBlk (Nat.le_refl _) live
    exact Or.inr (Or.inr (Or.inl distinct))

theorem old_not_scalar (h : Heap) (fresh : Fresh h) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) : ∀ off, p ≠ .ref (.blk h.nextBlk) off := by
  intro off ptr
  rw [ptr] at bytes
  rcases bytes with null | ⟨ref, start, a, same, get, _⟩
  · cases null.1
  · cases same
    have live : h.live h.nextBlk := Or.inl (by simp [show h.bytes h.nextBlk = some a from get])
    exact fresh h.nextBlk (Nat.le_refl _) live

theorem freed_cell (h : Heap) (block : Nat) (p : BPtr) (value : UInt64)
    (cell : LengthCell h p value) (outside : ∀ off, p ≠ .ref (.blk block) off) :
    LengthCell (freedHeap h block) p value := by
  have view {ref : BRef} {off : Nat} {a : Array UInt8}
      (ptr : p = .ref ref off) (get : Space.get h ref = some a) :
      Space.get (freedHeap h block) ref = some a := by
    cases ref with
    | blk b =>
      have different : b ≠ block := by intro same; subst b; exact outside off ptr
      simpa [Space.get, freedHeap, different] using get
    | dstate_depth b => exact get
    | str i => exact get
    | st_dist_code => exact get
    | st_length_code => exact get
  constructor
  · rcases cell.1 with null | ⟨ref, off, a, ptr, get, room, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, view ptr get, room, values⟩
  · rcases cell.2 with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, view ptr get, ro, room⟩

theorem free_scalar (h : Heap) (block : Nat) (value : UInt64)
    (uniq : Uniq h) (cell : LengthCell h (.ref (.blk block) 0) value) :
    freeB (.ref (.blk block) 0) h = .ok ((), freedHeap h block) ∧
    LiveChange h (freedHeap h block) (fun _ => False) (fun x => x = block) := by
  obtain ⟨a, get, ro⟩ : ∃ a, h.bytes block = some a ∧ h.ro block = false := by
    rcases cell.2 with null | ⟨ref, off, a, ptr, get, ro, _⟩
    · cases null.1
    · cases ptr
      exact ⟨a, get, ro⟩
  refine ⟨by simp [freeB, get, ro, freedHeap], ?_⟩
  have onlyByte := Uniq.bytes_only uniq get
  intro x
  by_cases same : x = block
  · subst x
    simp [freedHeap, Heap.live, onlyByte.1, onlyByte.2.1, onlyByte.2.2.1,
      onlyByte.2.2.2.1, onlyByte.2.2.2.2.1, onlyByte.2.2.2.2.2]
  · simp [freedHeap, Heap.live, same]

theorem freed_uniq (h : Heap) (block : Nat) (uniq : Uniq h) : Uniq (freedHeap h block) := by
  intro x
  have count := uniq x
  by_cases same : x = block
  · subst x
    simp only [freedHeap, upd_same, cnt_none]
    omega
  · simpa [freedHeap, same] using count

theorem freed_subset (h : Heap) (block x : Nat) : (freedHeap h block).live x → h.live x := by
  intro live
  rcases live with byte | word | stream | header | dstate | istate | gzstate
  · left
    by_cases same : x = block
    · simp [freedHeap, same] at byte
    · simpa [freedHeap, same] using byte
  · exact Or.inr (Or.inl word)
  · exact Or.inr (Or.inr (Or.inl stream))
  · exact Or.inr (Or.inr (Or.inr (Or.inl header)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl dstate))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl istate)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr gzstate)))))

theorem freed_fresh (h : Heap) (block : Nat) (fresh : Fresh h) : Fresh (freedHeap h block) := by
  intro x bound live
  exact fresh x bound (freed_subset h block x live)

theorem scalar_live (h : Heap) (n : UInt64) (x : Nat) :
    (scalarHeap h n).live x ↔ h.live x ∨ x = h.nextBlk := by
  by_cases same : x = h.nextBlk
  · subst x
    simp [scalarHeap, Heap.live]
  · simp [scalarHeap, Heap.live, same]

/-- The actual single-length entry allocates and writes its temporary input
cell, runs the proved counted wrapper on that same heap, and frees the same
returned temporary cell. No caller supplies a callee contract. -/
theorem uncompress_z_memory (h : Heap) (source dest destLen : BPtr) (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (cellSeparate : Separate destLen 8 dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after got,
      C.run (uncompress_z dest destLen source n) h = .ok (rc, after) ∧
      LengthCell after destLen got ∧ got.toNat ≤ capacity.toNat ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  obtain ⟨destBytes, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have tempDest := scalar_separate_old h fresh dest capacity.toNat destBytes destRead
  have tempCell := scalar_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨rc, after, consumed, got, run, tempAfter, outputAfter, _inputBound, gotBound, live, unique, freshAfter, fitAfter⟩ :=
    uncompress2_z_caller_cells (scalarHeap h n) source dest (.ref (.blk h.nextBlk) 0) destLen n capacity xs
      (scalar_fresh h n fresh) (scalar_uniq h n uniq fresh) globals (scalar_platform h n platform)
      (scalar_cell h n) (scalar_old_cell h n fresh destLen capacity outputCell)
      (scalar_old_bytes h n fresh source n.toNat xs readable)
      (scalar_old_writable h n fresh dest capacity.toNat writable)
      separate tempDest cellSeparate tempCell validInput validOutput
  obtain ⟨freeRun, freeLedger⟩ := free_scalar after h.nextBlk consumed unique tempAfter
  have finalCell := freed_cell after h.nextBlk destLen got outputAfter
    (old_not_scalar h fresh destLen 8 (lengthBytes capacity) outputCell.1)
  refine ⟨rc, freedHeap after h.nextBlk, got, ?_, finalCell, gotBound, ?_,
    freed_uniq after h.nextBlk unique, freed_fresh after h.nextBlk freshAfter,
    Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform after h.nextBlk fitAfter⟩
  · simp only [C.run] at run
    simp [C.run, uncompress_z, scalar_allocate h fresh, scalar_write h n, run, freeRun]
  · intro x
    have inner : after.live x ↔ (scalarHeap h n).live x := by
      simpa only [not_false_eq_true, and_true, or_false] using live x
    have outer := freeLedger x
    have beginning := scalar_live h n x
    constructor
    · intro current
      obtain ⟨old, outside⟩ := (outer.mp current).resolve_right (by simp)
      rcases beginning.mp (inner.mp old) with original | temporary
      · exact Or.inl ⟨original, by simp⟩
      · exact False.elim (outside temporary)
    · rintro (⟨original, _⟩ | impossible)
      · have different : x ≠ h.nextBlk := by have below := fresh.lt original; omega
        exact outer.mpr (Or.inl ⟨inner.mpr (beginning.mpr (Or.inl original)), different⟩)
      · exact False.elim impossible

#print axioms uncompress_z_memory

#print axioms scalar_write
end Zlib.Uncompr.Proof.SingleLength
