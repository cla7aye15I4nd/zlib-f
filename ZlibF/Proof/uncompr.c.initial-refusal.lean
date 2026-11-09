import ZlibF.Proof.«uncompr.c.wrapper-safe»

/-!
# First allocation refusal and unconditional wrapper memory safety

The actual first allocation refusal returns MEM_ERROR without writing either
caller length cell. Both automatic objects are released, all caller objects are
framed and the allocation count advances once. Combining this branch with the
actual initialized path removes the first-allocation-success premise. The
internal Uniq/platform domain and open public format goal remain explicit.
-/

set_option maxRecDepth 8192

namespace Zlib.Uncompr.Proof.InitialRefusal
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Finish

/-- Exact heap of the first allocation refusal after both automatic frees. -/
def refusedHeap (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes (h.nextBlk + 1) none
    streams := upd h.streams h.nextBlk none
    ro := upd h.ro (h.nextBlk + 1) false
    nextBlk := h.nextBlk + 2
    nalloc := h.nalloc + 1 }

theorem init_refused (h : Heap) (source : BPtr) (fresh : Fresh h)
    (allocation : ¬ h.allocOk h.nalloc = true) :
    C.run (Zlib.Inflate.inflateInit_ (some (.tab h.nextBlk)) (.ref (.str 57) 0) 112) (preparedHeap h source) =
      .ok (Z_MEM_ERROR, initMemHeap (preparedHeap h source) (.tab h.nextBlk) (Wrapper.preparedStream h source)) := by
  have get : ZStreamRef.get (preparedHeap h source) (.tab h.nextBlk) = some (Wrapper.preparedStream h source) := by
    simp [preparedHeap, ZStreamRef.get]
  have byte : OkOn (preparedHeap h source) (index8 (.ref (.str 57) 0) 0) 49 := by
    have hg : Space.get (preparedHeap h source) (.str 57 : BRef) = some (strBytes ZLIB_VERSION) := by
      rw [BRef.get_str]
      rfl
    exact Ptr.index_ok hg (by decide)
  exact inflateInit2_memfail get (prepared_fresh h fresh source) allocation
    (Or.inl rfl) (Or.inl rfl) (by simp) byte

/-- A first allocation refusal returns MEM_ERROR, frees both automatic objects
and has never reached either caller length writeback. -/
theorem uncompress2_z_initial_refusal (h : Heap) (source dest sourceLen destLen : BPtr) (n capacity : UInt64)
    (fresh : Fresh h) (allocation : ¬ h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    C.run (uncompress2_z dest destLen source sourceLen) h = .ok (Z_MEM_ERROR, refusedHeap h) := by
  have srcNotNull := cell_nonnull h sourceLen n inputCell
  have dstNotNull := cell_nonnull h destLen capacity outputCell
  have input := load64_lengthCell (localHeap h) sourceLen n (local_cell h fresh sourceLen n inputCell)
  have output := load64_lengthCell (localHeap h) destLen capacity (local_cell h fresh destLen capacity outputCell)
  simp only [C.run] at input output
  have initialized := init_refused h source fresh allocation
  simp only [C.run] at initialized
  have sourceValid : ¬ (0 < n ∧ source = .null) := by
    rintro ⟨positive, null⟩
    simp [validInput null] at positive
  have destValid : ¬ (0 < capacity ∧ dest = .null) := by
    rintro ⟨positive, null⟩
    simp [validOutput null] at positive
  have notOk : Z_MEM_ERROR ≠ Z_OK := by decide
  simp [C.run, uncompress2_z, allocLocalZ_run h fresh, allocReserved_run h fresh,
    srcNotNull, dstNotNull, input, output, sourceValid, destValid, prepare_run,
    version_run, initialized, notOk]
  simp [initMemHeap, preparedHeap, localHeap, ZStreamRef.put, freeB, freeZStream, upd_upd, refusedHeap]

theorem refused_frame (h : Heap) (fresh : Fresh h) : Frame h (refusedHeap h) (fun _ => False) := by
  refine ⟨rfl, rfl, rfl, by simp [refusedHeap], by simp [refusedHeap], ?_⟩
  intro b live _
  have below := fresh.lt live
  simp [refusedHeap, show b ≠ h.nextBlk by omega, show b ≠ h.nextBlk + 1 by omega]

theorem refused_live (h : Heap) (fresh : Fresh h) :
    LiveChange h (refusedHeap h) (fun _ => False) (fun _ => False) := by
  intro x
  by_cases atStream : x = h.nextBlk
  · subst x
    have dead := fresh h.nextBlk (Nat.le_refl _)
    simp only [Heap.live] at dead
    simp_all [refusedHeap, Heap.live]
  · by_cases atReserved : x = h.nextBlk + 1
    · subst x
      have dead := fresh (h.nextBlk + 1) (by omega)
      simp_all [refusedHeap, Heap.live]
    · simp [refusedHeap, Heap.live, atStream, atReserved]

theorem refused_cell (h : Heap) (fresh : Fresh h) (p : BPtr) (v : UInt64)
    (cell : LengthCell h p v) : LengthCell (refusedHeap h) p v := by
  have view {ref : BRef} {a : Array UInt8} (get : Space.get h ref = some a) :
      Space.get (refusedHeap h) ref = some a ∧ Space.ro (refusedHeap h) ref = Space.ro h ref := by
    cases ref with
    | blk b =>
      have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [show h.bytes b = some a from get]))
      constructor
      · simpa [Space.get, refusedHeap, show b ≠ h.nextBlk + 1 by omega] using get
      · simp [Space.ro, refusedHeap, show b ≠ h.nextBlk + 1 by omega]
    | dstate_depth b => exact ⟨get, rfl⟩
    | str i => exact ⟨get, rfl⟩
    | st_dist_code => exact ⟨get, rfl⟩
    | st_length_code => exact ⟨get, rfl⟩
  constructor
  · rcases cell.1 with null | ⟨ref, off, a, ptr, get, room, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, (view get).1, room, values⟩
  · rcases cell.2 with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, (view get).1, (view get).2.trans ro, room⟩

/-- The actual valid-entry wrapper has no first-allocation-success assumption.
First refusal retains both input scalar values; after successful init, ordinary
return writes exact consumed and produced counts. Both alternatives leave no
allocation residue. The explicit internal Uniq/platform domain remains visible. -/
theorem uncompress2_z_memory (h : Heap) (source dest sourceLen destLen : BPtr)
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
    ∃ rc after,
      C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      (h.allocOk h.nalloc = false → rc = Z_MEM_ERROR ∧ LengthCell after sourceLen n ∧
        LengthCell after destLen capacity ∧ after.nalloc = h.nalloc + 1 ∧ Frame h after (fun _ => False)) ∧
      (h.allocOk h.nalloc = true → ∃ used made,
        LengthCell after sourceLen (UInt64.ofNat used) ∧ LengthCell after destLen (UInt64.ofNat made) ∧
        used ≤ n.toNat ∧ made ≤ capacity.toNat ∧
        ∃ err remainIn, err ≠ Z_OK ∧ PublicInflateCode err ∧ rc = resultCode err remainIn ∧
          used + remainIn.toNat = n.toNat) := by
  by_cases allocation : h.allocOk h.nalloc = true
  · obtain ⟨rc, after, used, made, run, input, output, usedBound, madeBound, live, error⟩ :=
      Zlib.Uncompr.Proof.WrapperSafe.uncompress2_z_safe h source dest sourceLen destLen n capacity xs
        fresh uniq globals platform allocation inputCell outputCell readable writable separate
        sourceSeparate destSeparate cellSeparate validInput validOutput
    refine ⟨rc, after, run, live, ?_, fun _ => ⟨used, made, input, output, usedBound, madeBound, error⟩⟩
    intro impossible
    rw [allocation] at impossible
    cases impossible
  · refine ⟨Z_MEM_ERROR, refusedHeap h,
      uncompress2_z_initial_refusal h source dest sourceLen destLen n capacity fresh allocation
        inputCell outputCell validInput validOutput,
      refused_live h fresh, ?_, ?_⟩
    · intro _
      exact ⟨rfl, refused_cell h fresh sourceLen n inputCell,
        refused_cell h fresh destLen capacity outputCell, rfl, refused_frame h fresh⟩
    · intro impossible
      exact False.elim (allocation impossible)

#print axioms uncompress2_z_memory
#print axioms init_refused
#print axioms uncompress2_z_initial_refusal
#print axioms refused_frame
#print axioms refused_live
#print axioms refused_cell
end Zlib.Uncompr.Proof.InitialRefusal
