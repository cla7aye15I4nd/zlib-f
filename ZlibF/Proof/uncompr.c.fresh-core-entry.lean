import ZlibF.Proof.«uncompr.c.wrapper-init»

namespace Zlib.Uncompr.Proof.FreshCoreEntry
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Loop
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Actual default initialization itself does not require global caller
object uniqueness. The stronger decoder relation is a separate obligation. -/
theorem initialized_run (h : Heap) (source : BPtr) (fresh : Fresh h)
    (allocation : h.allocOk h.nalloc = true) :
    C.run (inflateInit_ (some (.tab h.nextBlk)) (.ref (.str 57) 0) 112) (preparedHeap h source) =
      .ok (Z_OK, initHeap h source) := by
  have get : ZStreamRef.get (preparedHeap h source) (.tab h.nextBlk) = some (Wrapper.preparedStream h source) := by
    simp [preparedHeap, ZStreamRef.get]
  have byte : OkOn (preparedHeap h source) (index8 (.ref (.str 57) 0) 0) 49 := by
    have bytes : Space.get (preparedHeap h source) (.str 57 : BRef) = some (strBytes ZLIB_VERSION) := by
      rw [BRef.get_str]
      rfl
    exact Ptr.index_ok bytes (by decide)
  exact inflateInit2_success get (prepared_fresh h fresh source) allocation
    (Or.inl rfl) (Or.inl rfl) (by simp) byte params15

/-- The entire real wrapper reaches exactly the original counted-loop
continuation after actual guards, local allocations, length reads, default
init and NULL+zero output substitution. Only Fresh is needed here; this
source equation does not assert that the remaining decoder is safe. -/
theorem uncompress2_z_to_core (h : Heap) (source dest sourceLen destLen : BPtr) (n capacity : UInt64)
    (fresh : Fresh h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    C.run (uncompress2_z dest destLen source sourceLen) h =
      (do
        let last ← cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
          { err := Z_OK, len := n, left := capacity }
        finish (some (.tab h.nextBlk)) (.ref (.blk (h.nextBlk + 1)) 0) destLen sourceLen last)
        (coreHeap h source dest capacity) := by
  have srcNotNull := cell_nonnull h sourceLen n inputCell
  have dstNotNull := cell_nonnull h destLen capacity outputCell
  have input := load64_lengthCell (localHeap h) sourceLen n (local_cell h fresh sourceLen n inputCell)
  have output := load64_lengthCell (localHeap h) destLen capacity (local_cell h fresh destLen capacity outputCell)
  simp only [C.run] at input output
  have initialized := initialized_run h source fresh allocation
  simp only [C.run] at initialized
  have outputSet := output_run (initHeap h source) h.nextBlk (initializedStream h source)
    (normalizedDest h dest capacity) (initHeap_stream h source)
  have sourceValid : ¬ (0 < n ∧ source = .null) := by
    rintro ⟨positive, null⟩
    simp [validInput null] at positive
  have destValid : ¬ (0 < capacity ∧ dest = .null) := by
    rintro ⟨positive, null⟩
    simp [validOutput null] at positive
  simp only [normalizedDest, Bool.and_eq_true, beq_iff_eq] at outputSet
  rw [uncompress2_z_wrapper_source]
  simp [C.run, Wrapper.decomposed, entered, allocLocalZ_run h fresh, allocReserved_run h fresh,
    srcNotNull, dstNotNull, input, output, sourceValid, destValid, prepare_run,
    version_run, initialized, normalizedDest, outputSet, coreHeap]

#print axioms initialized_run
#print axioms uncompress2_z_to_core
end Zlib.Uncompr.Proof.FreshCoreEntry
