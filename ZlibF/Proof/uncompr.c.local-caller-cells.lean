import ZlibF.Proof.«uncompr.c.local-wrapper-shape-return»

/-! Actual counted-wrapper observations for callers with their own earlier
scalar allocations. The original caller heap needs Fresh, not global Uniq. -/
namespace Zlib.Uncompr.Proof.LocalCallerCells
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells
set_option autoImplicit false

/-- Both scalar observations, exact live accounting and typed shape refer to
the same complete actual call. Any earlier local uniqueness cutoff survives. -/
theorem uncompress2_z_caller_cells (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
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
      Shape h after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      (∀ cutoff, UniqueFrom h cutoff → UniqueFrom after cutoff) := by
  obtain ⟨rc, after, run, live, refused, counted⟩ :=
    LocalWrapperSafe.uncompress2_z_memory h source dest sourceLen destLen n capacity xs
      fresh globals platform inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput
  have shape := LocalWrapperShape.uncompress2_z_return_shape h after source dest sourceLen destLen
    n capacity xs rc fresh globals platform inputCell outputCell readable writable separate
    sourceSeparate destSeparate cellSeparate validInput validOutput run
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
end Zlib.Uncompr.Proof.LocalCallerCells
