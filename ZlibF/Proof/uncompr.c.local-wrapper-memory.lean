import ZlibF.Proof.«uncompr.c.local-wrapper-safe»
import ZlibF.Proof.«uncompr.c.initial-refusal»

namespace Zlib.Uncompr.Proof.LocalWrapperSafe
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Finish
open Zlib.Uncompr.Proof.InitialRefusal
set_option autoImplicit false

/-- The actual valid-entry wrapper has no first-allocation-success assumption.
First refusal retains both input scalar values; after successful init, ordinary
return writes exact consumed and produced counts. Both alternatives leave no
allocation residue. The explicit platform and scalar/range separation premises remain visible;
there is no uniqueness premise on old caller objects. -/
theorem uncompress2_z_memory (h : Heap) (source dest sourceLen destLen : BPtr)
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
      LocalWrapperSafe.uncompress2_z_safe h source dest sourceLen destLen n capacity xs
        fresh globals platform allocation inputCell outputCell readable writable separate
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
end Zlib.Uncompr.Proof.LocalWrapperSafe
