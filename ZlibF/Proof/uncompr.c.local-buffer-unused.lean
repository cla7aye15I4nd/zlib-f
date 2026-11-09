import ZlibF.Proof.«uncompr.c.local-wrapper-memory»

namespace Zlib.Uncompr.Proof.LocalBufferUnused
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Finish
set_option autoImplicit false

private theorem mapped_buffer_remaining (err : Int32) (remaining : UInt64)
    (mapped : resultCode err remaining = Z_BUF_ERROR) : remaining ≠ 0 := by
  intro zero
  rw [zero] at mapped
  by_cases selected : err = Z_BUF_ERROR
  · subst err
    simp [resultCode,Z_BUF_ERROR,Z_STREAM_END,Z_NEED_DICT,Z_DATA_ERROR] at mapped
  · unfold resultCode at mapped
    split at mapped
    · exact (by decide : Z_OK ≠ Z_BUF_ERROR) mapped
    · split at mapped
      · exact (by decide : Z_DATA_ERROR ≠ Z_BUF_ERROR) mapped
      · split at mapped
        · exact (by decide : Z_DATA_ERROR ≠ Z_BUF_ERROR) mapped
        · exact selected mapped

/-- Actual buffer exhaustion leaves at least one source byte unused.
This follows from the real result map and exact outer remainder, including
UInt32 chunk boundaries; no valid-format assumption is required. -/
theorem uncompress2_z_buffer_unused (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (after : Heap)
    (actual : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (Z_BUF_ERROR, after)) :
    ∃ used, LengthCell after sourceLen (UInt64.ofNat used) ∧ used < n.toNat := by
  obtain ⟨rc,returned,run,_ledger,refused,counted⟩ := LocalWrapperSafe.uncompress2_z_memory
    h source dest sourceLen destLen n capacity xs fresh globals platform inputCell outputCell
    readable writable separate sourceSeparate destSeparate cellSeparate validInput validOutput
  cases Except.ok.inj (run.symm.trans actual)
  have allocation : h.allocOk h.nalloc = true := by
    cases flag : h.allocOk h.nalloc with
    | true => rfl
    | false =>
      have impossible := (refused flag).1
      exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_MEM_ERROR) impossible)
  obtain ⟨used,made,sourceCell,_destCell,_usedBound,_madeBound,
      err,remain,_stopped,_codes,mapped,count⟩ := counted allocation
  have positive : 0 < remain.toNat := by
    have nonzero := mapped_buffer_remaining err remain mapped.symm
    have natNonzero : remain.toNat ≠ 0 := by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    omega
  exact ⟨used,sourceCell,by omega⟩

#print axioms uncompress2_z_buffer_unused
end Zlib.Uncompr.Proof.LocalBufferUnused
