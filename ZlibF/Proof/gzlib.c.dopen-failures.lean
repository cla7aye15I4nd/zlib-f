import ZlibF.Proof.«gzlib.c.dopen-accounting»

/-!
# gzlib.c: descriptor wrapper allocation refusals

Every actual allocation phase has a concrete failure result and exact caller
frame/no-new-live ledger. The existing descriptor and file world are retained.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Any valid caller mode is untouched when the actual inner handle allocation
refuses. Formatting and the final wrapper free still execute in source order. -/
theorem gzdopen_inner_alloc_failure (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (flags : List UInt8) (hf : Fresh h) (hu : Uniq h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode flags) (ha : h.allocOk h.nalloc = true)
    (ha1 : h.allocOk (h.nalloc + 1) = false) :
    let entry := descriptorEntryHeap h fd
    let inner := { entry with nalloc := entry.nalloc + 1 }
    let after := descriptorReleased inner h.nextBlk
    gzdopen fd mode fs h = .ok ((none, fs), after) ∧
    ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
    ZlibF.Spec.Public.AllocationFailed h after := by
  dsimp only
  obtain ⟨_, hue⟩ := descriptorEntry_invariants h fd hf hu
  have he : (descriptorEntryHeap h fd).allocOk (descriptorEntryHeap h fd).nalloc = false := by
    simpa only [(descriptorEntry_counts h fd).2.1, (descriptorEntry_counts h fd).2.2] using ha1
  have hm' := descriptorEntry_cstring h fd mode flags hf hm
  obtain ⟨r, off, a, hptr, _, _, _⟩ := writerCString_view _ mode flags hm'
  have hmn : mode ≠ .null := by simp [hptr]
  have hrun := gz_open_alloc_failure (descriptorEntryHeap h fd) fs (.ref (.blk h.nextBlk) 0)
    fd mode (by simp) hmn he
  obtain ⟨hframe, hlive, hfailed⟩ := writerFirstFailure_checks (descriptorEntryHeap h fd) he
  refine ⟨?_, descriptorCaller_frame h fd _ hf hframe,
    descriptorCaller_ledger h fd _ (fun _ => False) hf hue hframe hlive (by simp),
    descriptorCaller_allocation_failed h fd _ hfailed⟩
  rw [gzdopen_entry h fs fd mode hf hn ha]
  unfold descriptorOpenTail
  offsetsimp [hrun, descriptor_free_frame h fd _ hframe]

/-- Actual mode bytes for the four ordinary descriptor-wrapper branches. -/
def descriptorMode (reading variant : Bool) : List UInt8 :=
  if reading then (if variant then [114, 71] else [114])
  else (if variant then [119, 84] else [119])

/-- Refusal of the actual private-path allocation frees both the inner handle
and, finally, the wrapper temporary, preserving every original allocation. -/
theorem gzdopen_inner_path_failure (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (reading variant : Bool) (hf : Fresh h) (hu : Uniq h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode (descriptorMode reading variant))
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc + 1) = true)
    (ha2 : h.allocOk (h.nalloc + 2) = false) :
    let entry := descriptorEntryHeap h fd
    let inner := { openReleased entry with nalloc := entry.nalloc + 2 }
    let after := descriptorReleased inner h.nextBlk
    gzdopen fd mode fs h = .ok ((none, fs), after) ∧
    ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
    ZlibF.Spec.Public.AllocationFailed h after := by
  dsimp only
  obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
  have he : (descriptorEntryHeap h fd).allocOk ((descriptorEntryHeap h fd).nalloc + 1) = false := by
    simpa only [(descriptorEntry_counts h fd).2.1, (descriptorEntry_counts h fd).2.2, Nat.add_assoc] using ha2
  have ha' : (descriptorEntryHeap h fd).allocOk (descriptorEntryHeap h fd).nalloc = true := by
    simpa only [(descriptorEntry_counts h fd).2.1, (descriptorEntry_counts h fd).2.2] using ha1
  have hm' := descriptorEntry_cstring h fd mode (descriptorMode reading variant) hf hm
  have hrun : gz_open (.ref (.blk h.nextBlk) 0) fd mode fs (descriptorEntryHeap h fd) =
      .ok ((none, fs), { openReleased (descriptorEntryHeap h fd) with
        nalloc := (descriptorEntryHeap h fd).nalloc + 2 }) := by
    cases reading
    · exact gz_open_writer_path_failure _ fs _ mode fd variant (descriptorPath fd) hfe
        (descriptorEntry_path h fd hn) hm' ha' he
    · exact gz_open_reader_path_failure _ fs _ mode fd variant (descriptorPath fd) hfe
        (descriptorEntry_path h fd hn) hm' ha' he
  obtain ⟨hframe, hlive, hfailed⟩ := writerPathFailure_checks (descriptorEntryHeap h fd) hfe he
  refine ⟨?_, descriptorCaller_frame h fd _ hf hframe,
    descriptorCaller_ledger h fd _ (fun _ => False) hf hue hframe hlive (by simp),
    descriptorCaller_allocation_failed h fd _ hfailed⟩
  rw [gzdopen_entry h fs fd mode hf hn ha]
  unfold descriptorOpenTail
  offsetsimp [hrun, descriptor_free_frame h fd _ hframe]

#print axioms gzdopen_inner_alloc_failure
#print axioms gzdopen_inner_path_failure
end Zlib.Gzlib.Proofs
