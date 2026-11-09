import ZlibF.Proof.«gzlib.c.dopen-accounting»

/-!
# gzlib.c: descriptor wrapper success on its actual returned heap

These ordinary-mode theorems retain arbitrary descriptor and allocation garbage,
mode storage and file world. Actual allocation success is a branch condition.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- The preserved actual temporary still exists immediately before its free. -/
theorem descriptor_temp_frame (h : Heap) (fd : Int32) (after : Heap)
    (hf : ZlibF.Spec.Public.Frame (descriptorEntryHeap h fd) after (fun _ => False)) :
    after.bytes h.nextBlk =
      some (descriptorBuffer (descriptorAllocatedBytes h) (descriptorPath fd).toArray) := by
  have hb := (descriptorEntry_temp h fd).1
  have hl : (descriptorEntryHeap h fd).live h.nextBlk := Or.inl (by simp [hb])
  exact (hf.2.2.2.2.2 h.nextBlk hl (by simp)).1.trans hb

/-- Real descriptor wrapper w/wT execution and OpenState on the same final
heap after temporary-path free; no integer/pointer garbage is set to zero. -/
theorem gzdopen_writer_success (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (transparent : Bool) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode (if transparent then [119, 84] else [119]))
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc + 1) = true)
    (ha2 : h.allocOk (h.nalloc + 2) = true) :
    let entry := descriptorEntryHeap h fd
    let inner := writerOpenHeap entry transparent (descriptorPath fd) fd
    let result := writerOpenState entry transparent fd
    gzdopen fd mode fs h =
      .ok ((some (.in_gzstate_x entry.nextBlk), fs), descriptorReleased inner h.nextBlk) ∧
    ZlibF.Spec.Public.OpenState (descriptorReleased inner h.nextBlk) entry.nextBlk result
      .write (-1) 0 (if transparent then 1 else 0) fd (descriptorPath fd) := by
  dsimp only
  have hfd : fd ≠ -1 := by
    intro he
    rw [he] at hn
    contradiction
  obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
  have hio : writerIoResult (descriptorPath fd).toArray fd fs = (fd, fs) := by simp [writerIoResult, hfd]
  have hrun := gz_open_writer_allocated_run (descriptorEntryHeap h fd) fs
    (.ref (.blk h.nextBlk) 0) mode fd transparent (descriptorPath fd) hfe
    (descriptorEntry_path h fd hn) (descriptorEntry_cstring h fd mode _ hf hm)
    (by have hlen := descriptorPath_length fd hn; omega)
    (by simpa only [(descriptorEntry_counts h fd).2.1, (descriptorEntry_counts h fd).2.2] using ha1)
    (by simpa only [(descriptorEntry_counts h fd).2.1, (descriptorEntry_counts h fd).2.2, Nat.add_assoc] using ha2)
  rw [hio] at hrun
  simp only [hfd, ite_false] at hrun
  have hframe := writerOpen_frame (descriptorEntryHeap h fd) transparent (descriptorPath fd) fd hfe hue
  constructor
  · rw [gzdopen_entry h fs fd mode hf hn ha]
    unfold descriptorOpenTail
    offsetsimp [hrun, descriptor_free_frame h fd _ hframe]
  · have ho := gz_open_writer_allocated_OpenState (descriptorEntryHeap h fd) fs fd transparent
      (descriptorPath fd) hfe hue (descriptorEntry_globals h fd hg) (descriptorPath_nonzero fd)
      (by have hlen := descriptorPath_length fd hn; omega) (by simpa only [hio] using hfd)
    rw [hio] at ho
    apply descriptorReleased_OpenState _ _ h.nextBlk _ .write (-1) 0 (if transparent then 1 else 0) fd
      (descriptorPath fd) _ ho (descriptor_temp_frame h fd _ hframe)
    have hcount := (descriptorEntry_counts h fd).1
    cases transparent <;>
      simp [writerOpenState, writerEntryRecord, resetRec, GZ_WRITE, GZ_READ, hcount] <;> omega

/-- Real descriptor wrapper r/rG execution, seek and reset remain connected to
OpenState on the returned heap after the actual temporary-path release. -/
theorem gzdopen_reader_success (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (gzipOnly : Bool) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode (if gzipOnly then [114, 71] else [114]))
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc + 1) = true)
    (ha2 : h.allocOk (h.nalloc + 2) = true) :
    let entry := descriptorEntryHeap h fd
    let io := readerIoResult (descriptorPath fd).toArray fd fs
    let inner := readerOpenHeap entry gzipOnly (descriptorPath fd) io
    let result := readerOpenState entry gzipOnly io
    gzdopen fd mode fs h =
      .ok ((some (.in_gzstate_x entry.nextBlk), io.fs), descriptorReleased inner h.nextBlk) ∧
    ZlibF.Spec.Public.OpenState (descriptorReleased inner h.nextBlk) entry.nextBlk result
      .read (-1) 0 (if gzipOnly then -1 else 0) fd (descriptorPath fd) := by
  dsimp only
  have hfd : fd ≠ -1 := by
    intro he
    rw [he] at hn
    contradiction
  have hiofd : (readerIoResult (descriptorPath fd).toArray fd fs).fd = fd := by
    simp [readerIoResult, hfd]
  have hioneg : (readerIoResult (descriptorPath fd).toArray fd fs).fd ≠ -1 := by rwa [hiofd]
  obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
  have hrun := gz_open_reader_allocated_run (descriptorEntryHeap h fd) fs
    (.ref (.blk h.nextBlk) 0) mode fd gzipOnly (descriptorPath fd) hfe
    (descriptorEntry_path h fd hn) (descriptorEntry_cstring h fd mode _ hf hm)
    (by have hlen := descriptorPath_length fd hn; omega)
    (by simpa only [(descriptorEntry_counts h fd).2.1, (descriptorEntry_counts h fd).2.2] using ha1)
    (by simpa only [(descriptorEntry_counts h fd).2.1, (descriptorEntry_counts h fd).2.2, Nat.add_assoc] using ha2)
  simp only [hioneg, ite_false] at hrun
  have hframe := readerOpen_frame (descriptorEntryHeap h fd) gzipOnly (descriptorPath fd)
    (readerIoResult (descriptorPath fd).toArray fd fs) hfe hue
  constructor
  · rw [gzdopen_entry h fs fd mode hf hn ha]
    unfold descriptorOpenTail
    offsetsimp [hrun, descriptor_free_frame h fd _ hframe]
  · have ho := gz_open_reader_allocated_OpenState (descriptorEntryHeap h fd) gzipOnly (descriptorPath fd)
      (readerIoResult (descriptorPath fd).toArray fd fs) hfe hue (descriptorEntry_globals h fd hg)
      (descriptorPath_nonzero fd) (by have hlen := descriptorPath_length fd hn; omega) hioneg
    rw [hiofd] at ho
    apply descriptorReleased_OpenState _ _ h.nextBlk _ .read (-1) 0 (if gzipOnly then -1 else 0) fd
      (descriptorPath fd) _ ho (descriptor_temp_frame h fd _ hframe)
    have hcount := (descriptorEntry_counts h fd).1
    cases gzipOnly <;>
      simp [readerOpenState, readerEntryRecord, readerCheckedRecord, resetRec, GZ_READ, hcount] <;> omega

/-- The same actual successful wrapper execution has its public state, caller
frame and exact final owned-allocation ledger after temporary cleanup. -/
theorem gzdopen_writer_accounted (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (transparent : Bool) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode (if transparent then [119, 84] else [119]))
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc + 1) = true)
    (ha2 : h.allocOk (h.nalloc + 2) = true) :
    let entry := descriptorEntryHeap h fd
    let inner := writerOpenHeap entry transparent (descriptorPath fd) fd
    let result := writerOpenState entry transparent fd
    gzdopen fd mode fs h =
      .ok ((some (.in_gzstate_x entry.nextBlk), fs), descriptorReleased inner h.nextBlk) ∧
    ZlibF.Spec.Public.OpenState (descriptorReleased inner h.nextBlk) entry.nextBlk result
      .write (-1) 0 (if transparent then 1 else 0) fd (descriptorPath fd) ∧
    ZlibF.Spec.Public.Frame h (descriptorReleased inner h.nextBlk) (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h (descriptorReleased inner h.nextBlk)
      (ZlibF.Spec.Public.GzOwned (descriptorReleased inner h.nextBlk) entry.nextBlk result) (fun _ => False) := by
  dsimp only
  obtain ⟨hrun, ho⟩ := gzdopen_writer_success h fs fd mode transparent hf hu hg hn hm ha ha1 ha2
  obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
  have hfd : fd ≠ -1 := by
    intro he
    rw [he] at hn
    contradiction
  have hframe := writerOpen_frame (descriptorEntryHeap h fd) transparent (descriptorPath fd) fd hfe hue
  have hledger := writerOpen_ledger (descriptorEntryHeap h fd) transparent (descriptorPath fd) fd hfe hue
  have hl : ZlibF.Spec.Public.LiveChange (descriptorEntryHeap h fd)
      (writerOpenHeap (descriptorEntryHeap h fd) transparent (descriptorPath fd) fd)
      (fun b => b = (descriptorEntryHeap h fd).nextBlk ∨ b = (descriptorEntryHeap h fd).nextBlk + 1)
      (fun _ => False) := by simpa [hfd] using hledger
  have hno : ¬ (h.nextBlk = (descriptorEntryHeap h fd).nextBlk ∨
      h.nextBlk = (descriptorEntryHeap h fd).nextBlk + 1) := by
    rw [(descriptorEntry_counts h fd).1]
    omega
  have hfinal := descriptorCaller_ledger h fd _ _ hf hue hframe hl hno
  refine ⟨hrun, ho, descriptorCaller_frame h fd _ hf hframe, ?_⟩
  intro b
  change (descriptorReleased (writerOpenHeap (descriptorEntryHeap h fd) transparent (descriptorPath fd) fd) h.nextBlk).live b ↔
    ((h.live b ∧ ¬ False) ∨ ZlibF.Spec.Public.GzOwned
      (descriptorReleased (writerOpenHeap (descriptorEntryHeap h fd) transparent (descriptorPath fd) fd) h.nextBlk)
      (descriptorEntryHeap h fd).nextBlk (writerOpenState (descriptorEntryHeap h fd) transparent fd) b)
  have hsize : (writerOpenState (descriptorEntryHeap h fd) transparent fd).size = 0 := by
    cases transparent <;> rfl
  rw [← descriptorOwned_zero_heap (writerOpenHeap (descriptorEntryHeap h fd) transparent (descriptorPath fd) fd)
    _ _ _ hsize b, writerOpen_owned]
  exact hfinal b

/-- The same actual successful wrapper execution has its public state, caller
frame and exact final owned-allocation ledger after temporary cleanup. -/
theorem gzdopen_reader_accounted (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (gzipOnly : Bool) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ≤ fd.toInt)
    (hm : ZlibF.Spec.Public.CString h mode (if gzipOnly then [114, 71] else [114]))
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc + 1) = true)
    (ha2 : h.allocOk (h.nalloc + 2) = true) :
    let entry := descriptorEntryHeap h fd
    let io := readerIoResult (descriptorPath fd).toArray fd fs
    let inner := readerOpenHeap entry gzipOnly (descriptorPath fd) io
    let result := readerOpenState entry gzipOnly io
    gzdopen fd mode fs h =
      .ok ((some (.in_gzstate_x entry.nextBlk), io.fs), descriptorReleased inner h.nextBlk) ∧
    ZlibF.Spec.Public.OpenState (descriptorReleased inner h.nextBlk) entry.nextBlk result
      .read (-1) 0 (if gzipOnly then -1 else 0) fd (descriptorPath fd) ∧
    ZlibF.Spec.Public.Frame h (descriptorReleased inner h.nextBlk) (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h (descriptorReleased inner h.nextBlk)
      (ZlibF.Spec.Public.GzOwned (descriptorReleased inner h.nextBlk) entry.nextBlk result) (fun _ => False) := by
  dsimp only
  obtain ⟨hrun, ho⟩ := gzdopen_reader_success h fs fd mode gzipOnly hf hu hg hn hm ha ha1 ha2
  obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
  have hfd : fd ≠ -1 := by
    intro he
    rw [he] at hn
    contradiction
  have hframe := readerOpen_frame (descriptorEntryHeap h fd) gzipOnly (descriptorPath fd) (readerIoResult (descriptorPath fd).toArray fd fs) hfe hue
  have hledger := readerOpen_ledger (descriptorEntryHeap h fd) gzipOnly (descriptorPath fd) (readerIoResult (descriptorPath fd).toArray fd fs) hfe hue
  have hioneg : (readerIoResult (descriptorPath fd).toArray fd fs).fd ≠ -1 := by
    simp [readerIoResult, hfd]
  have hl : ZlibF.Spec.Public.LiveChange (descriptorEntryHeap h fd)
      (readerOpenHeap (descriptorEntryHeap h fd) gzipOnly (descriptorPath fd) (readerIoResult (descriptorPath fd).toArray fd fs))
      (fun b => b = (descriptorEntryHeap h fd).nextBlk ∨ b = (descriptorEntryHeap h fd).nextBlk + 1)
      (fun _ => False) := by simpa [hioneg] using hledger
  have hno : ¬ (h.nextBlk = (descriptorEntryHeap h fd).nextBlk ∨
      h.nextBlk = (descriptorEntryHeap h fd).nextBlk + 1) := by
    rw [(descriptorEntry_counts h fd).1]
    omega
  have hfinal := descriptorCaller_ledger h fd _ _ hf hue hframe hl hno
  refine ⟨hrun, ho, descriptorCaller_frame h fd _ hf hframe, ?_⟩
  intro b
  change (descriptorReleased (readerOpenHeap (descriptorEntryHeap h fd) gzipOnly (descriptorPath fd) (readerIoResult (descriptorPath fd).toArray fd fs)) h.nextBlk).live b ↔
    ((h.live b ∧ ¬ False) ∨ ZlibF.Spec.Public.GzOwned
      (descriptorReleased (readerOpenHeap (descriptorEntryHeap h fd) gzipOnly (descriptorPath fd) (readerIoResult (descriptorPath fd).toArray fd fs)) h.nextBlk)
      (descriptorEntryHeap h fd).nextBlk (readerOpenState (descriptorEntryHeap h fd) gzipOnly (readerIoResult (descriptorPath fd).toArray fd fs)) b)
  have hsize : (readerOpenState (descriptorEntryHeap h fd) gzipOnly (readerIoResult (descriptorPath fd).toArray fd fs)).size = 0 := by
    cases gzipOnly <;> rfl
  rw [← descriptorOwned_zero_heap (readerOpenHeap (descriptorEntryHeap h fd) gzipOnly (descriptorPath fd) (readerIoResult (descriptorPath fd).toArray fd fs))
    _ _ _ hsize b, readerOpen_owned]
  exact hfinal b

#print axioms gzdopen_writer_accounted
#print axioms gzdopen_reader_accounted
#print axioms descriptor_temp_frame
#print axioms gzdopen_writer_success
#print axioms gzdopen_reader_success
end Zlib.Gzlib.Proofs
