import ZlibF.Proof.«gzlib.c.open-copy-stage»

/-!
# gzlib.c: composed ordinary read tail

The internal short-path branch retains the separate full-domain goal. The
actual guard, allocation, copy, I/O and reset share one execution heap.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Exact reader allocation/copy/I/O heap, including the saved seek result. -/
def readerFinishedHeap (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool)
    (name : List UInt8) (result : ReaderIoResult) : Heap :=
  readerIoHeap (readerFormattedHeap h i s gzipOnly name) i h.nextBlk
    { readerCheckedRecord s gzipOnly with path := .ref (.blk h.nextBlk) 0 } result

/-- The actual r/rG tail, through both allocation and OS success or refusal.
No library contract is an input and all old pointer values remain arbitrary. -/
theorem openAfterMode_reader_run (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (path : BPtr) (fd : Int32) (ml : ModeLoop) (gzipOnly : Bool) (name : List UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ)
    (hd : s.direct = if gzipOnly then -1 else 0) (hmsg : s.msg = .null)
    (hdone : ml.done = false) (hflags : ml.oflag = 0) (hexcl : ml.exclusive = 0)
    (hf : Fresh h) (hc : ZlibF.Spec.Public.CString h path name)
    (hlen : name.length ≤ 2147483647) (hok : h.allocOk h.nalloc = true) :
    openAfterMode (some (.tab i)) path fd ml fs h =
      .ok (((if (readerIoResult name.toArray fd fs).fd = -1 then none
        else some (.in_gzstate_x i)), (readerIoResult name.toArray fd fs).fs),
        readerFinishedHeap h i s gzipOnly name (readerIoResult name.toArray fd fs)) := by
  have hfc : Fresh (readerCheckedHeap h i s gzipOnly) := by
    cases gzipOnly
    · exact Shape.fresh (shape_setS hs _) rfl hf
    · exact hf
  rw [openAfterMode_reader_copy h fs i s path fd ml gzipOnly name hs hm hd hdone hf hc hlen hok]
  have hn : (readerCheckedHeap h i s gzipOnly).nextBlk = h.nextBlk := by cases gzipOnly <;> rfl
  have hmc : (readerCheckedRecord s gzipOnly).mode = GZ_READ := by cases gzipOnly <;> exact hm
  have hmsgc : (readerCheckedRecord s gzipOnly).msg = .null := by cases gzipOnly <;> exact hmsg
  have hcall := openAfterPath_reader
    (writerFormattedHeap (readerCheckedHeap h i s gzipOnly) i (readerCheckedRecord s gzipOnly) name)
    fs i (readerCheckedHeap h i s gzipOnly).nextBlk
    { readerCheckedRecord s gzipOnly with path := .ref (.blk (readerCheckedHeap h i s gzipOnly).nextBlk) 0 }
    ml path fd name (name.toArray.push 0)
    (writerFormatted_state _ i _ name) hmc hmsgc hflags hexcl
    (writerFormatted_cstring _ i _ name path name hfc
      (readerChecked_cstring h i s gzipOnly path name hc)) rfl
    (writerFormatted_private_bytes _ i _ name) (writerFormatted_private_ro _ i _ name)
  simpa only [hn, readerFinishedHeap, readerFormattedHeap] using hcall

/-- The same real tail establishes OpenState on success from initialized
primitive fields and actual allocated-path facts. -/
theorem openAfterMode_reader_OpenState (h : Heap) (i : Nat) (s : GzState)
    (gzipOnly : Bool) (name : List UInt8) (result : ReaderIoResult)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ)
    (hd : s.direct = if gzipOnly then -1 else 0)
    (hsize : s.size = 0) (hwant : s.want = 8192)
    (hlevel : s.level = Z_DEFAULT_COMPRESSION) (hstrategy : s.strategy = Z_DEFAULT_STRATEGY)
    (hf : Fresh h) (hu : Uniq h) (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64) (hr : result.fd ≠ -1) :
    ZlibF.Spec.Public.OpenState (readerFinishedHeap h i s gzipOnly name result) i
      (resetRec { readerCheckedRecord s gzipOnly with
        path := .ref (.blk h.nextBlk) 0
        fd := result.fd
        start := result.start })
      .read (-1) 0 (if gzipOnly then -1 else 0) result.fd name := by
  obtain ⟨hfc, huc⟩ := readerChecked_invariants h i s gzipOnly hs hf hu
  have hsc := readerChecked_state h i s gzipOnly hs
  have hnext : (readerCheckedHeap h i s gzipOnly).nextBlk = h.nextBlk := by cases gzipOnly <;> rfl
  have hgc : ZlibF.Spec.Public.LibraryGlobals (readerCheckedHeap h i s gzipOnly) := by
    cases gzipOnly <;> exact hg
  obtain ⟨hff, huf⟩ := writerFormatted_invariants _ i _ name hfc huc hsc
  obtain ⟨hpath, hbuf⟩ := writerFormatted_private (readerCheckedHeap h i s gzipOnly) i
    (readerCheckedRecord s gzipOnly) name hn hlen
  have hmc : (readerCheckedRecord s gzipOnly).mode = GZ_READ := by cases gzipOnly <;> exact hm
  have hdc : (readerCheckedRecord s gzipOnly).direct.toInt =
      (if (if gzipOnly then -1 else 0 : Int) = 0 then 1 else (if gzipOnly then -1 else 0)) := by
    cases gzipOnly <;> simp [readerCheckedRecord, hd]
  have hcall := readerIoHeap_OpenState _ i (readerCheckedHeap h i s gzipOnly).nextBlk
    { readerCheckedRecord s gzipOnly with path := .ref (.blk (readerCheckedHeap h i s gzipOnly).nextBlk) 0 }
    result name (if gzipOnly then -1 else 0)
    (writerFormatted_state _ i _ name) hmc rfl
    (by cases gzipOnly <;> exact hsize) (by cases gzipOnly <;> exact hwant)
    (by cases gzipOnly <;> exact hlevel) (by cases gzipOnly <;> exact hstrategy)
    hdc hff huf (writerFormatted_globals _ i _ name hgc) hpath hbuf hr
  simpa only [hnext, readerFinishedHeap, readerFormattedHeap] using hcall

/-- The actual read guard and saved start affect only the handle, compared to
an otherwise identical allocation/copy/cleanup heap. Object kinds are equal. -/
theorem readerFinished_congr (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool)
    (name : List UInt8) (result : ReaderIoResult) :
    ZlibF.Spec.Public.Frame (writerFinishedHeap h i s name result.fd)
      (readerFinishedHeap h i s gzipOnly name result) (fun b => b = i) ∧
    Shape (writerFinishedHeap h i s name result.fd) (readerFinishedHeap h i s gzipOnly name result) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (intro b _ hb
         cases gzipOnly <;> by_cases hr : result.fd = -1 <;>
           by_cases hz : name.toArray.isEmpty = true <;>
           simp [readerFinishedHeap, readerFormattedHeap, readerCheckedHeap, readerCheckedRecord,
             readerIoHeap, writerFinishedHeap, writerIoHeap, writerFormattedHeap,
             pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, allocatedPathBytes, upd_upd, hr, hz, setS, hb])
      | (cases gzipOnly <;> by_cases hr : result.fd = -1 <;>
         by_cases hz : name.toArray.isEmpty = true <;>
         simp [readerFinishedHeap, readerFormattedHeap, readerCheckedHeap, readerCheckedRecord,
           readerIoHeap, writerFinishedHeap, writerIoHeap, writerFormattedHeap,
           pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, allocatedPathBytes, upd_upd, hr, hz, setS])
  · intro b
    cases gzipOnly <;> by_cases hr : result.fd = -1 <;>
      by_cases hz : name.toArray.isEmpty = true <;> by_cases hb : b = i <;>
      simp [readerFinishedHeap, readerFormattedHeap, readerCheckedHeap, readerCheckedRecord,
        readerIoHeap, writerFinishedHeap, writerIoHeap, writerFormattedHeap,
        pathFormattedHeap, pathBytesHeap, pathAllocatedHeap, allocatedPathBytes, upd_upd, hr, hz, setS, hb]

/-- Exact accounting for the whole read tail: successful I/O adds the path;
refusal removes the handle. Caller objects other than the handle are preserved. -/
theorem readerFinished_ledger (h : Heap) (i : Nat) (s : GzState) (gzipOnly : Bool)
    (name : List UInt8) (result : ReaderIoResult)
    (hf : Fresh h) (hu : Uniq h) (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.Frame h (readerFinishedHeap h i s gzipOnly name result) (fun b => b = i) ∧
    ZlibF.Spec.Public.LiveChange h (readerFinishedHeap h i s gzipOnly name result)
      (fun b => result.fd ≠ -1 ∧ b = h.nextBlk) (fun b => result.fd = -1 ∧ b = i) := by
  have hb := writerFinished_ledger h i s name result.fd hf hu hs
  have hc := readerFinished_congr h i s gzipOnly name result
  constructor
  · obtain ⟨s1, o1, g1, n1, a1, f1⟩ := hb.1
    obtain ⟨s2, o2, g2, n2, a2, f2⟩ := hc.1
    refine ⟨s1.trans s2, o1.trans o2, g1.trans g2, Nat.le_trans n1 n2,
      Nat.le_trans a1 a2, ?_⟩
    intro b hl hbi
    have hmid : (writerFinishedHeap h i s name result.fd).live b :=
      (hb.2 b).2 (Or.inl ⟨hl, fun he => hbi he.2⟩)
    obtain ⟨b1, w1, z1, g1, d1, i1, s1, r1⟩ := f1 b hl hbi
    obtain ⟨b2, w2, z2, g2, d2, i2, s2, r2⟩ := f2 b hmid hbi
    exact ⟨b2.trans b1, w2.trans w1, z2.trans z1, g2.trans g1, d2.trans d1,
      i2.trans i1, s2.trans s1, r2.trans r1⟩
  · intro b
    exact (Shape.live hc.2 b).trans (hb.2 b)

#print axioms openAfterMode_reader_run
#print axioms openAfterMode_reader_OpenState
#print axioms readerFinished_congr
#print axioms readerFinished_ledger
end Zlib.Gzlib.Proofs
