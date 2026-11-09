import ZlibF.Proof.«gzlib.c.open-read-mode»

/-!
# gzlib.c: actual reader open, seek, and reset

File-open and seek results come from their fixed actual computations. Reset
establishes the read fields and preserves the old `x.next` pointer unchanged.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Actual descriptor, final world, and saved initial read position. -/
structure ReaderIoResult where
  fd : Int32
  fs : Fs
  start : Int64

/-- The fixed actual read open followed by the actual current-position query. -/
def readerIoResult (name : Array UInt8) (fd : Int32) (fs : Fs) : ReaderIoResult :=
  let opened := if fd = -1 then openFsResult name 0 fs else (fd, fs)
  if opened.1 = -1 then { fd := opened.1, fs := opened.2, start := 0 }
  else
    let seek := lseekRes opened.1 0 SEEK_CUR opened.2
    { fd := opened.1, fs := seek.2, start := if seek.1 = -1 then 0 else seek.1 }

/-- Exact reader heap on actual open refusal or successful seek/reset. -/
def readerIoHeap (h : Heap) (i pb : Nat) (s : GzState) (result : ReaderIoResult) : Heap :=
  if result.fd = -1 then
    { h with bytes := upd h.bytes pb none, gzstates := upd h.gzstates i none }
  else setS h i (resetRec { s with fd := result.fd, start := result.start })

/-- The actual post-copy read tail, for arbitrary file worlds, supplied
descriptors, caller storage, and old pointer/integer fields. Refusal frees the
copied path and handle. Success performs real `lseek` and read-mode reset. -/
theorem openAfterPath_reader (h : Heap) (fs : Fs) (i pb : Nat) (s : GzState)
    (ml : ModeLoop) (path : BPtr) (fd : Int32) (name : List UInt8) (copy : Array UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ) (hmsg : s.msg = .null)
    (hflags : ml.oflag = 0) (hexcl : ml.exclusive = 0)
    (hpath : ZlibF.Spec.Public.CString h path name)
    (hprivate : s.path = .ref (.blk pb) 0)
    (hcopy : h.bytes pb = some copy) (hro : h.ro pb = false) :
    openAfterPath (some (.tab i)) path fd ml fs h =
      .ok (((if (readerIoResult name.toArray fd fs).fd = -1 then none
        else some (.in_gzstate_x i)), (readerIoResult name.toArray fd fs).fs),
        readerIoHeap h i pb s (readerIoResult name.toArray fd fs)) := by
  have hname := openPath_cstring_public h path name hpath
  by_cases hfd : fd = -1
  · by_cases hf : (openFsResult name.toArray 0 fs).1 = -1
    · unfold openAfterPath
      offsetsimp [hs, hm, hflags, hexcl, hfd, hname, openFs_eq, readerIoResult,
        readerIoHeap, hf, hprivate, hcopy, hro, freeB, freeGzState,
        setS, upd_upd, O_LARGEFILE, GZ_READ, GZ_APPEND, hnd]
    · by_cases ht : (lseekRes (openFsResult name.toArray 0 fs).1 0 SEEK_CUR
          (openFsResult name.toArray 0 fs).2).1 = -1
      · unfold openAfterPath
        offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname, openFs_eq,
          readerIoResult, readerIoHeap, hf, ht, gz_reset, gz_error, resetRec,
          setS, upd_upd, O_LARGEFILE, GZ_READ, GZ_APPEND, hnd]
      · unfold openAfterPath
        offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname, openFs_eq,
          readerIoResult, readerIoHeap, hf, ht, gz_reset, gz_error, resetRec,
          setS, upd_upd, O_LARGEFILE, GZ_READ, GZ_APPEND, hnd]
  · by_cases ht : (lseekRes fd 0 SEEK_CUR fs).1 = -1
    · unfold openAfterPath
      offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname, readerIoResult,
        readerIoHeap, ht, gz_reset, gz_error, resetRec, fsFcntl,
        setS, upd_upd, O_LARGEFILE, GZ_READ, GZ_APPEND, hnd]
    · unfold openAfterPath
      offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname, readerIoResult,
        readerIoHeap, ht, gz_reset, gz_error, resetRec, fsFcntl,
        setS, upd_upd, O_LARGEFILE, GZ_READ, GZ_APPEND, hnd]

/-- The read tail establishes the public state from real prepared fields and
allocated path facts, with arbitrary preserved pointer and integer fields. -/
theorem readerIoHeap_OpenState (h : Heap) (i pb : Nat) (s : GzState) (result : ReaderIoResult)
    (name : List UInt8) (direct : Int)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ)
    (hprivate : s.path = .ref (.blk pb) 0)
    (hsize : s.size = 0) (hwant : s.want = 8192)
    (hlevel : s.level = Z_DEFAULT_COMPRESSION) (hstrategy : s.strategy = Z_DEFAULT_STRATEGY)
    (hdirect : s.direct.toInt = (if direct = 0 then 1 else direct)) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hpath : ZlibF.Spec.Public.CString h (.ref (.blk pb) 0) name)
    (hbuf : ZlibF.Spec.Public.MallocBuffer h (.ref (.blk pb) 0) (name.length + 1))
    (hresult : result.fd ≠ -1) :
    ZlibF.Spec.Public.OpenState (readerIoHeap h i pb s result) i
      (resetRec { s with fd := result.fd, start := result.start }) .read (-1) 0 direct result.fd name := by
  rw [readerIoHeap, ite_eq_right (by exact hresult)]
  let final := resetRec { s with fd := result.fd, start := result.start }
  have hshape := shape_setS hs final
  have hpf := openCString_setS h i final (.ref (.blk pb) 0) name hpath
  have hbf := openMallocBuffer_setS h i final (.ref (.blk pb) 0) (name.length + 1) hbuf
  have hfinalPath : final.path = .ref (.blk pb) 0 := by
    simp [final, resetRec, hm, hprivate, GZ_READ]
  have hv : ZlibF.Spec.Public.GzValid (setS h i final) i final := by
    refine ⟨by simp [setS], ?_, Shape.fresh hshape rfl hf, Shape.uniq hshape hu,
      hg, ⟨name, ?_, ?_⟩, Or.inl ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [final, resetRec, hm, GZ_READ]
    · simpa only [hfinalPath] using hpf
    · simpa only [hfinalPath] using hbf
    · simp [final, resetRec, hm, GZ_READ]
    · intro _; simp [final, resetRec, hm, GZ_READ]
    · simp [final, resetRec, hwant, hm, GZ_READ]
    · simp [final, resetRec, hwant, hm, GZ_READ]
    · simp [final, resetRec, hsize, hm, GZ_READ]
    · simp [final, resetRec, hm, GZ_READ]
  refine ⟨hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (change ZlibF.Spec.Public.CString (setS h i final) final.path name
       rw [hfinalPath]
       exact hpf)
    | simp [resetRec, hm, hprivate, hsize, hwant, hlevel, hstrategy,
        hdirect, GZ_READ, Z_DEFAULT_COMPRESSION, Z_DEFAULT_STRATEGY]

/-- The actual reader OS operations satisfy the fixed public world relation.
Both r and rG use read-only flags; the real seek result determines start. -/
theorem readerIoResult_OpenWorld (h : Heap) (fs : Fs) (name : List UInt8) (fd : Int32)
    (gzipOnly : Bool) :
    ZlibF.Spec.Public.OpenWorld h fs (readerIoResult name.toArray fd fs).fs name
      (if gzipOnly then [114, 71] else [114]) .read
      (if fd = -1 then none else some fd) (readerIoResult name.toArray fd fs).fd
      (readerIoResult name.toArray fd fs).start := by
  have hflags : ZlibF.Spec.Public.openFlags (if gzipOnly then [114, 71] else [114]) .read = 0 := by
    cases gzipOnly <;> decide
  by_cases he : fd = -1
  · by_cases hf : (openFsResult name.toArray 0 fs).1 = -1
    · refine ⟨(openFsResult name.toArray 0 fs).2, ?_, ?_⟩
      · have hpair : openFsResult name.toArray 0 fs = (-1, (openFsResult name.toArray 0 fs).2) := by
          apply Prod.ext
          · exact hf
          · rfl
        have hcall := openFs_eq name.toArray 0 fs h
        rw [hpair] at hcall
        simpa [readerIoResult, he, hf, hflags] using hcall
      · simp [readerIoResult, he, hf]
    · refine ⟨(openFsResult name.toArray 0 fs).2, ?_, ?_⟩
      · simpa [readerIoResult, he, hf, hflags] using openFs_eq name.toArray 0 fs h
      · simp only [readerIoResult, he, ite_true, hf, ite_false]
        exact ⟨(lseekRes (openFsResult name.toArray 0 fs).1 0 SEEK_CUR
          (openFsResult name.toArray 0 fs).2).1, fsLseek_eq _ _ _ _ _, rfl⟩
  · refine ⟨fs, ?_, ?_⟩
    · simp [readerIoResult, he]
    · simp only [readerIoResult, he, ite_false]
      exact ⟨(lseekRes fd 0 SEEK_CUR fs).1, fsLseek_eq _ _ _ _ _, rfl⟩

/-- Reset preserves arbitrary old x.next; later reading needs the real gz_look
pointer write. This is explicitly not pointer-initialization evidence. -/
theorem readerReset_next (s : GzState) (result : ReaderIoResult) :
    (resetRec { s with fd := result.fd, start := result.start }).x.next = s.x.next := rfl

/-- Saving the actual initial read position changes only the handle record,
with no effect on object kinds or unrelated data. -/
theorem readerIoHeap_congr (h : Heap) (i pb : Nat) (s : GzState) (result : ReaderIoResult) :
    ZlibF.Spec.Public.Frame (writerIoHeap h i pb s result.fd) (readerIoHeap h i pb s result)
      (fun b => b = i) ∧
    Shape (writerIoHeap h i pb s result.fd) (readerIoHeap h i pb s result) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (intro b _ hb
         by_cases hr : result.fd = -1 <;> simp [readerIoHeap, writerIoHeap, hr, setS, hb])
      | (by_cases hr : result.fd = -1 <;> simp [readerIoHeap, writerIoHeap, hr, setS])
  · intro b
    by_cases hr : result.fd = -1 <;> by_cases hb : b = i <;>
      simp [readerIoHeap, writerIoHeap, hr, setS, hb]

/-- Both reader I/O results have exact frame and allocation accounting, including
all open refusals; the real seek itself never creates a C heap allocation. -/
theorem readerIoHeap_ledger (h : Heap) (i pb : Nat) (s : GzState) (result : ReaderIoResult)
    (copy : Array UInt8) (hu : Uniq h) (hs : h.gzstates i = some s)
    (hp : h.bytes pb = some copy) :
    ZlibF.Spec.Public.Frame h (readerIoHeap h i pb s result)
      (fun b => b = i ∨ result.fd = -1 ∧ b = pb) ∧
    ZlibF.Spec.Public.LiveChange h (readerIoHeap h i pb s result)
      (fun _ => False) (fun b => result.fd = -1 ∧ (b = i ∨ b = pb)) := by
  have hbase := writerIoHeap_ledger h i pb s result.fd copy hu hs hp
  have hcongr := readerIoHeap_congr h i pb s result
  constructor
  · obtain ⟨s1, o1, g1, n1, a1, f1⟩ := hbase.1
    obtain ⟨s2, o2, g2, n2, a2, f2⟩ := hcongr.1
    refine ⟨s1.trans s2, o1.trans o2, g1.trans g2, Nat.le_trans n1 n2,
      Nat.le_trans a1 a2, ?_⟩
    intro b hl hn
    have hbi : b ≠ i := fun he => hn (Or.inl he)
    have hremoved : ¬ (result.fd = -1 ∧ (b = i ∨ b = pb)) := by
      rintro ⟨hf, hi | hpb⟩
      · exact hn (Or.inl hi)
      · exact hn (Or.inr ⟨hf, hpb⟩)
    have hb : (writerIoHeap h i pb s result.fd).live b := (hbase.2 b).2 (Or.inl ⟨hl, hremoved⟩)
    obtain ⟨b1, w1, z1, g1, d1, i1, s1, r1⟩ := f1 b hl hn
    obtain ⟨b2, w2, z2, g2, d2, i2, s2, r2⟩ := f2 b hb hbi
    exact ⟨b2.trans b1, w2.trans w1, z2.trans z1, g2.trans g1, d2.trans d1,
      i2.trans i1, s2.trans s1, r2.trans r1⟩
  · intro b
    exact (Shape.live hcongr.2 b).trans (hbase.2 b)

#print axioms openAfterPath_reader
#print axioms readerIoHeap_OpenState
#print axioms readerIoResult_OpenWorld
#print axioms readerReset_next
#print axioms readerIoHeap_ledger
end Zlib.Gzlib.Proofs
