import ZlibF.Proof.«gzlib.c.open-read-io»

/-!
# gzlib.c: actual append I/O continuation

Append performs its real end seek, ignores that seek's return value, changes
mode to write, and resets. This is distinct from ordinary writer initialization.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Ordinary append flags, before any separate e/N/x options. -/
def appendOpenFlags : Int32 := O_WRONLY ||| O_CREAT ||| O_APPEND

/-- The actual open or supplied descriptor, followed by the actual ignored
end seek when opening succeeded. Seek errors are retained in the world. -/
def appendIoResult (name : Array UInt8) (fd : Int32) (fs : Fs) : Int32 × Fs :=
  let opened := if fd = -1 then openFsResult name appendOpenFlags fs else (fd, fs)
  if opened.1 = -1 then opened
  else (opened.1, (lseekRes opened.1 0 SEEK_END opened.2).2)

/-- Exact append cleanup or post-seek mode transition and reset heap. -/
def appendIoHeap (h : Heap) (i pb : Nat) (s : GzState) (fd : Int32) : Heap :=
  if fd = -1 then
    { h with bytes := upd h.bytes pb none, gzstates := upd h.gzstates i none }
  else setS h i (resetRec { s with fd, mode := GZ_WRITE })

/-- The actual source's post-copy append tail, including open refusal, ignored
seek failure, the mode write and real reset on the same live handle. -/
theorem openAfterPath_append (h : Heap) (fs : Fs) (i pb : Nat) (s : GzState)
    (ml : ModeLoop) (path : BPtr) (fd : Int32) (name : List UInt8) (copy : Array UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_APPEND) (hmsg : s.msg = .null)
    (hflags : ml.oflag = 0) (hexcl : ml.exclusive = 0)
    (hpath : ZlibF.Spec.Public.CString h path name)
    (hprivate : s.path = .ref (.blk pb) 0)
    (hcopy : h.bytes pb = some copy) (hro : h.ro pb = false) :
    openAfterPath (some (.tab i)) path fd ml fs h =
      .ok (((if (appendIoResult name.toArray fd fs).1 = -1 then none else some (.in_gzstate_x i)),
        (appendIoResult name.toArray fd fs).2), appendIoHeap h i pb s (appendIoResult name.toArray fd fs).1) := by
  have hname := openPath_cstring_public h path name hpath
  have hnb : (appendOpenFlags &&& O_NONBLOCK) = 0 := by decide
  have hce : (appendOpenFlags &&& O_CLOEXEC) = 0 := by decide
  dsimp only [appendOpenFlags] at hnb hce
  by_cases hfd : fd = -1
  · by_cases he : (openFsResult name.toArray appendOpenFlags fs).1 = -1
    · dsimp only [appendOpenFlags] at he
      unfold openAfterPath
      offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname, openFs_eq,
        appendOpenFlags, appendIoResult, appendIoHeap, he, hprivate, hcopy, hro,
        freeB, freeGzState, setS, upd_upd, O_LARGEFILE, GZ_APPEND, GZ_WRITE, GZ_READ, hnd]
    · dsimp only [appendOpenFlags] at he
      unfold openAfterPath
      offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname, openFs_eq,
        appendOpenFlags, appendIoResult, appendIoHeap, he,
        gz_reset, gz_error, resetRec, setS, upd_upd, O_LARGEFILE, GZ_APPEND, GZ_WRITE, GZ_READ, hnd]
  · unfold openAfterPath
    offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname,
      appendOpenFlags, appendIoResult, appendIoHeap, hnb, hce, fsFcntl,
      gz_reset, gz_error, resetRec, setS, upd_upd, O_LARGEFILE, GZ_APPEND, GZ_WRITE, GZ_READ, hnd]

/-- Public append world relation uses the actual end seek, including ignored
errors; it makes no usable-descriptor or successful-seek assumption. -/
theorem appendIoResult_OpenWorld (h : Heap) (fs : Fs) (name : List UInt8) (fd : Int32)
    (transparent : Bool) (start : Int64) :
    ZlibF.Spec.Public.OpenWorld h fs (appendIoResult name.toArray fd fs).2 name
      (if transparent then [97, 84] else [97]) .append
      (if fd = -1 then none else some fd) (appendIoResult name.toArray fd fs).1 start := by
  have hflags : ZlibF.Spec.Public.openFlags (if transparent then [97, 84] else [97]) .append = appendOpenFlags := by
    cases transparent <;> decide
  by_cases hfd : fd = -1
  · by_cases he : (openFsResult name.toArray appendOpenFlags fs).1 = -1
    · refine ⟨(openFsResult name.toArray appendOpenFlags fs).2, ?_, ?_⟩
      · have hp : openFsResult name.toArray appendOpenFlags fs =
            (-1, (openFsResult name.toArray appendOpenFlags fs).2) := Prod.ext he rfl
        have hc := openFs_eq name.toArray appendOpenFlags fs h
        rw [hp] at hc
        simpa [appendIoResult, hfd, he, hflags] using hc
      · simp [appendIoResult, hfd, he]
    · refine ⟨(openFsResult name.toArray appendOpenFlags fs).2, ?_, ?_⟩
      · simpa [appendIoResult, hfd, he, hflags] using openFs_eq name.toArray appendOpenFlags fs h
      · simp only [appendIoResult, hfd, ite_true, he, ite_false]
        exact ⟨_, fsLseek_eq _ _ _ _ _⟩
  · refine ⟨fs, ?_, ?_⟩
    · simp [appendIoResult, hfd]
    · simp only [appendIoResult, hfd, ite_false]
      exact ⟨_, fsLseek_eq _ _ _ _ _⟩

/-- The actual append mode transition and reset establish public OpenState
from primitive initialized fields on the same returned execution heap. -/
theorem appendIoHeap_OpenState (h : Heap) (i pb : Nat) (s : GzState) (result : Int32)
    (name : List UInt8) (direct : Int)
    (hs : h.gzstates i = some s)
    (hprivate : s.path = .ref (.blk pb) 0)
    (hsize : s.size = 0) (hwant : s.want = 8192)
    (hlevel : s.level = Z_DEFAULT_COMPRESSION) (hstrategy : s.strategy = Z_DEFAULT_STRATEGY)
    (hdirect : s.direct.toInt = direct) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hpath : ZlibF.Spec.Public.CString h (.ref (.blk pb) 0) name)
    (hbuf : ZlibF.Spec.Public.MallocBuffer h (.ref (.blk pb) 0) (name.length + 1))
    (hresult : result ≠ -1) :
    ZlibF.Spec.Public.OpenState (appendIoHeap h i pb s result) i
      (resetRec { s with fd := result, mode := GZ_WRITE }) .append (-1) 0 direct result name := by
  rw [appendIoHeap, ite_eq_right (by exact hresult)]
  let final := resetRec { s with fd := result, mode := GZ_WRITE }
  have hshape := shape_setS hs final
  have hpf := openCString_setS h i final (.ref (.blk pb) 0) name hpath
  have hbf := openMallocBuffer_setS h i final (.ref (.blk pb) 0) (name.length + 1) hbuf
  have hfinalPath : final.path = .ref (.blk pb) 0 := by
    simp [final, resetRec, hprivate, GZ_WRITE, GZ_READ]
  have hv : ZlibF.Spec.Public.GzValid (setS h i final) i final := by
    refine ⟨by simp [setS], ?_, Shape.fresh hshape rfl hf, Shape.uniq hshape hu,
      hg, ⟨name, ?_, ?_⟩, Or.inl ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [final, resetRec, GZ_WRITE, GZ_READ]
    · simpa only [hfinalPath] using hpf
    · simpa only [hfinalPath] using hbf
    · simp [final, resetRec, GZ_WRITE, GZ_READ]
    · intro _; simp [final, resetRec, GZ_WRITE, GZ_READ]
    · simp [final, resetRec, hwant, GZ_WRITE, GZ_READ]
    · simp [final, resetRec, hwant, GZ_WRITE, GZ_READ]
    · simp [final, resetRec, hsize, GZ_WRITE, GZ_READ]
    · simp [final, resetRec, GZ_WRITE, GZ_READ]
  refine ⟨hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (change ZlibF.Spec.Public.CString (setS h i final) final.path name
       rw [hfinalPath]
       exact hpf)
    | simp [resetRec, hprivate, hsize, hwant, hlevel, hstrategy,
        hdirect, GZ_WRITE, GZ_READ, Z_DEFAULT_COMPRESSION, Z_DEFAULT_STRATEGY]

/-- Saving the real append mode transition changes only the handle, with the
same actual allocation kinds as the ordinary I/O cleanup/reset expression. -/
theorem appendIoHeap_congr (h : Heap) (i pb : Nat) (s : GzState) (fd : Int32) :
    ZlibF.Spec.Public.Frame (writerIoHeap h i pb s fd) (appendIoHeap h i pb s fd) (fun b => b = i) ∧
    Shape (writerIoHeap h i pb s fd) (appendIoHeap h i pb s fd) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (intro b _ hb; by_cases he : fd = -1 <;> simp [writerIoHeap, appendIoHeap, he, setS, hb])
      | (by_cases he : fd = -1 <;> simp [writerIoHeap, appendIoHeap, he, setS])
  · intro b
    by_cases he : fd = -1 <;> by_cases hb : b = i <;>
      simp [writerIoHeap, appendIoHeap, he, hb, setS]

/-- Both actual append I/O outcomes have exact frame and live-allocation
accounting; the ignored end-seek creates no C heap allocation. -/
theorem appendIoHeap_ledger (h : Heap) (i pb : Nat) (s : GzState) (fd : Int32)
    (copy : Array UInt8) (hu : Uniq h) (hs : h.gzstates i = some s) (hp : h.bytes pb = some copy) :
    ZlibF.Spec.Public.Frame h (appendIoHeap h i pb s fd) (fun b => b = i ∨ fd = -1 ∧ b = pb) ∧
    ZlibF.Spec.Public.LiveChange h (appendIoHeap h i pb s fd)
      (fun _ => False) (fun b => fd = -1 ∧ (b = i ∨ b = pb)) := by
  have hb := writerIoHeap_ledger h i pb s fd copy hu hs hp
  have hc := appendIoHeap_congr h i pb s fd
  constructor
  · obtain ⟨s1, o1, g1, n1, a1, f1⟩ := hb.1
    obtain ⟨s2, o2, g2, n2, a2, f2⟩ := hc.1
    refine ⟨s1.trans s2, o1.trans o2, g1.trans g2, Nat.le_trans n1 n2, Nat.le_trans a1 a2, ?_⟩
    intro b hl hn
    have hbi : b ≠ i := fun he => hn (Or.inl he)
    have hr : ¬ (fd = -1 ∧ (b = i ∨ b = pb)) := by
      rintro ⟨hf, hi | hp⟩
      · exact hn (Or.inl hi)
      · exact hn (Or.inr ⟨hf, hp⟩)
    have hmid : (writerIoHeap h i pb s fd).live b := (hb.2 b).2 (Or.inl ⟨hl, hr⟩)
    obtain ⟨b1, w1, z1, g1, d1, i1, s1, r1⟩ := f1 b hl hn
    obtain ⟨b2, w2, z2, g2, d2, i2, s2, r2⟩ := f2 b hmid hbi
    exact ⟨b2.trans b1, w2.trans w1, z2.trans z1, g2.trans g1, d2.trans d1,
      i2.trans i1, s2.trans s1, r2.trans r1⟩
  · intro b
    exact (Shape.live hc.2 b).trans (hb.2 b)

#print axioms appendIoHeap_OpenState
#print axioms openAfterPath_append
#print axioms appendIoResult_OpenWorld
#print axioms appendIoHeap_ledger
end Zlib.Gzlib.Proofs
