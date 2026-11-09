import ZlibF.Proof.«gzlib.c.open-reader»

/-!
# gzlib.c: ordinary read entry

Internal r/rG entry on short paths, retaining the separate full-domain goal.
All actual allocations, mode writes, filesystem calls and reset share the
returned heap. The old x.next is arbitrary until the real gz_look writes it.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Exact caller-to-result heap after both successful allocations. -/
def readerOpenHeap (h : Heap) (gzipOnly : Bool) (name : List UInt8)
    (result : ReaderIoResult) : Heap :=
  readerFinishedHeap (readerEntryHeap h gzipOnly) h.nextBlk
    (readerEntryRecord h gzipOnly) gzipOnly name result

/-- The actual returned record, including the real initial seek result. -/
def readerOpenState (h : Heap) (gzipOnly : Bool) (result : ReaderIoResult) : GzState :=
  resetRec { readerCheckedRecord (readerEntryRecord h gzipOnly) gzipOnly with
    path := .ref (.blk (h.nextBlk + 1)) 0
    fd := result.fd
    start := result.start }

/-- Fields actually written by initialization and reset, available to the lazy
read-buffer producer. This makes no claim about an unwritten pointer. -/
theorem readerOpenState_fields (h : Heap) (gzipOnly : Bool) (result : ReaderIoResult) :
    let s := readerOpenState h gzipOnly result
    s.mode = GZ_READ ∧ s.size = 0 ∧ s.want = 8192 ∧ s.how = LOOK ∧
    s.eof = 0 ∧ s.junk = -1 ∧ s.x.have = 0 ∧ s.x.pos = 0 ∧ s.strm.avail_in = 0 ∧
    s.skip = 0 ∧ s.err = Z_OK ∧ s.msg = .null ∧
    s.x.next = (openFrontRecord h).x.next := by
  cases gzipOnly <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual read caller-to-result execution, including the real front,
allocation, copied path, OS refusal or saved start and reset. -/
theorem gz_open_reader_allocated_run (h : Heap) (fs : Fs) (path mode : BPtr) (fd : Int32)
    (gzipOnly : Bool) (name : List UInt8) (hf : Fresh h)
    (hp : ZlibF.Spec.Public.CString h path name)
    (hm : ZlibF.Spec.Public.CString h mode (if gzipOnly then [114, 71] else [114]))
    (hlen : name.length ≤ 2147483647)
    (hok : h.allocOk h.nalloc = true) (hok1 : h.allocOk (h.nalloc + 1) = true) :
    gz_open path fd mode fs h =
      .ok (((if (readerIoResult name.toArray fd fs).fd = -1 then none
        else some (.in_gzstate_x h.nextBlk)), (readerIoResult name.toArray fd fs).fs),
        readerOpenHeap h gzipOnly name (readerIoResult name.toArray fd fs)) := by
  obtain ⟨r, off, a, he, _, _, _⟩ := writerCString_view h path name hp
  have hnonnull : path ≠ .null := by simp [he]
  obtain ⟨ml, hdone, hflags, hexcl, hfront⟩ :=
    readerEntry_front h fs path fd mode gzipOnly hnonnull hm hok hf
  have hs : (readerEntryHeap h gzipOnly).gzstates h.nextBlk =
      some (readerEntryRecord h gzipOnly) := by simp [readerEntryHeap, setS]
  have hdir : (readerEntryRecord h gzipOnly).direct = if gzipOnly then -1 else 0 := rfl
  rw [hfront]
  exact openAfterMode_reader_run _ fs h.nextBlk _ path fd ml gzipOnly name hs rfl hdir rfl
    hdone hflags hexcl (readerEntry_fresh h gzipOnly hf)
    (readerEntry_cstring h gzipOnly path name hp) hlen
    (by simpa [readerEntryHeap, setS, openFrontHeap] using hok1)

/-- The very same returned heap satisfies the public read OpenState, including
all real reset fields; arbitrary allocation garbage is admitted. -/
theorem gz_open_reader_allocated_OpenState (h : Heap) (gzipOnly : Bool) (name : List UInt8)
    (result : ReaderIoResult) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64)
    (hr : result.fd ≠ -1) :
    ZlibF.Spec.Public.OpenState (readerOpenHeap h gzipOnly name result) h.nextBlk
      (readerOpenState h gzipOnly result) .read (-1) 0 (if gzipOnly then -1 else 0) result.fd name := by
  have hs : (readerEntryHeap h gzipOnly).gzstates h.nextBlk =
      some (readerEntryRecord h gzipOnly) := by simp [readerEntryHeap, setS]
  have hglobal : ZlibF.Spec.Public.LibraryGlobals (readerEntryHeap h gzipOnly) := hg
  exact openAfterMode_reader_OpenState _ h.nextBlk _ gzipOnly name result hs rfl rfl
    rfl rfl rfl rfl (readerEntry_fresh h gzipOnly hf) (readerEntry_uniq h gzipOnly hf hu)
    hglobal hn hlen hr

/-- Caller objects are preserved through the complete successful-allocation
execution, even when the subsequent I/O call refuses to open the file. -/
theorem readerOpen_frame (h : Heap) (gzipOnly : Bool) (name : List UInt8) (result : ReaderIoResult)
    (hf : Fresh h) (hu : Uniq h) :
    ZlibF.Spec.Public.Frame h (readerOpenHeap h gzipOnly name result) (fun _ => False) := by
  have hp := openFrontHeap_ledger h (readerEntryRecord h gzipOnly) (Fresh.slotUsed_next hf)
  have hs : (readerEntryHeap h gzipOnly).gzstates h.nextBlk =
      some (readerEntryRecord h gzipOnly) := by simp [readerEntryHeap, setS]
  have ht := readerFinished_ledger _ h.nextBlk _ gzipOnly name result
    (readerEntry_fresh h gzipOnly hf) (readerEntry_uniq h gzipOnly hf hu) hs
  obtain ⟨s1, o1, g1, n1, a1, f1⟩ := hp.1
  obtain ⟨s2, o2, g2, n2, a2, f2⟩ := ht.1
  refine ⟨s1.trans s2, o1.trans o2, g1.trans g2, Nat.le_trans n1 n2,
    Nat.le_trans a1 a2, ?_⟩
  intro b hl _
  have hbi : b ≠ h.nextBlk := fun he => hf h.nextBlk (Nat.le_refl _) (he ▸ hl)
  have hentry : (readerEntryHeap h gzipOnly).live b := (hp.2 b).2 (Or.inl ⟨hl, by simp⟩)
  obtain ⟨b1, w1, z1, g1, d1, i1, s1, r1⟩ := f1 b hl (by simp)
  obtain ⟨b2, w2, z2, g2, d2, i2, s2, r2⟩ := f2 b hentry hbi
  exact ⟨b2.trans b1, w2.trans w1, z2.trans z1, g2.trans g1, d2.trans d1,
    i2.trans i1, s2.trans s1, r2.trans r1⟩

/-- Exact caller-to-result ledger. I/O success adds just the handle and its
private path; I/O refusal leaves no new live allocation. -/
theorem readerOpen_ledger (h : Heap) (gzipOnly : Bool) (name : List UInt8) (result : ReaderIoResult)
    (hf : Fresh h) (hu : Uniq h) :
    ZlibF.Spec.Public.LiveChange h (readerOpenHeap h gzipOnly name result)
      (fun b => result.fd ≠ -1 ∧ (b = h.nextBlk ∨ b = h.nextBlk + 1)) (fun _ => False) := by
  have hp := (openFrontHeap_ledger h (readerEntryRecord h gzipOnly) (Fresh.slotUsed_next hf)).2
  have hs : (readerEntryHeap h gzipOnly).gzstates h.nextBlk =
      some (readerEntryRecord h gzipOnly) := by simp [readerEntryHeap, setS]
  have ht := (readerFinished_ledger _ h.nextBlk _ gzipOnly name result
    (readerEntry_fresh h gzipOnly hf) (readerEntry_uniq h gzipOnly hf hu) hs).2
  have hn : ¬ h.live h.nextBlk := hf h.nextBlk (Nat.le_refl _)
  intro b
  unfold readerOpenHeap
  rw [ht b]
  change ZlibF.Spec.Public.LiveChange h (readerEntryHeap h gzipOnly)
    (fun b => b = h.nextBlk) (fun _ => False) at hp
  rw [hp b]
  change ((h.live b ∧ ¬ False ∨ b = h.nextBlk) ∧ ¬ (result.fd = -1 ∧ b = h.nextBlk) ∨
      result.fd ≠ -1 ∧ b = h.nextBlk + 1) ↔
    (h.live b ∧ ¬ False) ∨ result.fd ≠ -1 ∧ (b = h.nextBlk ∨ b = h.nextBlk + 1)
  by_cases hr : result.fd = -1
  · by_cases hb : b = h.nextBlk
    · subst b; simp [hr, hn]
    · simp [hr, hb]
  · simp [hr, or_assoc]

/-- With size zero, ownership is exactly the fresh handle and copied path.
Old inactive buffers and pointer garbage do not become owned objects. -/
theorem readerOpen_owned (h : Heap) (gzipOnly : Bool) (name : List UInt8)
    (result : ReaderIoResult) (b : Nat) :
    ZlibF.Spec.Public.GzOwned (readerOpenHeap h gzipOnly name result) h.nextBlk
      (readerOpenState h gzipOnly result) b ↔ b = h.nextBlk ∨ b = h.nextBlk + 1 := by
  cases gzipOnly <;>
    simp [ZlibF.Spec.Public.GzOwned, readerOpenState, readerEntryRecord, readerCheckedRecord,
      openFrontRecord, resetRec, GZ_READ, eq_comm]

/-- The true second-allocation refusal frees the newly initialized handle.
This branch does not need the short-path formatter bound. -/
theorem gz_open_reader_path_failure (h : Heap) (fs : Fs) (path mode : BPtr) (fd : Int32)
    (gzipOnly : Bool) (name : List UInt8) (hf : Fresh h)
    (hp : ZlibF.Spec.Public.CString h path name)
    (hm : ZlibF.Spec.Public.CString h mode (if gzipOnly then [114, 71] else [114]))
    (hok : h.allocOk h.nalloc = true) (hfail : h.allocOk (h.nalloc + 1) = false) :
    gz_open path fd mode fs h =
      .ok ((none, fs), { openReleased h with nalloc := h.nalloc + 2 }) := by
  obtain ⟨r, off, a, he, _, _, _⟩ := writerCString_view h path name hp
  have hnonnull : path ≠ .null := by simp [he]
  obtain ⟨ml, hdone, _, _, hfront⟩ :=
    readerEntry_front h fs path fd mode gzipOnly hnonnull hm hok hf
  have hs : (readerEntryHeap h gzipOnly).gzstates h.nextBlk =
      some (readerEntryRecord h gzipOnly) := by simp [readerEntryHeap, setS]
  rw [hfront, openAfterMode_reader_guard _ fs h.nextBlk _ path fd ml gzipOnly hs rfl rfl hdone]
  have hstr := openPath_strlen_public
    (readerCheckedHeap (readerEntryHeap h gzipOnly) h.nextBlk (readerEntryRecord h gzipOnly) gzipOnly) path name
    (readerChecked_cstring (readerEntryHeap h gzipOnly) h.nextBlk (readerEntryRecord h gzipOnly) gzipOnly path name
      (readerEntry_cstring h gzipOnly path name hp))
  have hsc := readerChecked_state _ h.nextBlk _ gzipOnly hs
  have hfailure : (readerCheckedHeap (readerEntryHeap h gzipOnly) h.nextBlk
      (readerEntryRecord h gzipOnly) gzipOnly).allocOk
      (readerCheckedHeap (readerEntryHeap h gzipOnly) h.nextBlk
        (readerEntryRecord h gzipOnly) gzipOnly).nalloc = false := by
    cases gzipOnly <;> exact hfail
  unfold openCopyPath
  offsetsimp [hsc, hstr, hfailure, allocB, freeGzState, setS, upd_upd]
  cases gzipOnly <;>
    simp [readerCheckedHeap, readerEntryHeap, openFrontHeap, openReleased, setS, upd_upd]

/-- Real read I/O refusal always supplies the public zero start value. -/
theorem readerIoResult_failure_start (name : Array UInt8) (fd : Int32) (fs : Fs)
    (hr : (readerIoResult name fd fs).fd = -1) :
    (readerIoResult name fd fs).start = 0 := by
  by_cases hfd : fd = -1
  · by_cases hopen : (openFsResult name 0 fs).1 = -1
    · simp [readerIoResult, hfd, hopen]
    · simp [readerIoResult, hfd, hopen] at hr
  · simp [readerIoResult, hfd] at hr

/-- Ordinary `r`/`rG` entry on the internal short-path branch, with arbitrary
caller path storage, file world, supplied descriptor, allocation refusals, and
all admitted garbage values. This theorem retains the actual execution and
public state/world/frame/ledger conclusions; it does not replace `Goal.gzopen`. -/
theorem gz_open_reader_short (h : Heap) (fs : Fs) (path mode : BPtr) (fd : Int32)
    (gzipOnly : Bool) (name : List UInt8) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hp : ZlibF.Spec.Public.CString h path name)
    (hm : ZlibF.Spec.Public.CString h mode (if gzipOnly then [114, 71] else [114]))
    (hlen : name.length ≤ 2147483647) :
    ∃ file fs' after, gz_open path fd mode fs h = .ok ((file, fs'), after) ∧
      ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
      (match file with
       | none => ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
           (ZlibF.Spec.Public.AllocationFailed h after ∨
             ZlibF.Spec.Public.OpenWorld h fs fs' name
               (if gzipOnly then [114, 71] else [114]) .read
               (if fd = -1 then none else some fd) (-1) 0)
       | some (.in_gzstate_x i) => ∃ s,
           ZlibF.Spec.Public.OpenState after i s .read (-1) 0
             (if gzipOnly then -1 else 0) s.fd name ∧
           ZlibF.Spec.Public.OpenWorld h fs fs' name
             (if gzipOnly then [114, 71] else [114]) .read
             (if fd = -1 then none else some fd) s.fd s.start ∧ s.fd ≠ -1 ∧
           ZlibF.Spec.Public.LiveChange h after (ZlibF.Spec.Public.GzOwned after i s) (fun _ => False)) := by
  obtain ⟨pr, po, pa, hpp, _, _, _⟩ := writerCString_view h path name hp
  obtain ⟨mr, mo, ma, hmp, _, _, _⟩ := writerCString_view h mode _ hm
  have hpn : path ≠ .null := by simp [hpp]
  have hmn : mode ≠ .null := by simp [hmp]
  by_cases h0 : h.allocOk h.nalloc = true
  · by_cases h1 : h.allocOk (h.nalloc + 1) = true
    · let io := readerIoResult name.toArray fd fs
      have hrun : gz_open path fd mode fs h =
          .ok (((if io.fd = -1 then none else some (.in_gzstate_x h.nextBlk)), io.fs),
            readerOpenHeap h gzipOnly name io) :=
        gz_open_reader_allocated_run h fs path mode fd gzipOnly name hf hp hm hlen h0 h1
      by_cases he : io.fd = -1
      · refine ⟨none, io.fs, readerOpenHeap h gzipOnly name io, ?_,
          readerOpen_frame h gzipOnly name io hf hu, ?_, Or.inr ?_⟩
        · simpa only [he, ite_true] using hrun
        · simpa [he] using readerOpen_ledger h gzipOnly name io hf hu
        · have hw := readerIoResult_OpenWorld h fs name fd gzipOnly
          change ZlibF.Spec.Public.OpenWorld h fs io.fs name
            (if gzipOnly then [114, 71] else [114]) .read
            (if fd = -1 then none else some fd) io.fd io.start at hw
          have hz : io.start = 0 := readerIoResult_failure_start name.toArray fd fs he
          simpa only [he, hz] using hw
      · let out := readerOpenState h gzipOnly io
        have hfd : out.fd = io.fd := by
          cases gzipOnly <;> rfl
        refine ⟨some (.in_gzstate_x h.nextBlk), io.fs, readerOpenHeap h gzipOnly name io,
          ?_, readerOpen_frame h gzipOnly name io hf hu, out, ?_, ?_, ?_, ?_⟩
        · simpa only [he, ite_false] using hrun
        · rw [hfd]
          exact gz_open_reader_allocated_OpenState h gzipOnly name io hf hu hg hp.2.1 hp.2.2 he
        · have hstart : out.start = io.start := by
            cases gzipOnly <;> rfl
          rw [hfd, hstart]
          exact readerIoResult_OpenWorld h fs name fd gzipOnly
        · simpa only [hfd] using he
        · intro b
          change (readerOpenHeap h gzipOnly name io).live b ↔
            ((h.live b ∧ ¬ False) ∨ ZlibF.Spec.Public.GzOwned
              (readerOpenHeap h gzipOnly name io) h.nextBlk (readerOpenState h gzipOnly io) b)
          rw [readerOpen_owned]
          simpa [he] using readerOpen_ledger h gzipOnly name io hf hu b
    · have he : h.allocOk (h.nalloc + 1) = false := by simpa using h1
      obtain ⟨hframe, hlive, halloc⟩ := writerPathFailure_checks h hf he
      exact ⟨none, fs, { openReleased h with nalloc := h.nalloc + 2 },
        gz_open_reader_path_failure h fs path mode fd gzipOnly name hf hp hm h0 he,
        hframe, hlive, Or.inl halloc⟩
  · have he : h.allocOk h.nalloc = false := by simpa using h0
    obtain ⟨hframe, hlive, halloc⟩ := writerFirstFailure_checks h he
    exact ⟨none, fs, { h with nalloc := h.nalloc + 1 },
      gz_open_alloc_failure h fs path fd mode hpn hmn he, hframe, hlive, Or.inl halloc⟩

/-- `gzFile gzopen(const char *path, const char *mode)`: the ordinary short-path
entry also produces an actual public-history witness on its very same returned
heap. This gives later gzip proofs a real initialization producer. -/
theorem gzopen_reader_short_reachable (h : Heap) (fs : Fs) (path mode : BPtr)
    (gzipOnly : Bool) (name : List UInt8) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hfs : ZlibF.Spec.Public.FileSystem fs)
    (hp : ZlibF.Spec.Public.CString h path name)
    (hm : ZlibF.Spec.Public.CString h mode (if gzipOnly then [114, 71] else [114]))
    (hlen : name.length ≤ 2147483647) :
    ∃ file fs' after, gzopen path mode fs h = .ok ((file, fs'), after) ∧
      ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
      (match file with
       | none => ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
           (ZlibF.Spec.Public.AllocationFailed h after ∨
             ZlibF.Spec.Public.OpenWorld h fs fs' name
               (if gzipOnly then [114, 71] else [114]) .read
               none (-1) 0)
       | some (.in_gzstate_x i) => ∃ s, ZlibF.Spec.Public.GzReachable after fs' i ∧
           ZlibF.Spec.Public.OpenState after i s .read (-1) 0
             (if gzipOnly then -1 else 0) s.fd name ∧
           ZlibF.Spec.Public.OpenWorld h fs fs' name
             (if gzipOnly then [114, 71] else [114]) .read
             none s.fd s.start ∧ s.fd ≠ -1 ∧
           ZlibF.Spec.Public.LiveChange h after (ZlibF.Spec.Public.GzOwned after i s) (fun _ => False)) := by
  obtain ⟨file, fs', after, hrun, hframe, hpost⟩ :=
    gz_open_reader_short h fs path mode (-1) gzipOnly name hf hu hg hp hm hlen
  refine ⟨file, fs', after, hrun, hframe, ?_⟩
  cases file with
  | none => simpa using hpost
  | some ref =>
    cases ref with
    | in_gzstate_x i =>
      obtain ⟨s, hstate, hworld, hfd, hledger⟩ := hpost
      exact ⟨s, ZlibF.Spec.Public.GzReachable.open hf hu hg hfs hp hm hrun,
        hstate, by simpa using hworld, hfd, hledger⟩

#print axioms readerOpenState_fields
#print axioms gz_open_reader_allocated_run
#print axioms gz_open_reader_allocated_OpenState
#print axioms readerOpen_frame
#print axioms readerOpen_ledger
#print axioms readerOpen_owned
#print axioms gz_open_reader_path_failure
#print axioms readerIoResult_failure_start
#print axioms gz_open_reader_short
#print axioms gzopen_reader_short_reachable
end Zlib.Gzlib.Proofs
