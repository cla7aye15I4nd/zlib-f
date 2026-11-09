import ZlibF.Proof.«gzlib.c.open-writer»

/-!
# gzlib.c: ordinary writer entry

This internal branch uses the actual public `w`/`wT` mode strings and an input
path no longer than INT_MAX. It retains the separate full-domain public goal.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Physical bytes of any public caller string, including its terminating NUL. -/
theorem writerCString_view (h : Heap) (path : BPtr) (xs : List UInt8)
    (hc : ZlibF.Spec.Public.CString h path xs) :
    ∃ r off a, path = .ref r off ∧ Space.get h r = some a ∧ off + xs.length < a.size ∧
      ∀ k, k ≤ xs.length → a[off + k]? = (xs ++ [0])[k]? := by
  rcases hc.1 with ⟨_, hz, _⟩ | ⟨r, off, a, hp, hg, hbound, hbytes⟩
  · simp at hz
  · refine ⟨r, off, a, hp, hg, by omega, ?_⟩
    intro k hk
    have he := congrArg (fun ys : List UInt8 => ys[k]?) hbytes
    simpa [List.getElem?_take, show k < xs.length + 1 by omega,
      List.getElem?_drop] using he.symm

/-- The ordinary writer record established by the actual allocation and mode loop. -/
def writerEntryRecord (h : Heap) (transparent : Bool) : GzState :=
  { openFrontRecord h with mode := GZ_WRITE, direct := if transparent then 1 else 0 }

/-- Exact heap after the first successful allocation, initialization, and parsing. -/
def writerEntryHeap (h : Heap) (transparent : Bool) : Heap :=
  setS (openFrontHeap h) h.nextBlk (writerEntryRecord h transparent)

/-- The actual public `w` or `wT` bytes reach the real source continuation.
No parsed-mode result or library callee contract is assumed. -/
theorem writerEntry_front (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32)
    (mode : BPtr) (transparent : Bool) (hp : path ≠ .null)
    (hc : ZlibF.Spec.Public.CString h mode (if transparent then [119, 84] else [119]))
    (hok : h.allocOk h.nalloc = true) (hf : Fresh h) :
    ∃ ml : ModeLoop, ml.done = false ∧ ml.oflag = 0 ∧ ml.exclusive = 0 ∧
      gz_open path fd mode fs h = openAfterMode (some (.tab h.nextBlk)) path fd ml fs
        (writerEntryHeap h transparent) := by
  cases transparent with
  | false =>
    obtain ⟨r, off, a, rfl, hg, hb, hchar⟩ := writerCString_view h mode [119] hc
    have hend : off + 1 < a.size := by simpa using hb
    have hoff : off < a.size := by omega
    have hw : a[off] = 119 := by
      simpa [Array.getElem?_eq_getElem hoff] using hchar 0 (by simp)
    have hz : a[off + 1] = 0 := by
      simpa [Array.getElem?_eq_getElem hend] using hchar 1 (by simp)
    refine ⟨{ mode := .ref r (off + 1), oflag := 0, exclusive := 0, done := false },
      rfl, rfl, rfl, ?_⟩
    simpa [writerEntryHeap, writerEntryRecord, openFrontRecord] using
      gz_open_write_front h fs path fd r off a hp hg hend hw hz hok (Fresh.slotUsed_next hf)
  | true =>
    obtain ⟨r, off, a, rfl, hg, hb, hchar⟩ := writerCString_view h mode [119, 84] hc
    have hend : off + 2 < a.size := by simpa using hb
    have hoff : off < a.size := by omega
    have hoff1 : off + 1 < a.size := by omega
    have hw : a[off] = 119 := by
      simpa [Array.getElem?_eq_getElem hoff] using hchar 0 (by simp)
    have ht : a[off + 1] = 84 := by
      simpa [Array.getElem?_eq_getElem hoff1] using hchar 1 (by simp)
    have hz : a[off + 2] = 0 := by
      simpa [Array.getElem?_eq_getElem hend] using hchar 2 (by simp)
    refine ⟨{ mode := .ref r (off + 2), oflag := 0, exclusive := 0, done := false },
      rfl, rfl, rfl, ?_⟩
    simpa [writerEntryHeap, writerEntryRecord] using
      gz_open_write_direct_front h fs path fd r off a hp hg hend hw ht hz hok
        (Fresh.slotUsed_next hf)

/-- The first actual allocation and mode writes establish a fresh heap. -/
theorem writerEntry_fresh (h : Heap) (transparent : Bool) (hf : Fresh h) :
    Fresh (writerEntryHeap h transparent) := by
  have hl := (openFrontHeap_ledger h (writerEntryRecord h transparent) (Fresh.slotUsed_next hf)).2
  intro b hb hLive
  have hb' : h.nextBlk + 1 ≤ b := hb
  rcases (hl b).1 hLive with ⟨ho, _⟩ | hn
  · exact hf b (by omega) ho
  · omega

/-- The fresh handle occupies exactly one object table. -/
theorem writerEntry_uniq (h : Heap) (transparent : Bool) (hf : Fresh h) (hu : Uniq h) :
    Uniq (writerEntryHeap h transparent) := by
  have hn := Heap.not_live.mp (hf h.nextBlk (Nat.le_refl _))
  intro b
  by_cases hb : b = h.nextBlk
  · subst b
    simp [writerEntryHeap, openFrontHeap, setS, hn.1, hn.2.1, hn.2.2.1,
      hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1]
  · simpa [writerEntryHeap, openFrontHeap, setS, hb] using hu b

/-- The real first allocation and parsing do not change caller byte arrays. -/
theorem writerEntry_cstring (h : Heap) (transparent : Bool) (path : BPtr) (name : List UInt8)
    (hc : ZlibF.Spec.Public.CString h path name) :
    ZlibF.Spec.Public.CString (writerEntryHeap h transparent) path name := by
  rcases hc with ⟨hb, hn, hl⟩
  refine ⟨?_, hn, hl⟩
  rcases hb with hn | ⟨r, off, a, hp, hg, hbound, he⟩
  · exact Or.inl hn
  · refine Or.inr ⟨r, off, a, hp, ?_, hbound, he⟩
    rw [writerEntryHeap, modeBytes_setS, modeBytes_openFrontHeap]
    exact hg

/-- Exact caller-to-result heap when both actual allocations succeed. -/
def writerOpenHeap (h : Heap) (transparent : Bool) (name : List UInt8) (result : Int32) : Heap :=
  writerFinishedHeap (writerEntryHeap h transparent) h.nextBlk
    (writerEntryRecord h transparent) name result

/-- Exact returned record after real successful I/O and reset. -/
def writerOpenState (h : Heap) (transparent : Bool) (result : Int32) : GzState :=
  resetRec { writerEntryRecord h transparent with
    path := .ref (.blk (h.nextBlk + 1)) 0
    fd := result }

/-- The actual caller-to-result execution, including initialization, mode scan,
both successful allocations, formatting, I/O refusal or successful reset. -/
theorem gz_open_writer_allocated_run (h : Heap) (fs : Fs) (path mode : BPtr) (fd : Int32)
    (transparent : Bool) (name : List UInt8) (hf : Fresh h)
    (hp : ZlibF.Spec.Public.CString h path name)
    (hm : ZlibF.Spec.Public.CString h mode (if transparent then [119, 84] else [119]))
    (hlen : name.length ≤ 2147483647)
    (hok : h.allocOk h.nalloc = true) (hok1 : h.allocOk (h.nalloc + 1) = true) :
    gz_open path fd mode fs h =
      .ok (((if (writerIoResult name.toArray fd fs).1 = -1 then none
        else some (.in_gzstate_x h.nextBlk)), (writerIoResult name.toArray fd fs).2),
        writerOpenHeap h transparent name (writerIoResult name.toArray fd fs).1) := by
  obtain ⟨r, off, a, he, _, _, _⟩ := writerCString_view h path name hp
  have hnonnull : path ≠ .null := by simp [he]
  obtain ⟨ml, hdone, hflags, hexcl, hfront⟩ :=
    writerEntry_front h fs path fd mode transparent hnonnull hm hok hf
  have hs : (writerEntryHeap h transparent).gzstates h.nextBlk =
      some (writerEntryRecord h transparent) := by simp [writerEntryHeap, setS]
  have hdir : (writerEntryRecord h transparent).direct ≠ -1 := by
    cases transparent
    · change (0 : Int32) ≠ -1; decide
    · change (1 : Int32) ≠ -1; decide
  rw [hfront]
  exact openAfterMode_writer_run _ fs h.nextBlk _ path fd ml name hs rfl hdir rfl
    hdone hflags hexcl (writerEntry_fresh h transparent hf)
    (writerEntry_cstring h transparent path name hp) hlen
    (by simpa [writerEntryHeap, setS, openFrontHeap] using hok1)

/-- Successful real entry establishes `OpenState` on the same execution heap,
for every allocation garbage value admitted by the original runtime. -/
theorem gz_open_writer_allocated_OpenState (h : Heap) (fs : Fs) (fd : Int32)
    (transparent : Bool) (name : List UInt8) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64)
    (hr : (writerIoResult name.toArray fd fs).1 ≠ -1) :
    ZlibF.Spec.Public.OpenState
      (writerOpenHeap h transparent name (writerIoResult name.toArray fd fs).1) h.nextBlk
      (writerOpenState h transparent (writerIoResult name.toArray fd fs).1)
      .write (-1) 0 (if transparent then 1 else 0) (writerIoResult name.toArray fd fs).1 name := by
  have hs : (writerEntryHeap h transparent).gzstates h.nextBlk =
      some (writerEntryRecord h transparent) := by simp [writerEntryHeap, setS]
  have hglobal : ZlibF.Spec.Public.LibraryGlobals (writerEntryHeap h transparent) := hg
  have hd : (writerEntryRecord h transparent).direct.toInt =
      (if transparent then 1 else 0) := by cases transparent <;> rfl
  exact openAfterMode_writer_OpenState _ fs h.nextBlk _ fd name _ hs rfl rfl rfl rfl rfl hd
    (writerEntry_fresh h transparent hf) (writerEntry_uniq h transparent hf hu) hglobal hn hlen hr

/-- Caller objects are preserved through the complete successful-allocation
execution, even when the subsequent I/O call refuses to open the file. -/
theorem writerOpen_frame (h : Heap) (transparent : Bool) (name : List UInt8) (result : Int32)
    (hf : Fresh h) (hu : Uniq h) :
    ZlibF.Spec.Public.Frame h (writerOpenHeap h transparent name result) (fun _ => False) := by
  have hp := openFrontHeap_ledger h (writerEntryRecord h transparent) (Fresh.slotUsed_next hf)
  have hs : (writerEntryHeap h transparent).gzstates h.nextBlk =
      some (writerEntryRecord h transparent) := by simp [writerEntryHeap, setS]
  have ht := writerFinished_ledger _ h.nextBlk _ name result
    (writerEntry_fresh h transparent hf) (writerEntry_uniq h transparent hf hu) hs
  obtain ⟨s1, o1, g1, n1, a1, f1⟩ := hp.1
  obtain ⟨s2, o2, g2, n2, a2, f2⟩ := ht.1
  refine ⟨s1.trans s2, o1.trans o2, g1.trans g2, Nat.le_trans n1 n2,
    Nat.le_trans a1 a2, ?_⟩
  intro b hl _
  have hbi : b ≠ h.nextBlk := fun he => hf h.nextBlk (Nat.le_refl _) (he ▸ hl)
  have hentry : (writerEntryHeap h transparent).live b := (hp.2 b).2 (Or.inl ⟨hl, by simp⟩)
  obtain ⟨b1, w1, z1, g1, d1, i1, s1, r1⟩ := f1 b hl (by simp)
  obtain ⟨b2, w2, z2, g2, d2, i2, s2, r2⟩ := f2 b hentry hbi
  exact ⟨b2.trans b1, w2.trans w1, z2.trans z1, g2.trans g1, d2.trans d1,
    i2.trans i1, s2.trans s1, r2.trans r1⟩

/-- Exact caller-to-result ledger. I/O success adds just the handle and its
private path; I/O refusal leaves no new live allocation. -/
theorem writerOpen_ledger (h : Heap) (transparent : Bool) (name : List UInt8) (result : Int32)
    (hf : Fresh h) (hu : Uniq h) :
    ZlibF.Spec.Public.LiveChange h (writerOpenHeap h transparent name result)
      (fun b => result ≠ -1 ∧ (b = h.nextBlk ∨ b = h.nextBlk + 1)) (fun _ => False) := by
  have hp := (openFrontHeap_ledger h (writerEntryRecord h transparent) (Fresh.slotUsed_next hf)).2
  have hs : (writerEntryHeap h transparent).gzstates h.nextBlk =
      some (writerEntryRecord h transparent) := by simp [writerEntryHeap, setS]
  have ht := (writerFinished_ledger _ h.nextBlk _ name result
    (writerEntry_fresh h transparent hf) (writerEntry_uniq h transparent hf hu) hs).2
  have hn : ¬ h.live h.nextBlk := hf h.nextBlk (Nat.le_refl _)
  intro b
  unfold writerOpenHeap
  rw [ht b]
  change ZlibF.Spec.Public.LiveChange h (writerEntryHeap h transparent)
    (fun b => b = h.nextBlk) (fun _ => False) at hp
  rw [hp b]
  change ((h.live b ∧ ¬ False ∨ b = h.nextBlk) ∧ ¬ (result = -1 ∧ b = h.nextBlk) ∨
      result ≠ -1 ∧ b = h.nextBlk + 1) ↔
    (h.live b ∧ ¬ False) ∨ result ≠ -1 ∧ (b = h.nextBlk ∨ b = h.nextBlk + 1)
  by_cases hr : result = -1
  · by_cases hb : b = h.nextBlk
    · subst b; simp [hr, hn]
    · simp [hr, hb]
  · simp [hr, or_assoc]

/-- On the actual reset record the owned identities are exactly the two new
allocations. Inactive buffers and arbitrary old pointers are not counted. -/
theorem writerOpen_owned (h : Heap) (transparent : Bool) (name : List UInt8)
    (result : Int32) (b : Nat) :
    ZlibF.Spec.Public.GzOwned (writerOpenHeap h transparent name result) h.nextBlk
      (writerOpenState h transparent result) b ↔ b = h.nextBlk ∨ b = h.nextBlk + 1 := by
  cases transparent <;>
    simp [ZlibF.Spec.Public.GzOwned, writerOpenState, writerEntryRecord, openFrontRecord,
      resetRec, GZ_WRITE, GZ_READ, eq_comm]

/-- If the actual second allocation refuses, the whole public-mode entry
releases its newly created handle. This branch needs no INT_MAX path bound. -/
theorem gz_open_writer_path_failure (h : Heap) (fs : Fs) (path mode : BPtr) (fd : Int32)
    (transparent : Bool) (name : List UInt8) (hf : Fresh h)
    (hp : ZlibF.Spec.Public.CString h path name)
    (hm : ZlibF.Spec.Public.CString h mode (if transparent then [119, 84] else [119]))
    (hok : h.allocOk h.nalloc = true) (hfail : h.allocOk (h.nalloc + 1) = false) :
    gz_open path fd mode fs h =
      .ok ((none, fs), { openReleased h with nalloc := h.nalloc + 2 }) := by
  obtain ⟨r, off, a, he, _, _, _⟩ := writerCString_view h path name hp
  have hnonnull : path ≠ .null := by simp [he]
  obtain ⟨ml, hdone, _, _, hfront⟩ :=
    writerEntry_front h fs path fd mode transparent hnonnull hm hok hf
  have hs : (writerEntryHeap h transparent).gzstates h.nextBlk =
      some (writerEntryRecord h transparent) := by simp [writerEntryHeap, setS]
  have hd : (writerEntryRecord h transparent).direct ≠ -1 := by
    cases transparent
    · change (0 : Int32) ≠ -1; decide
    · change (1 : Int32) ≠ -1; decide
  have hstr := openPath_strlen_public _ path name (writerEntry_cstring h transparent path name hp)
  have hfailure : (writerEntryHeap h transparent).allocOk
      (writerEntryHeap h transparent).nalloc = false := hfail
  rw [hfront]
  have hmode : (writerEntryRecord h transparent).mode = GZ_WRITE := rfl
  unfold openAfterMode
  offsetsimp [hdone, hs, hd, hmode, hstr, hfailure, allocB, freeGzState,
    setS, upd_upd, GZ_WRITE, GZ_READ, GZ_NONE]
  simp [writerEntryHeap, openFrontHeap, openReleased, setS, upd_upd]

/-- The second-allocation refusal preserves all original objects and leaves no
new live object. The explicit false oracle is an actual allocation-error cause. -/
theorem writerPathFailure_checks (h : Heap) (hf : Fresh h)
    (hfail : h.allocOk (h.nalloc + 1) = false) :
    ZlibF.Spec.Public.Frame h { openReleased h with nalloc := h.nalloc + 2 } (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h { openReleased h with nalloc := h.nalloc + 2 }
      (fun _ => False) (fun _ => False) ∧
    ZlibF.Spec.Public.AllocationFailed h { openReleased h with nalloc := h.nalloc + 2 } := by
  obtain ⟨hframe, hlive⟩ := openReleased_frame h (Fresh.slotUsed_next hf)
  obtain ⟨hs, ho, hg, hn, _, hp⟩ := hframe
  refine ⟨⟨hs, ho, hg, hn, by simp, hp⟩, hlive, ?_⟩
  exact ⟨h.nalloc + 1, by omega, by change h.nalloc + 1 < h.nalloc + 2; omega, hfail⟩

/-- The first-allocation refusal likewise retains the entire original heap. -/
theorem writerFirstFailure_checks (h : Heap) (hfail : h.allocOk h.nalloc = false) :
    ZlibF.Spec.Public.Frame h { h with nalloc := h.nalloc + 1 } (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h { h with nalloc := h.nalloc + 1 }
      (fun _ => False) (fun _ => False) ∧
    ZlibF.Spec.Public.AllocationFailed h { h with nalloc := h.nalloc + 1 } := by
  refine ⟨⟨rfl, rfl, rfl, Nat.le_refl _, by simp, ?_⟩, ?_, ?_⟩
  · intro b _ _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b; simp [Heap.live]
  · exact ⟨h.nalloc, Nat.le_refl _, by change h.nalloc < h.nalloc + 1; omega, hfail⟩

/-- Ordinary `w`/`wT` entry on the internal short-path branch, with arbitrary
caller path storage, file world, supplied descriptor, allocation refusals, and
all admitted garbage values. This theorem retains the actual execution and
public state/world/frame/ledger conclusions; it does not replace `Goal.gzopen`. -/
theorem gz_open_writer_short (h : Heap) (fs : Fs) (path mode : BPtr) (fd : Int32)
    (transparent : Bool) (name : List UInt8) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hp : ZlibF.Spec.Public.CString h path name)
    (hm : ZlibF.Spec.Public.CString h mode (if transparent then [119, 84] else [119]))
    (hlen : name.length ≤ 2147483647) :
    ∃ file fs' after, gz_open path fd mode fs h = .ok ((file, fs'), after) ∧
      ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
      (match file with
       | none => ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
           (ZlibF.Spec.Public.AllocationFailed h after ∨
             ZlibF.Spec.Public.OpenWorld h fs fs' name
               (if transparent then [119, 84] else [119]) .write
               (if fd = -1 then none else some fd) (-1) 0)
       | some (.in_gzstate_x i) => ∃ s,
           ZlibF.Spec.Public.OpenState after i s .write (-1) 0
             (if transparent then 1 else 0) s.fd name ∧
           ZlibF.Spec.Public.OpenWorld h fs fs' name
             (if transparent then [119, 84] else [119]) .write
             (if fd = -1 then none else some fd) s.fd s.start ∧ s.fd ≠ -1 ∧
           ZlibF.Spec.Public.LiveChange h after (ZlibF.Spec.Public.GzOwned after i s) (fun _ => False)) := by
  obtain ⟨pr, po, pa, hpp, _, _, _⟩ := writerCString_view h path name hp
  obtain ⟨mr, mo, ma, hmp, _, _, _⟩ := writerCString_view h mode _ hm
  have hpn : path ≠ .null := by simp [hpp]
  have hmn : mode ≠ .null := by simp [hmp]
  by_cases h0 : h.allocOk h.nalloc = true
  · by_cases h1 : h.allocOk (h.nalloc + 1) = true
    · let io := writerIoResult name.toArray fd fs
      have hrun : gz_open path fd mode fs h =
          .ok (((if io.1 = -1 then none else some (.in_gzstate_x h.nextBlk)), io.2),
            writerOpenHeap h transparent name io.1) :=
        gz_open_writer_allocated_run h fs path mode fd transparent name hf hp hm hlen h0 h1
      by_cases he : io.1 = -1
      · refine ⟨none, io.2, writerOpenHeap h transparent name io.1, ?_,
          writerOpen_frame h transparent name io.1 hf hu, ?_, Or.inr ?_⟩
        · simpa only [he, ite_true] using hrun
        · simpa [he] using writerOpen_ledger h transparent name io.1 hf hu
        · have hw := writerIoResult_OpenWorld h fs name fd transparent 0
          change ZlibF.Spec.Public.OpenWorld h fs io.2 name
            (if transparent then [119, 84] else [119]) .write
            (if fd = -1 then none else some fd) io.1 0 at hw
          simpa only [he] using hw
      · let out := writerOpenState h transparent io.1
        have hfd : out.fd = io.1 := by
          simp [out, writerOpenState, resetRec, writerEntryRecord, GZ_WRITE, GZ_READ]
        refine ⟨some (.in_gzstate_x h.nextBlk), io.2, writerOpenHeap h transparent name io.1,
          ?_, writerOpen_frame h transparent name io.1 hf hu, out, ?_, ?_, ?_, ?_⟩
        · simpa only [he, ite_false] using hrun
        · rw [hfd]
          exact gz_open_writer_allocated_OpenState h fs fd transparent name hf hu hg hp.2.1 hp.2.2 he
        · rw [hfd]
          exact writerIoResult_OpenWorld h fs name fd transparent out.start
        · simpa only [hfd] using he
        · intro b
          change (writerOpenHeap h transparent name io.1).live b ↔
            ((h.live b ∧ ¬ False) ∨ ZlibF.Spec.Public.GzOwned
              (writerOpenHeap h transparent name io.1) h.nextBlk (writerOpenState h transparent io.1) b)
          rw [writerOpen_owned]
          simpa [he] using writerOpen_ledger h transparent name io.1 hf hu b
    · have he : h.allocOk (h.nalloc + 1) = false := by simpa using h1
      obtain ⟨hframe, hlive, halloc⟩ := writerPathFailure_checks h hf he
      exact ⟨none, fs, { openReleased h with nalloc := h.nalloc + 2 },
        gz_open_writer_path_failure h fs path mode fd transparent name hf hp hm h0 he,
        hframe, hlive, Or.inl halloc⟩
  · have he : h.allocOk h.nalloc = false := by simpa using h0
    obtain ⟨hframe, hlive, halloc⟩ := writerFirstFailure_checks h he
    exact ⟨none, fs, { h with nalloc := h.nalloc + 1 },
      gz_open_alloc_failure h fs path fd mode hpn hmn he, hframe, hlive, Or.inl halloc⟩

/-- `gzFile gzopen(const char *path, const char *mode)`: the ordinary short-path
entry also produces an actual public-history witness on its very same returned
heap. This gives later gzip proofs a real initialization producer. -/
theorem gzopen_writer_short_reachable (h : Heap) (fs : Fs) (path mode : BPtr)
    (transparent : Bool) (name : List UInt8) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h) (hfs : ZlibF.Spec.Public.FileSystem fs)
    (hp : ZlibF.Spec.Public.CString h path name)
    (hm : ZlibF.Spec.Public.CString h mode (if transparent then [119, 84] else [119]))
    (hlen : name.length ≤ 2147483647) :
    ∃ file fs' after, gzopen path mode fs h = .ok ((file, fs'), after) ∧
      ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
      (match file with
       | none => ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
           (ZlibF.Spec.Public.AllocationFailed h after ∨
             ZlibF.Spec.Public.OpenWorld h fs fs' name
               (if transparent then [119, 84] else [119]) .write
               none (-1) 0)
       | some (.in_gzstate_x i) => ∃ s, ZlibF.Spec.Public.GzReachable after fs' i ∧
           ZlibF.Spec.Public.OpenState after i s .write (-1) 0
             (if transparent then 1 else 0) s.fd name ∧
           ZlibF.Spec.Public.OpenWorld h fs fs' name
             (if transparent then [119, 84] else [119]) .write
             none s.fd s.start ∧ s.fd ≠ -1 ∧
           ZlibF.Spec.Public.LiveChange h after (ZlibF.Spec.Public.GzOwned after i s) (fun _ => False)) := by
  obtain ⟨file, fs', after, hrun, hframe, hpost⟩ :=
    gz_open_writer_short h fs path mode (-1) transparent name hf hu hg hp hm hlen
  refine ⟨file, fs', after, hrun, hframe, ?_⟩
  cases file with
  | none => simpa using hpost
  | some ref =>
    cases ref with
    | in_gzstate_x i =>
      obtain ⟨s, hstate, hworld, hfd, hledger⟩ := hpost
      exact ⟨s, ZlibF.Spec.Public.GzReachable.open hf hu hg hfs hp hm hrun,
        hstate, by simpa using hworld, hfd, hledger⟩

#print axioms writerEntry_front
#print axioms writerEntry_fresh
#print axioms writerEntry_uniq
#print axioms gz_open_writer_allocated_run
#print axioms gz_open_writer_allocated_OpenState
#print axioms writerOpen_frame
#print axioms writerOpen_ledger
#print axioms writerOpen_owned
#print axioms gz_open_writer_path_failure
#print axioms writerPathFailure_checks
#print axioms writerFirstFailure_checks
#print axioms gz_open_writer_short
#print axioms gzopen_writer_short_reachable
end Zlib.Gzlib.Proofs
