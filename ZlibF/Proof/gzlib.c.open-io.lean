import ZlibF.Proof.«gzlib.c.path-copy»
import ZlibF.Proof.«gzlib.c.error»
import ZlibF.Proof.«gzfs.oracle»

/-!
# gzlib.c: the actual writer I/O and reset tail

These lemmas evaluate the source after its path has been copied. File-open
results come from the `fsOpen` computation (any oracle value). No callee contract is assumed.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Exact source tail after the successful path-formatting call. -/
def openAfterPath (state : GzStatePtr) (path : BPtr) (fd : Int32) (ml : ModeLoop) : G GzFilePtr := do
  let oflag0 := ml.oflag
  let exclusive := ml.exclusive
  -- compute the flags for open()
  let s ← ldS state
  let oflag : Int32 := oflag0 ||| (O_LARGEFILE |||
    (if s.mode == GZ_READ then 0
     else (O_WRONLY ||| O_CREAT ||| (if exclusive != 0 then O_EXCL else 0) |||
           (if s.mode == GZ_WRITE then O_TRUNC else O_APPEND))))
  -- open the file with the appropriate flags (or just use fd)
  if fd == -1 then
    -- state->fd = open((const char *)path, oflag, 0666);
    let name ← cstring path
    let r ← fsOpen name oflag
    updS state fun s => { s with fd := r }
  else
    -- if (oflag & O_NONBLOCK) fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
    if oflag &&& O_NONBLOCK != 0 then fsFcntl fd
    -- if (oflag & O_CLOEXEC) fcntl(fd, F_SETFD, fcntl(fd, F_GETFD) | FD_CLOEXEC);
    if oflag &&& O_CLOEXEC != 0 then fsFcntl fd
    updS state fun s => { s with fd := fd }
  -- if (state->fd == -1) { free(state->path); free(state); return NULL; }
  let s ← ldS state
  if s.fd == -1 then
    freeB s.path
    freeGzState state
    return none
  -- if (state->mode == GZ_APPEND) { LSEEK(state->fd, 0, SEEK_END); state->mode = GZ_WRITE; }
  if s.mode == GZ_APPEND then
    let _ ← fsLseek s.fd 0 SEEK_END
    updS state fun s => { s with mode := GZ_WRITE }
  -- if (state->mode == GZ_READ) { state->start = LSEEK(state->fd, 0, SEEK_CUR); if (state->start == -1) state->start = 0; }
  let s ← ldS state
  if s.mode == GZ_READ then
    let st ← fsLseek s.fd 0 SEEK_CUR
    updS state fun s => { s with start := st }
    if st == -1 then updS state fun s => { s with start := 0 }
  -- gz_reset(state); return (gzFile)state;
  gz_reset state
  return castFile state



/-- Rejoining the path-prefix and I/O cut is exactly the actual source tail. -/
theorem openAfterMode_path_cut (state : GzStatePtr) (path : BPtr) (fd : Int32) (ml : ModeLoop) :
    openAfterMode state path fd ml = (do
    if ml.done then return none
    -- if (state->mode == GZ_NONE) { free(state); return NULL; }
    let s ← ldS state
    if s.mode == GZ_NONE then
      freeGzState state
      return none
    -- direct is 0, 1 if "T", or -1 if "G"
    if s.mode == GZ_READ then
      if s.direct == 1 then
        freeGzState state
        return none
      if s.direct == 0 then
        updS state fun s => { s with direct := 1 }
    else if s.direct == -1 then
      freeGzState state
      return none
    -- len = strlen((const char *)path); state->path = (char *)malloc(len + 1);
    let len ← strlenB path
    let p ← allocB (len + 1).toNat
    updS state fun s => { s with path := p }
    if p == .null then
      freeGzState state
      return none
    -- (void)snprintf(state->path, len + 1, "%s", (const char *)path);
    let fmt ← strLit "%s"
    let _ ← snprintf p (len + 1) fmt [.str path]
    openAfterPath state path fd ml) := by
  rfl

/-- The external `open` computation never touches the C heap and does not
raise a C fault. Errors are returned as the actual descriptor and file world. -/
theorem openFs_pure (name : Array UInt8) (flags : Int32) (fs : Fs) :
    ∃ result, fsOpen name flags fs = (pure result : M (Int32 × Fs)) :=
  Zlib.GzFs.Proofs.fsOpen_pure name flags fs

/-- The external call's exact result, defined from its real computation. -/
def openFsResult (name : Array UInt8) (flags : Int32) (fs : Fs) : Int32 × Fs :=
  match fsOpen name flags fs Heap.empty with
  | .ok (result, _) => result
  | .error _ => (-1, fs)

/-- Exact fixed-world `open` execution on every C heap. -/
theorem openFs_eq (name : Array UInt8) (flags : Int32) (fs : Fs) (h : Heap) :
    fsOpen name flags fs h = .ok (openFsResult name flags fs, h) := by
  obtain ⟨result, hr⟩ := openFs_pure name flags fs
  unfold openFsResult
  rw [hr]
  rfl

/-- The writer reset needs only the live record and its actually initialized
mode/message fields. All untouched integer and pointer fields are arbitrary;
the theorem does not claim that C wrote any preserved pointer. -/
theorem gz_reset_writer_null (h : Heap) (i : Nat) (s : GzState)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE) (hmsg : s.msg = .null) :
    gz_reset (some (.tab i)) h = .ok ((), setS h i (resetRec s)) := by
  unfold gz_reset
  offsetsimp [hs, hm, hmsg, gz_error, resetRec, setS, upd_upd, GZ_WRITE, GZ_READ]

/-- Ordinary writer flags, independent of compressed versus transparent output. -/
def writerOpenFlags : Int32 := O_WRONLY ||| O_CREAT ||| O_TRUNC

/-- The exact descriptor/world chosen by the source: either call `open` or
retain the supplied descriptor, with no synthetic I/O-success assumption. -/
def writerIoResult (name : Array UInt8) (fd : Int32) (fs : Fs) : Int32 × Fs :=
  if fd = -1 then openFsResult name writerOpenFlags fs else (fd, fs)

/-- Heap after actual writer I/O refusal or reset. The failure releases the
copied path and handle; success retains both and writes the reset record. -/
def writerIoHeap (h : Heap) (i pb : Nat) (s : GzState) (result : Int32) : Heap :=
  if result = -1 then
    { h with bytes := upd h.bytes pb none, gzstates := upd h.gzstates i none }
  else setS h i (resetRec { s with fd := result })

/-- The actual post-copy writer tail handles every external `open` result.
All source bytes, the file world, supplied descriptor, and uninitialized fields
are arbitrary. On refusal it frees the actual private path and handle; on
success it resets that same handle and returns it. -/
theorem openAfterPath_writer (h : Heap) (fs : Fs) (i pb : Nat) (s : GzState)
    (ml : ModeLoop) (path : BPtr) (fd : Int32) (name : List UInt8) (copy : Array UInt8)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE) (hmsg : s.msg = .null)
    (hflags : ml.oflag = 0) (hexcl : ml.exclusive = 0)
    (hpath : ZlibF.Spec.Public.CString h path name)
    (hprivate : s.path = .ref (.blk pb) 0)
    (hcopy : h.bytes pb = some copy) (hro : h.ro pb = false) :
    openAfterPath (some (.tab i)) path fd ml fs h =
      .ok (((if (writerIoResult name.toArray fd fs).1 = -1 then none
        else some (.in_gzstate_x i)), (writerIoResult name.toArray fd fs).2),
        writerIoHeap h i pb s (writerIoResult name.toArray fd fs).1) := by
  have hname := openPath_cstring_public h path name hpath
  by_cases hfd : fd = -1
  · by_cases hf : (openFsResult name.toArray writerOpenFlags fs).1 = -1
    · dsimp only [writerOpenFlags] at hf
      unfold openAfterPath
      offsetsimp [hs, hm, hflags, hexcl, hfd, hname, openFs_eq, writerOpenFlags,
        writerIoResult, writerIoHeap, hf, hprivate, hcopy, hro, freeB, freeGzState,
        setS, upd_upd, O_LARGEFILE, GZ_WRITE, GZ_READ, GZ_APPEND, hnd]
    · dsimp only [writerOpenFlags] at hf
      unfold openAfterPath
      offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname, openFs_eq, writerOpenFlags,
        writerIoResult, writerIoHeap, hf, gz_reset, gz_error, resetRec,
        setS, upd_upd, O_LARGEFILE, GZ_WRITE, GZ_READ, GZ_APPEND, hnd]
  · have hnb : (writerOpenFlags &&& O_NONBLOCK) = 0 := by decide
    have hce : (writerOpenFlags &&& O_CLOEXEC) = 0 := by decide
    dsimp only [writerOpenFlags] at hnb hce
    unfold openAfterPath
    offsetsimp [hs, hm, hmsg, hflags, hexcl, hfd, hname, writerOpenFlags,
      writerIoResult, writerIoHeap, gz_reset, gz_error, resetRec, fsFcntl,
      setS, upd_upd, O_LARGEFILE, hnb, hce, GZ_WRITE, GZ_READ, GZ_APPEND, hnd]

/-- Replacing the handle record preserves every public caller string. No byte
reference kind stores its byte array inside a `gz_state`. -/
theorem openCString_setS (h : Heap) (i : Nat) (s : GzState) (path : BPtr) (xs : List UInt8)
    (hc : ZlibF.Spec.Public.CString h path xs) :
    ZlibF.Spec.Public.CString (setS h i s) path xs := by
  rcases hc with ⟨hb, hn, hlen⟩
  refine ⟨?_, hn, hlen⟩
  rcases hb with hn | ⟨r, off, a, hp, hg, hb, he⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, off, a, hp, (modeBytes_setS h i s r).trans hg, hb, he⟩

/-- A raw allocated path remains allocated and writable after handle writes. -/
theorem openMallocBuffer_setS (h : Heap) (i : Nat) (s : GzState) (path : BPtr) (n : Nat)
    (hb : ZlibF.Spec.Public.MallocBuffer h path n) :
    ZlibF.Spec.Public.MallocBuffer (setS h i s) path n := by
  rcases hb with ⟨b, a, hp, hg, hr, hfit⟩
  exact ⟨b, a, hp, hg, hr, hfit⟩

/-- The successful real writer I/O/reset tail produces `OpenState` from the
physical allocated path and fields established by the actual source prefix.
No `GzValid` or unproved callee contract is an assumption. -/
theorem writerIoHeap_OpenState (h : Heap) (i pb : Nat) (s : GzState) (result : Int32)
    (name : List UInt8) (direct : Int)
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE)
    (hprivate : s.path = .ref (.blk pb) 0)
    (hsize : s.size = 0) (hwant : s.want = 8192)
    (hlevel : s.level = Z_DEFAULT_COMPRESSION) (hstrategy : s.strategy = Z_DEFAULT_STRATEGY)
    (hdirect : s.direct.toInt = direct) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hpath : ZlibF.Spec.Public.CString h (.ref (.blk pb) 0) name)
    (hbuf : ZlibF.Spec.Public.MallocBuffer h (.ref (.blk pb) 0) (name.length + 1))
    (hresult : result ≠ -1) :
    ZlibF.Spec.Public.OpenState (writerIoHeap h i pb s result) i
      (resetRec { s with fd := result }) .write (-1) 0 direct result name := by
  rw [writerIoHeap, ite_eq_right (by exact hresult)]
  let final := resetRec { s with fd := result }
  have hshape := shape_setS hs final
  have hpf := openCString_setS h i final (.ref (.blk pb) 0) name hpath
  have hbf := openMallocBuffer_setS h i final (.ref (.blk pb) 0) (name.length + 1) hbuf
  have hfinalPath : final.path = .ref (.blk pb) 0 := by
    simp [final, resetRec, hm, hprivate, GZ_WRITE, GZ_READ]
  have hv : ZlibF.Spec.Public.GzValid (setS h i final) i final := by
    refine ⟨by simp [setS], ?_, Shape.fresh hshape rfl hf, Shape.uniq hshape hu,
      hg, ⟨name, ?_, ?_⟩, Or.inl ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [final, resetRec, hm, GZ_WRITE, GZ_READ]
    · simpa only [hfinalPath] using hpf
    · simpa only [hfinalPath] using hbf
    · simp [final, resetRec, hm, GZ_WRITE, GZ_READ]
    · intro _; simp [final, resetRec, hm, GZ_WRITE, GZ_READ]
    · simp [final, resetRec, hwant, hm, GZ_WRITE, GZ_READ]
    · simp [final, resetRec, hwant, hm, GZ_WRITE, GZ_READ]
    · simp [final, resetRec, hsize, hm, GZ_WRITE, GZ_READ]
    · simp [final, resetRec, hm, GZ_WRITE, GZ_READ]
  refine ⟨hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (change ZlibF.Spec.Public.CString (setS h i final) final.path name
       rw [hfinalPath]
       exact hpf)
    | simp [resetRec, hm, hprivate, hsize, hwant, hlevel, hstrategy,
        hdirect, GZ_WRITE, GZ_READ, Z_DEFAULT_COMPRESSION, Z_DEFAULT_STRATEGY]

/-- At a unique live handle, every non-handle table entry is absent. -/
theorem writerHandle_only (h : Heap) (i : Nat) (s : GzState) (hu : Uniq h)
    (hs : h.gzstates i = some s) :
    h.bytes i = none ∧ h.words i = none ∧ h.streams i = none ∧
    h.gzheaders i = none ∧ h.dstates i = none ∧ h.istates i = none := by
  have hc := hu i
  simp only [hs, cnt_some] at hc
  have hz {α : Type} (v : Option α) (hv : cnt v ≤ 0) : v = none := by
    cases v <;> simp [cnt] at *
  exact ⟨hz _ (by omega), hz _ (by omega), hz _ (by omega),
    hz _ (by omega), hz _ (by omega), hz _ (by omega)⟩

/-- At a unique private path, every non-byte table entry is absent. -/
theorem writerPath_only (h : Heap) (pb : Nat) (copy : Array UInt8) (hu : Uniq h)
    (hp : h.bytes pb = some copy) :
    h.words pb = none ∧ h.streams pb = none ∧ h.gzheaders pb = none ∧
    h.dstates pb = none ∧ h.istates pb = none ∧ h.gzstates pb = none := by
  have hc := hu pb
  simp only [hp, cnt_some] at hc
  have hz {α : Type} (v : Option α) (hv : cnt v ≤ 0) : v = none := by
    cases v <;> simp [cnt] at *
  exact ⟨hz _ (by omega), hz _ (by omega), hz _ (by omega),
    hz _ (by omega), hz _ (by omega), hz _ (by omega)⟩

/-- The actual writer I/O tail retains every unrelated object. Refusal removes
exactly the handle and copied path; success removes nothing. Neither branch
creates a C heap object or performs an allocation-oracle call. -/
theorem writerIoHeap_ledger (h : Heap) (i pb : Nat) (s : GzState) (result : Int32)
    (copy : Array UInt8) (hu : Uniq h) (hs : h.gzstates i = some s)
    (hp : h.bytes pb = some copy) :
    ZlibF.Spec.Public.Frame h (writerIoHeap h i pb s result)
      (fun b => b = i ∨ result = -1 ∧ b = pb) ∧
    ZlibF.Spec.Public.LiveChange h (writerIoHeap h i pb s result)
      (fun _ => False) (fun b => result = -1 ∧ (b = i ∨ b = pb)) := by
  by_cases hr : result = -1
  · have hi := writerHandle_only h i s hu hs
    have hb := writerPath_only h pb copy hu hp
    constructor
    · refine ⟨by simp [writerIoHeap, hr], by simp [writerIoHeap, hr],
        by simp [writerIoHeap, hr], by simp [writerIoHeap, hr],
        by simp [writerIoHeap, hr], ?_⟩
      intro b _ hn
      have hbi : b ≠ i := fun he => hn (Or.inl he)
      have hbp : b ≠ pb := fun he => hn (Or.inr ⟨hr, he⟩)
      simp [writerIoHeap, hr, hbi, hbp]
    · intro b
      by_cases hbi : b = i
      · subst b
        simp [writerIoHeap, hr, Heap.live, upd_apply, hs, hi.1, hi.2.1,
          hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2]
      · by_cases hbp : b = pb
        · subst b
          simp [writerIoHeap, hr, Heap.live, hbi, hp, hb.1, hb.2.1,
            hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]
        · simp [writerIoHeap, hr, Heap.live, hbi, hbp]
  · simpa [writerIoHeap, hr] using
      openModeLoop_frame h i s (resetRec { s with fd := result }) hs

/-- The public external-world relation is obtained from the actual I/O result,
for either `w` or `wT`, without assuming a file-system operation's contract. -/
theorem writerIoResult_OpenWorld (h : Heap) (fs : Fs) (name : List UInt8) (fd : Int32)
    (transparent : Bool) (start : Int64) :
    ZlibF.Spec.Public.OpenWorld h fs (writerIoResult name.toArray fd fs).2 name
      (if transparent then [119, 84] else [119]) .write
      (if fd = -1 then none else some fd) (writerIoResult name.toArray fd fs).1 start := by
  have hflags : ZlibF.Spec.Public.openFlags (if transparent then [119, 84] else [119])
      .write = writerOpenFlags := by cases transparent <;> decide
  by_cases he : fd = -1
  · refine ⟨(openFsResult name.toArray writerOpenFlags fs).2, ?_, ?_⟩
    · simpa [he, writerIoResult, hflags] using openFs_eq name.toArray writerOpenFlags fs h
    · simp [writerIoResult, he]
  · refine ⟨fs, ?_, ?_⟩
    · simp [he, writerIoResult]
    · simp [he, writerIoResult]

#print axioms openAfterMode_path_cut
#print axioms openFs_pure
#print axioms openFs_eq
#print axioms gz_reset_writer_null
#print axioms openAfterPath_writer
#print axioms writerIoHeap_OpenState
#print axioms writerIoHeap_ledger
#print axioms writerIoResult_OpenWorld
end Zlib.Gzlib.Proofs
