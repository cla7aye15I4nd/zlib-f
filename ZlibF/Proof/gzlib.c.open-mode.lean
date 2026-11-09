import ZlibF.Proof.«gzlib.c.open-init»

/-!
# gzlib.c: the actual mode loop for ordinary writer modes

The named loop and tail below are proof cuts of the real source. The equality
`gz_open_mode_cut` checks that rejoining them gives the original translation.
The loop execution lemmas admit every byte reference, heap, and file world.
They do not assume a callee specification or a successful file operation.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- The exact source mode loop, given a live freshly initialized handle. -/
def openModeLoop (state : GzStatePtr) (mode : BPtr) : G ModeLoop := do
  gwhile
    (fun (l : ModeLoop) => do
      let c ← load8 l.mode
      return (c != 0 && !l.done, l))
    (fun (l : ModeLoop) => do
      let c : Int32 := (← load8 l.mode).toInt8.toInt32
      let mut l := l
      if c ≥ 48 && c ≤ 57 then
        -- state->level = *mode - '0';
        updS state fun s => { s with level := c - 48 }
      else if c == 114 then       -- 'r'
        updS state fun s => { s with mode := GZ_READ }
      else if c == 119 then       -- 'w'
        updS state fun s => { s with mode := GZ_WRITE }
      else if c == 97 then        -- 'a'
        updS state fun s => { s with mode := GZ_APPEND }
      else if c == 43 then        -- '+': can't read and write at the same time
        freeGzState state
        l := { l with done := true }
      else if c == 98 then        -- 'b'
        pure ()
      else if c == 101 then       -- 'e'
        l := { l with oflag := l.oflag ||| O_CLOEXEC }
      else if c == 120 then       -- 'x'
        l := { l with exclusive := 1 }
      else if c == 102 then       -- 'f'
        updS state fun s => { s with strategy := Z_FILTERED }
      else if c == 104 then       -- 'h'
        updS state fun s => { s with strategy := Z_HUFFMAN_ONLY }
      else if c == 82 then        -- 'R'
        updS state fun s => { s with strategy := Z_RLE }
      else if c == 70 then        -- 'F'
        updS state fun s => { s with strategy := Z_FIXED }
      else if c == 71 then        -- 'G'
        updS state fun s => { s with direct := -1 }
      else if c == 78 then        -- 'N'
        l := { l with oflag := l.oflag ||| O_NONBLOCK }
      else if c == 84 then        -- 'T'
        updS state fun s => { s with direct := 1 }
      else pure ()                -- default: ignore
      if !l.done then l := { l with mode := ← l.mode.add 1 }
      return l)
    { mode, oflag := 0, exclusive := 0, done := false }

/-- The exact source continuation after its mode loop. -/
def openAfterMode (state : GzStatePtr) (path : BPtr) (fd : Int32) (ml : ModeLoop) : G GzFilePtr := do
  if ml.done then return none
  let oflag0 := ml.oflag
  let exclusive := ml.exclusive
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
  let _ ← vsnprintf p (len + 1) fmt [.str path]
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


/-- `gzFile gz_open(const void *path, int fd, const char *mode)` is exactly its
source prefix, named mode loop, and source tail. This guards the proof cuts
against silently replacing the real computation. -/
theorem gz_open_mode_cut (path : BPtr) (fd : Int32) (mode : BPtr) :
    gz_open path fd mode = (do
    -- int oflag = 0; int exclusive = 0;
    -- if (path == NULL || mode == NULL) return NULL;
    if path == .null || mode == .null then return none
    -- state = (gz_statep)malloc(sizeof(gz_state)); if (state == NULL) return NULL;
    let state ← allocGzState
    if state.isNone then return none
    -- state->size = 0; state->want = GZBUFSIZE; state->err = Z_OK; state->msg = NULL;
    updS state fun s => { s with size := 0, want := GZBUFSIZE.toUInt32, err := Z_OK, msg := .null }
    -- state->mode = GZ_NONE; level = Z_DEFAULT_COMPRESSION; strategy = Z_DEFAULT_STRATEGY; direct = 0;
    updS state fun s => { s with mode := GZ_NONE, level := Z_DEFAULT_COMPRESSION, strategy := Z_DEFAULT_STRATEGY,
                                 direct := 0 }
    -- while (*mode) { ... mode++; }
    let ml ← openModeLoop state mode
    openAfterMode state path fd ml) := by
  rfl

/-- A `gz_state` field update cannot modify a mode-string byte object, including
static strings and byte arrays embedded in other kinds of record. -/
theorem modeBytes_setS (h : Heap) (i : Nat) (s : GzState) (r : BRef) :
    Space.get (setS h i s) r = Space.get h r := by
  cases r <;> rfl

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` scans an exact
`w` mode from any byte-reference kind. It returns the real loop locals, changes
only the handle's mode, consumes no allocation, and leaves the file world alone.
The pointer may be an interior offset and the old integer fields are arbitrary. -/
theorem openModeLoop_write (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a)
    (hend : off + 1 < a.size) (hw : a[off] = 119) (hz : a[off + 1] = 0) :
    openModeLoop (some (.tab i)) (.ref r off) fs h =
      .ok (({ mode := .ref r (off + 1), oflag := 0, exclusive := 0, done := false }, fs),
        setS h i { s with mode := GZ_WRITE }) := by
  have hoff : off < a.size := by omega
  have hadd : 0 ≤ (off : Int) + 1 ∧ (off : Int) + 1 ≤ (a.size : Int) := by omega
  unfold openModeLoop gwhile
  rw [show fuel = 18446744073709551615 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, ha, hoff, hw, hs, Ptr.add, hadd, modeBytes_setS]
  rw [show 18446744073709551615 = 18446744073709551614 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, modeBytes_setS, ha, hend, hz]

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` scans an exact
`wT` mode without imposing a path, file-system, or allocation-success condition.
The real three loop tests terminate, the mode pointer advances twice, and only
the mode/direct fields of the live handle change. -/
theorem openModeLoop_write_direct (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a)
    (hend : off + 2 < a.size) (hw : a[off] = 119)
    (ht : a[off + 1] = 84) (hz : a[off + 2] = 0) :
    openModeLoop (some (.tab i)) (.ref r off) fs h =
      .ok (({ mode := .ref r (off + 2), oflag := 0, exclusive := 0, done := false }, fs),
        setS h i { s with mode := GZ_WRITE, direct := 1 }) := by
  have hoff : off < a.size := by omega
  have hoff1 : off + 1 < a.size := by omega
  have hadd : 0 ≤ (off : Int) + 1 ∧ (off : Int) + 1 ≤ (a.size : Int) := by omega
  have hadd1 : 0 ≤ ((off + 1 : Nat) : Int) + 1 ∧
      ((off + 1 : Nat) : Int) + 1 ≤ (a.size : Int) := by omega
  have hadd2 : 0 ≤ (off : Int) + 1 + 1 ∧ (off : Int) + 1 + 1 ≤ (a.size : Int) := by omega
  have htoNat : ((off : Int) + 1 + 1).toNat = off + 2 := by omega
  have hs1 : (setS h i { s with mode := GZ_WRITE }).gzstates i =
      some { s with mode := GZ_WRITE } := by simp [setS]
  unfold openModeLoop gwhile
  rw [show fuel = 18446744073709551615 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, ha, hoff, hw, hs, Ptr.add, hadd, modeBytes_setS]
  rw [show 18446744073709551615 = 18446744073709551614 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, modeBytes_setS, ha, hoff1, ht, hs1, Ptr.add, hadd1, hadd2, htoNat]
  rw [show 18446744073709551614 = 18446744073709551613 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, modeBytes_setS, ha, hend, hz, Nat.add_assoc]

/-- Mode parsing replaces one live handle, preserves every other existing
object, and neither creates nor removes any live allocation. -/
theorem openModeLoop_frame (h : Heap) (i : Nat) (s t : GzState)
    (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.Frame h (setS h i t) (fun b => b = i) ∧
    ZlibF.Spec.Public.LiveChange h (setS h i t) (fun _ => False) (fun _ => False) := by
  constructor
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    simp [setS, hb]
  · intro b
    by_cases hb : b = i
    · subst b
      simp [Heap.live, setS, hs]
    · simp [Heap.live, setS, hb]

/-- The actual fields written before parsing, retaining arbitrary untouched
integers from the successful handle allocation. -/
def openFrontRecord (h : Heap) : GzState :=
  { GzState.garbage (h.garbage h.nalloc) with
    size := 0
    want := GZBUFSIZE.toUInt32
    err := Z_OK
    msg := .null
    mode := GZ_NONE
    level := Z_DEFAULT_COMPRESSION
    strategy := Z_DEFAULT_STRATEGY
    direct := 0 }

/-- Exact heap between the real initial field writes and mode parsing. -/
def openFrontHeap (h : Heap) : Heap :=
  { h with
    gzstates := upd h.gzstates h.nextBlk (some (openFrontRecord h))
    nextBlk := h.nextBlk + 1
    nalloc := h.nalloc + 1 }

/-- Neither successful handle allocation nor its field writes change a mode byte. -/
theorem modeBytes_openFrontHeap (h : Heap) (r : BRef) :
    Space.get (openFrontHeap h) r = Space.get h r := by
  cases r <;> rfl

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` reaches its
actual source tail after successful handle allocation and exact `w` parsing.
The path, file world, descriptor, and untouched allocation garbage are arbitrary.
This equality exposes the later operations instead of assuming their contracts. -/
theorem gz_open_write_front (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32)
    (r : BRef) (off : Nat) (a : Array UInt8) (hp : path ≠ .null)
    (ha : Space.get h r = some a) (hend : off + 1 < a.size)
    (hw : a[off] = 119) (hz : a[off + 1] = 0)
    (hok : h.allocOk h.nalloc = true) (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open path fd (.ref r off) fs h =
      openAfterMode (some (.tab h.nextBlk)) path fd
        { mode := .ref r (off + 1), oflag := 0, exclusive := 0, done := false }
        fs (setS (openFrontHeap h) h.nextBlk { openFrontRecord h with mode := GZ_WRITE }) := by
  have hs : (openFrontHeap h).gzstates h.nextBlk = some (openFrontRecord h) := by
    simp [openFrontHeap]
  have hg : Space.get (openFrontHeap h) r = some a := by
    rw [modeBytes_openFrontHeap]; exact ha
  have hloop := openModeLoop_write (openFrontHeap h) fs h.nextBlk (openFrontRecord h)
    r off a hs hg hend hw hz
  rw [gz_open_mode_cut]
  offsetsimp [hp, allocGzState, hok, hfresh, setS, upd_upd]
  dsimp only [openFrontHeap, openFrontRecord] at hloop
  rw [hloop]
  rfl


/-- `gzFile gz_open(const void *path, int fd, const char *mode)` reaches its
actual source tail after successful handle allocation and exact `wT` parsing.
The path, file world, descriptor, and untouched allocation garbage are arbitrary.
This equality exposes the later operations instead of assuming their contracts. -/
theorem gz_open_write_direct_front (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32)
    (r : BRef) (off : Nat) (a : Array UInt8) (hp : path ≠ .null)
    (ha : Space.get h r = some a) (hend : off + 2 < a.size)
    (hw : a[off] = 119) (ht : a[off + 1] = 84) (hz : a[off + 2] = 0)
    (hok : h.allocOk h.nalloc = true) (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open path fd (.ref r off) fs h =
      openAfterMode (some (.tab h.nextBlk)) path fd
        { mode := .ref r (off + 2), oflag := 0, exclusive := 0, done := false }
        fs (setS (openFrontHeap h) h.nextBlk { openFrontRecord h with mode := GZ_WRITE, direct := 1 }) := by
  have hs : (openFrontHeap h).gzstates h.nextBlk = some (openFrontRecord h) := by
    simp [openFrontHeap]
  have hg : Space.get (openFrontHeap h) r = some a := by
    rw [modeBytes_openFrontHeap]; exact ha
  have hloop := openModeLoop_write_direct (openFrontHeap h) fs h.nextBlk (openFrontRecord h)
    r off a hs hg hend hw ht hz
  rw [gz_open_mode_cut]
  offsetsimp [hp, allocGzState, hok, hfresh, setS, upd_upd]
  dsimp only [openFrontHeap, openFrontRecord] at hloop
  rw [hloop]
  rfl


/-- The successfully allocated handle is the only new live object before path
allocation. Every caller object is retained exactly; no old object is removed.
Only the actual successful allocation's freshness check is assumed. -/
theorem openFrontHeap_ledger (h : Heap) (t : GzState)
    (hfresh : h.slotUsed h.nextBlk = false) :
    ZlibF.Spec.Public.Frame h (setS (openFrontHeap h) h.nextBlk t) (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h (setS (openFrontHeap h) h.nextBlk t)
      (fun b => b = h.nextBlk) (fun _ => False) := by
  have hn : ¬ h.live h.nextBlk := Heap.slotUsed_eq_false.mp hfresh
  constructor
  · refine ⟨rfl, rfl, rfl, by simp [setS, openFrontHeap],
      by simp [setS, openFrontHeap], ?_⟩
    intro b hl _
    have hb : b ≠ h.nextBlk := fun he => hn (he ▸ hl)
    simp [setS, openFrontHeap, hb]
  · intro b
    by_cases hb : b = h.nextBlk
    · subst b
      simp [setS, openFrontHeap, Heap.live]
    · simp [setS, openFrontHeap, Heap.live, hb]

/-- `gzFile gz_open(const void *path, int fd, const char *mode)`: the actual
writer tail frees its live handle when allocating the copied path fails.
The path is any terminated byte range and the file system is arbitrary. The
file-opening stage is never reached on this allocation-refusal branch. -/
theorem openAfterMode_write_path_failure (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (ml : ModeLoop) (fd : Int32) (pr : BRef) (po last : Nat) (pa : Array UInt8)
    (hs : h.gzstates i = some s) (hmode : s.mode = GZ_WRITE) (hdir : s.direct ≠ -1)
    (hdone : ml.done = false) (hp : Space.get h pr = some pa)
    (hplast : po ≤ last) (hpz : pa[last]? = some 0)
    (hpn : ∀ j, po ≤ j → j < last → pa[j]? ≠ some 0)
    (hfail : h.allocOk h.nalloc = false) :
    openAfterMode (some (.tab i)) (.ref pr po) fd ml fs h =
      .ok ((none, fs), { h with gzstates := upd h.gzstates i none, nalloc := h.nalloc + 1 }) := by
  have hstr : strlenFrom pa po = some last :=
    strlenFrom_eq pa last hpz (last - po) po (by omega) hpn
  unfold openAfterMode
  offsetsimp [hdone, hs, hmode, hdir, GZ_WRITE, GZ_READ, GZ_NONE,
    strlenB, hp, hstr, allocB, hfail, freeGzState, setS, upd_upd]

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` with exact `w`
mode handles a refused path allocation for any valid terminated path, any file
world, and any first-allocation garbage. Both byte references may be interior
or static; no file permission assumption is needed before the open stage. -/
theorem gz_open_write_path_failure_anyref (h : Heap) (fs : Fs) (fd : Int32)
    (mr pr : BRef) (mo po last : Nat) (ma pa : Array UInt8)
    (hm : Space.get h mr = some ma) (hmend : mo + 1 < ma.size)
    (hmw : ma[mo] = 119) (hmz : ma[mo + 1] = 0)
    (hp : Space.get h pr = some pa) (hplast : po ≤ last)
    (hpz : pa[last]? = some 0)
    (hpn : ∀ j, po ≤ j → j < last → pa[j]? ≠ some 0)
    (hok : h.allocOk h.nalloc = true) (hfail : h.allocOk (h.nalloc + 1) = false)
    (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open (.ref pr po) fd (.ref mr mo) fs h =
      .ok ((none, fs), { openReleased h with nalloc := h.nalloc + 2 }) := by
  rw [gz_open_write_front h fs (.ref pr po) fd mr mo ma (by simp)
    hm hmend hmw hmz hok hfresh]
  let parsed := { openFrontRecord h with mode := GZ_WRITE }
  let after := setS (openFrontHeap h) h.nextBlk parsed
  have hs : after.gzstates h.nextBlk = some parsed := by simp [after, setS]
  have hpath : Space.get after pr = some pa := by
    dsimp only [after]
    rw [modeBytes_setS, modeBytes_openFrontHeap]; exact hp
  have hex := openAfterMode_write_path_failure after fs h.nextBlk parsed
    { mode := .ref mr (mo + 1), oflag := 0, exclusive := 0, done := false }
    fd pr po last pa hs rfl (by change (0 : Int32) ≠ -1; decide) rfl hpath hplast hpz hpn
    (by simpa [after, setS, openFrontHeap] using hfail)
  simpa [after, setS, openFrontHeap, openReleased, upd_upd, Nat.add_assoc] using hex

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` with exact `wT`
mode handles a refused path allocation for any valid terminated path, any file
world, and any first-allocation garbage. Both byte references may be interior
or static; no file permission assumption is needed before the open stage. -/
theorem gz_open_write_direct_path_failure_anyref (h : Heap) (fs : Fs) (fd : Int32)
    (mr pr : BRef) (mo po last : Nat) (ma pa : Array UInt8)
    (hm : Space.get h mr = some ma) (hmend : mo + 2 < ma.size)
    (hmw : ma[mo] = 119) (hmt : ma[mo + 1] = 84) (hmz : ma[mo + 2] = 0)
    (hp : Space.get h pr = some pa) (hplast : po ≤ last)
    (hpz : pa[last]? = some 0)
    (hpn : ∀ j, po ≤ j → j < last → pa[j]? ≠ some 0)
    (hok : h.allocOk h.nalloc = true) (hfail : h.allocOk (h.nalloc + 1) = false)
    (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open (.ref pr po) fd (.ref mr mo) fs h =
      .ok ((none, fs), { openReleased h with nalloc := h.nalloc + 2 }) := by
  rw [gz_open_write_direct_front h fs (.ref pr po) fd mr mo ma (by simp)
    hm hmend hmw hmt hmz hok hfresh]
  let parsed := { openFrontRecord h with mode := GZ_WRITE, direct := 1 }
  let after := setS (openFrontHeap h) h.nextBlk parsed
  have hs : after.gzstates h.nextBlk = some parsed := by simp [after, setS]
  have hpath : Space.get after pr = some pa := by
    dsimp only [after]
    rw [modeBytes_setS, modeBytes_openFrontHeap]; exact hp
  have hex := openAfterMode_write_path_failure after fs h.nextBlk parsed
    { mode := .ref mr (mo + 2), oflag := 0, exclusive := 0, done := false }
    fd pr po last pa hs rfl (by change (1 : Int32) ≠ -1; decide) rfl hpath hplast hpz hpn
    (by simpa [after, setS, openFrontHeap] using hfail)
  simpa [after, setS, openFrontHeap, openReleased, upd_upd, Nat.add_assoc] using hex

#print axioms gz_open_mode_cut
#print axioms openModeLoop_write
#print axioms openModeLoop_write_direct
#print axioms openModeLoop_frame
#print axioms gz_open_write_front
#print axioms gz_open_write_direct_front
#print axioms openFrontHeap_ledger
#print axioms openAfterMode_write_path_failure
#print axioms gz_open_write_path_failure_anyref
#print axioms gz_open_write_direct_path_failure_anyref
end Zlib.Gzlib.Proofs
