import ZlibF.Zlib.«gzguts.h»

/-!
# gzlib.c — faithful translation

Source: `gzlib.c` of the verified source (no patch touches it), default x86_64 Linux build: `LSEEK` is `lseek64`
(`_LARGEFILE64_SOURCE`, `_LFS64_LARGEFILE`), `O_CLOEXEC`, `O_NONBLOCK`, `O_EXCL`, `O_LARGEFILE` are defined
(`O_LARGEFILE` is 0), `O_BINARY`, `WIDECHAR`, `UNDER_CE`, `NO_GZCOMPRESS` are not. So `gz_strwinerror`, the `-2`
(wide path) branches and the `#ifndef O_EXCL` block are not compiled.

Open code paths that need a patch in the earlier repository (the translation follows the unpatched C):
* `gzseek64`: signed overflow with a negative `x.pos` (R-1, upstream PR 1361) is a `Fault.ub`.
* `gz_reset`: does not write `x.next` (R-3). A fresh `gz_state` has `x.next = NULL`, so `x.next += 0` is `NULL + 0`
  and does not fault; only R-4 (a dangling `x.next`) can.

File calls go through `Zlib.GzFs` (the model of `open`, `lseek`, `close`, `errno`, `snprintf`).
-/

namespace Zlib.Gzlib
open C Zlib.GzFs Zlib.Gzguts

/-- `unsigned ZLIB_INTERNAL gz_intmax(void)` (`INT_MAX` is defined: `return INT_MAX;`) -/
def gz_intmax : M UInt32 := pure 2147483647

/-- The macro `GT_OFF(x)` of `gzguts.h`: `(sizeof(int) == sizeof(z_off64_t) && (x) > gz_intmax())`. -/
def GT_OFF (x : UInt32) : M Bool := do
  if (4 : Nat) == 8 then return decide (x > (← gz_intmax)) else return false

/-- `void ZLIB_INTERNAL gz_error(gz_statep state, int err, const char *msg)` -/
def gz_error (state : GzStatePtr) (err : Int32) (msg : BPtr) : M Unit := do
  -- if (state->msg != NULL) { if (state->err != Z_MEM_ERROR) free(state->msg); state->msg = NULL; }
  let s ← ldS state
  if s.msg != .null then
    if s.err != Z_MEM_ERROR then freeB s.msg
    updS state fun s => { s with msg := .null }
  -- state->err = err; if (msg == NULL) return;
  updS state fun s => { s with err := err }
  if msg == .null then return
  -- if (err == Z_MEM_ERROR) return;
  if err == Z_MEM_ERROR then return
  -- if ((state->msg = malloc(strlen(state->path) + strlen(msg) + 3)) == NULL) { state->err = Z_MEM_ERROR; return; }
  let s ← ldS state
  let l1 ← strlenB s.path
  let l2 ← strlenB msg
  let m ← allocB (l1 + l2 + 3).toNat
  updS state fun s => { s with msg := m }
  if m == .null then
    updS state fun s => { s with err := Z_MEM_ERROR }
    return
  -- (void)snprintf(state->msg, strlen(state->path) + strlen(msg) + 3, "%s%s%s", state->path, ": ", msg);
  let s ← ldS state
  let fmt ← strLit "%s%s%s"
  let sep ← strLit ": "
  let l1 ← strlenB s.path
  let l2 ← strlenB msg
  let _ ← snprintf s.msg (l1 + l2 + 3) fmt [.str s.path, .str sep, .str msg]

/-- `local void gz_reset(gz_statep state)`. Does not write `x.next` (R-3: the earlier repository's `ub.patch`
hunk `state->x.next = Z_NULL;` is not applied; a fresh state has `x.next = NULL` in the model). -/
def gz_reset (state : GzStatePtr) : M Unit := do
  -- state->x.have = 0; state->past = 0;
  updX state fun x => { x with «have» := 0 }
  updS state fun s => { s with past := 0 }
  -- if (state->mode == GZ_READ) { eof = 0; how = LOOK; junk = -1; } else state->reset = 0;
  let s ← ldS state
  if s.mode == GZ_READ then
    updS state fun s => { s with eof := 0, how := LOOK, junk := -1 }
  else
    updS state fun s => { s with reset := 0 }
  -- state->again = 0; state->skip = 0;
  updS state fun s => { s with again := 0, skip := 0 }
  -- gz_error(state, Z_OK, NULL);
  gz_error state Z_OK .null
  -- state->x.pos = 0; state->strm.avail_in = 0;
  updX state fun x => { x with pos := 0 }
  updZ (strmOf state) fun z => { z with avail_in := 0 }

/-- Loop-carried locals of the mode loop of `gz_open`; `done` is the control tag for `return NULL`. -/
structure ModeLoop where
  mode : BPtr
  oflag : Int32
  exclusive : Int32
  done : Bool

/-- `local gzFile gz_open(const void *path, int fd, const char *mode)` -/
def gz_open (path : BPtr) (fd : Int32) (mode : BPtr) : G GzFilePtr := do
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
  let ml ← gwhile
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
  let _ ← snprintf p (len + 1) fmt [.str path]
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

/-- `gzFile ZEXPORT gzopen(const char *path, const char *mode)` -/
def gzopen (path mode : BPtr) : G GzFilePtr := gz_open path (-1) mode

/-- `gzFile ZEXPORT gzopen64(const char *path, const char *mode)` -/
def gzopen64 (path mode : BPtr) : G GzFilePtr := gz_open path (-1) mode

/-- `gzFile ZEXPORT gzdopen(int fd, const char *mode)` -/
def gzdopen (fd : Int32) (mode : BPtr) : G GzFilePtr := do
  -- if (fd < 0 || (path = (char *)malloc(7 + 3 * sizeof(int))) == NULL) return NULL;
  if fd < 0 then return none
  let path ← allocB (7 + 3 * 4)
  if path == .null then return none
  -- (void)snprintf(path, 7 + 3 * sizeof(int), "<fd:%d>", fd);
  let fmt ← strLit "<fd:%d>"
  let _ ← snprintf path (7 + 3 * 4) fmt [.int fd]
  -- gz = gz_open(path, fd, mode); free(path); return gz;
  let gz ← gz_open path fd mode
  freeB path
  return gz

/-- `int ZEXPORT gzbuffer(gzFile file, unsigned size)` -/
def gzbuffer (file : GzFilePtr) (size : UInt32) : M Int32 := do
  -- if (file == NULL) return -1;
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  -- if (state->mode != GZ_READ && state->mode != GZ_WRITE) return -1;
  if s.mode != GZ_READ && s.mode != GZ_WRITE then return -1
  -- if (state->size != 0) return -1;
  if s.size != 0 then return -1
  -- if ((size << 1) < size) return -1;
  if (size <<< 1) < size then return -1
  -- if (size < 8) size = 8; state->want = size; return 0;
  let size := if size < 8 then 8 else size
  updS state fun s => { s with want := size }
  return 0

/-- `int ZEXPORT gzrewind(gzFile file)` -/
def gzrewind (file : GzFilePtr) : G Int32 := do
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  -- if (state->mode != GZ_READ || (state->err != Z_OK && state->err != Z_BUF_ERROR)) return -1;
  if s.mode != GZ_READ || (s.err != Z_OK && s.err != Z_BUF_ERROR) then return -1
  -- if (LSEEK(state->fd, state->start, SEEK_SET) == -1) return -1;
  if (← fsLseek s.fd s.start SEEK_SET) == -1 then return -1
  gz_reset state
  return 0

/-- `z_off64_t ZEXPORT gzseek64(gzFile file, z_off64_t offset, int whence)`. Unpatched: signed overflow after a
`gzungetc()` right after `gzopen()` (R-1, upstream PR 1361) is `Fault.ub`. -/
def gzseek64 (file : GzFilePtr) (offset : Int64) (whence : Int32) : G Int64 := do
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ && s.mode != GZ_WRITE then return -1
  -- check that there's no error
  if s.err != Z_OK && s.err != Z_BUF_ERROR then return -1
  -- can only seek from start or relative to current position
  if whence != SEEK_SET && whence != SEEK_CUR then return -1
  -- pos = whence == SEEK_SET ? 0 : state->x.pos + (state->past ? 0 : state->skip);
  let mut pos : Int64 ← if whence == SEEK_SET then pure 0
    else i64add s.x.pos (if s.past != 0 then 0 else s.skip)
  -- if (offset > GZ_OFF_MAX - pos) return -1;
  if offset > (← i64sub GZ_OFF_MAX pos) then return -1
  -- if (offset < -pos) return -1;
  if offset < (← i64neg pos) then return -1
  -- pos += offset;
  pos ← i64add pos offset
  -- if (state->mode == GZ_READ && state->how == COPY) { ... }
  if s.mode == GZ_READ && s.how == GZ_COPY then
    let d ← i64sub (← i64sub pos s.x.pos) (u32ToI64 s.x.«have»)
    let ret ← fsLseek s.fd d SEEK_CUR
    if ret == -1 then return -1
    updX state fun x => { x with «have» := 0 }
    updS state fun s => { s with eof := 0, past := 0, skip := 0 }
    gz_error state Z_OK .null
    updZ (strmOf state) fun z => { z with avail_in := 0 }
    updX state fun x => { x with pos := pos }
    return pos
  -- if (pos < state->x.pos) { if (state->mode != GZ_READ) return -1; if (gzrewind(file) == -1) return -1; }
  let s ← ldS state
  if pos < s.x.pos then
    if s.mode != GZ_READ then return -1
    if (← gzrewind file) == -1 then return -1
  -- offset = pos - state->x.pos;
  let s ← ldS state
  let mut offset ← i64sub pos s.x.pos
  -- if (state->mode == GZ_READ) { ... }
  if s.mode == GZ_READ then
    let s ← ldS state
    -- n = GT_OFF(state->x.have) || (z_off64_t)state->x.have > offset ? (unsigned)offset : state->x.have;
    let n : UInt32 ← if (← GT_OFF s.x.«have») || u32ToI64 s.x.«have» > offset then pure offset.toUInt64.toUInt32
      else pure s.x.«have»
    -- state->x.have -= n; state->x.next += n; state->x.pos += n; offset -= n;
    updX state fun x => { x with «have» := x.«have» - n }
    let s ← ldS state
    let nx ← s.x.next.add n.toNat
    updX state fun x => { x with next := nx }
    let s ← ldS state
    let np ← i64add s.x.pos (u32ToI64 n)
    updX state fun x => { x with pos := np }
    offset ← i64sub offset (u32ToI64 n)
  -- state->skip = offset; return pos;
  updS state fun s => { s with skip := offset }
  return pos

/-- `z_off_t ZEXPORT gzseek(gzFile file, z_off_t offset, int whence)` (`z_off_t` is `long`) -/
def gzseek (file : GzFilePtr) (offset : Int64) (whence : Int32) : G Int64 := do
  -- ret = gzseek64(file, (z_off64_t)offset, whence);
  let ret ← gzseek64 file offset whence
  -- return ret == (z_off_t)ret ? (z_off_t)ret : -1;
  return if ret == ret then ret else -1

/-- `z_off64_t ZEXPORT gztell64(gzFile file)` -/
def gztell64 (file : GzFilePtr) : M Int64 := do
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ && s.mode != GZ_WRITE then return -1
  -- return state->x.pos + (state->past ? 0 : state->skip);
  i64add s.x.pos (if s.past != 0 then 0 else s.skip)

/-- `z_off_t ZEXPORT gztell(gzFile file)` -/
def gztell (file : GzFilePtr) : M Int64 := do
  let ret ← gztell64 file
  return if ret == ret then ret else -1

/-- `z_off64_t ZEXPORT gzoffset64(gzFile file)` -/
def gzoffset64 (file : GzFilePtr) : G Int64 := do
  if file.isNone then return -1
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ && s.mode != GZ_WRITE then return -1
  -- offset = LSEEK(state->fd, 0, SEEK_CUR); if (offset == -1) return -1;
  let mut offset ← fsLseek s.fd 0 SEEK_CUR
  if offset == -1 then return -1
  -- if (state->mode == GZ_READ) offset -= state->strm.avail_in;
  if s.mode == GZ_READ then
    let z ← ldZ (strmOf state)
    offset ← i64sub offset (u32ToI64 z.avail_in)
  return offset

/-- `z_off_t ZEXPORT gzoffset(gzFile file)` -/
def gzoffset (file : GzFilePtr) : G Int64 := do
  let ret ← gzoffset64 file
  return if ret == ret then ret else -1

/-- `int ZEXPORT gzeof(gzFile file)` -/
def gzeof (file : GzFilePtr) : M Int32 := do
  if file.isNone then return 0
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ && s.mode != GZ_WRITE then return 0
  -- return state->mode == GZ_READ ? state->past : 0;
  return if s.mode == GZ_READ then s.past else 0

/-- `const char * ZEXPORT gzerror(gzFile file, int *errnum)`. `errnum` is a pointer to a 4-byte block
(little-endian `int`, see `gzguts.h.lean`). -/
def gzerror (file : GzFilePtr) (errnum : BPtr) : M BPtr := do
  if file.isNone then return .null
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ && s.mode != GZ_WRITE then return .null
  -- if (errnum != NULL) *errnum = state->err;
  if errnum != .null then store32 errnum s.err
  -- return state->err == Z_MEM_ERROR ? "out of memory" : (state->msg == NULL ? "" : state->msg);
  if s.err == Z_MEM_ERROR then strLit "out of memory"
  else if s.msg == .null then strLit ""
  else pure s.msg

/-- `void ZEXPORT gzclearerr(gzFile file)` -/
def gzclearerr (file : GzFilePtr) : M Unit := do
  if file.isNone then return
  let state := castState file
  let s ← ldS state
  if s.mode != GZ_READ && s.mode != GZ_WRITE then return
  -- if (state->mode == GZ_READ) { state->eof = 0; state->past = 0; }
  if s.mode == GZ_READ then
    updS state fun s => { s with eof := 0, past := 0 }
  gz_error state Z_OK .null

end Zlib.Gzlib
