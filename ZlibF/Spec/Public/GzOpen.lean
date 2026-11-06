import ZlibF.Spec.Public.GzControl

namespace ZlibF.Spec.Public
open C Zlib.GzFs

def parsedMode (bytes : List UInt8) : Option (Api.GzMode × Int × Nat × Int) :=
  Api.gzMode? (bytes.map fun b => Char.ofNat b.toNat)

def openFlags (bytes : List UInt8) (mode : Api.GzMode) : Int32 :=
  (if 101 ∈ bytes then O_CLOEXEC else 0) ||| (if 78 ∈ bytes then O_NONBLOCK else 0) |||
  (if mode = .read then 0 else O_WRONLY ||| O_CREAT |||
    (if 120 ∈ bytes then O_EXCL else 0) ||| (if mode = .append then O_APPEND else O_TRUNC))

/-- OS operations remain the fixed external-world semantics, rather than an assumed zlib callee. -/
def OpenWorld (h : Heap) (before after : Fs) (path modeBytes : List UInt8)
    (mode : Api.GzMode) (existing : Option Int32) (fd : Int32) (start : Int64) : Prop :=
  ∃ opened,
    (match existing with
     | none => Zlib.GzFs.fsOpen path.toArray (openFlags modeBytes mode) before h = .ok ((fd, opened), h)
     | some oldFd => fd = oldFd ∧ opened = before) ∧
    (if fd = -1 then after = opened
     else if mode = .append then
       ∃ ignored, Zlib.GzFs.fsLseek fd 0 SEEK_END opened h = .ok ((ignored, after), h)
     else if mode = .read then
       ∃ position, Zlib.GzFs.fsLseek fd 0 SEEK_CUR opened h = .ok ((position, after), h) ∧
         start = (if position = -1 then 0 else position)
     else after = opened)

def OpenState (h : Heap) (i : Nat) (s : GzState) (mode : Api.GzMode)
    (level : Int) (strategy : Nat) (direct : Int) (fd : Int32) (path : List UInt8) : Prop :=
  GzValid h i s ∧
  s.mode = (if mode = .read then GZ_READ else GZ_WRITE) ∧ s.fd = fd ∧
  CString h s.path path ∧ s.level.toInt = level ∧ s.strategy.toInt = strategy ∧
  s.direct.toInt = (if mode = .read ∧ direct = 0 then 1 else direct) ∧
  s.size = 0 ∧ s.want = 8192 ∧ s.err = Z_OK ∧ s.msg = .null ∧
  s.x.have = 0 ∧ s.x.pos = 0 ∧ s.past = 0 ∧ s.again = 0 ∧ s.skip = 0 ∧ s.strm.avail_in = 0 ∧
  (mode = .read → s.eof = 0 ∧ s.how = LOOK ∧ s.junk = -1)

def OpenContract (program : BPtr → BPtr → G GzFilePtr) : Prop :=
  (∀ h fs path mode, path = .null ∨ mode = .null → program path mode fs h = .ok ((none, fs), h)) ∧
  (∀ h fs path mode name flags,
    Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → FileSystem fs →
    CString h path name → CString h mode flags →
    ∃ result fs' after, program path mode fs h = .ok ((result, fs'), after) ∧
      Frame h after (fun _ => False) ∧
      (match result with
       | none => LiveChange h after (fun _ => False) (fun _ => False) ∧
           (parsedMode flags = none ∨ AllocationFailed h after ∨
             ∃ mode level strategy direct start,
               parsedMode flags = some (mode, level, strategy, direct) ∧
               OpenWorld h fs fs' name flags mode none (-1) start)
       | some (.in_gzstate_x i) => ∃ s mode level strategy direct,
           parsedMode flags = some (mode, level, strategy, direct) ∧
           OpenState after i s mode level strategy direct s.fd name ∧
           OpenWorld h fs fs' name flags mode none s.fd s.start ∧ s.fd ≠ -1 ∧
           LiveChange h after (GzOwned after i s) (fun _ => False)))

/-- `gzFile gzopen(const char *path, const char *mode)`.
Parse the complete mode string, open/truncate/append as requested, transfer descriptor ownership,
initialize the handle, and release every allocation on a null result. -/
def Goal.gzopen : Prop := OpenContract Zlib.Gzlib.gzopen

/-- `gzFile gzopen64(const char *path, const char *mode)`.
The LP64 entry uses the same open flags and position range as `gzopen`. -/
def Goal.gzopen64 : Prop := OpenContract Zlib.Gzlib.gzopen64

/-- `gzFile gzdopen(int fd, const char *mode)`.
Negative descriptors are rejected. No open syscall occurs, and failure retains the caller's
descriptor. A successful handle takes ownership; its path is the formatted descriptor name. -/
def Goal.gzdopen : Prop :=
  (∀ h fs fd mode, fd.toInt < 0 → Zlib.Gzlib.gzdopen fd mode fs h = .ok ((none, fs), h)) ∧
  (∀ h fs fd mode flags,
    Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → FileSystem fs →
    0 ≤ fd.toInt → (mode ≠ .null → CString h mode flags) →
    ∃ result fs' after, Zlib.Gzlib.gzdopen fd mode fs h = .ok ((result, fs'), after) ∧
      Frame h after (fun _ => False) ∧
      (match result with
       | none => fs'.fds = fs.fds ∧ LiveChange h after (fun _ => False) (fun _ => False) ∧
           (mode = .null ∨ parsedMode flags = none ∨ AllocationFailed h after)
       | some (.in_gzstate_x i) => ∃ s mode level strategy direct,
           parsedMode flags = some (mode, level, strategy, direct) ∧
           OpenState after i s mode level strategy direct fd
             (String.toUTF8 ("<fd:" ++ toString fd.toInt ++ ">")).toList ∧
           OpenWorld h fs fs' [] flags mode (some fd) fd s.start ∧
           LiveChange h after (GzOwned after i s) (fun _ => False)))

end ZlibF.Spec.Public
