import ZlibF.Spec.Public.GzState
import ZlibF.Spec.Public.Queries

namespace ZlibF.Spec.Public
open C Zlib.GzFs

def putGz (h : Heap) (i : Nat) (s : GzState) : Heap :=
  { h with gzstates := upd h.gzstates i (some s) }

/-- `int gzbuffer(gzFile file, unsigned size)`.
The current source clamps to eight bytes. It refuses initialized buffers and doubled-size overflow. -/
def Goal.gzbuffer : Prop :=
  (∀ h size, C.run (Zlib.Gzlib.gzbuffer none size) h = .ok (-1, h)) ∧
  (∀ h i s size, h.gzstates i = some s →
    C.run (Zlib.Gzlib.gzbuffer (some (.in_gzstate_x i)) size) h =
      if (s.mode ≠ GZ_READ ∧ s.mode ≠ GZ_WRITE) ∨ s.size ≠ 0 ∨ 2 ^ 31 ≤ size.toNat then
        .ok (-1, h)
      else .ok (0, putGz h i { s with want := UInt32.ofNat (max size.toNat 8) }))

/-- `int gzeof(gzFile file)`.
Report a read past the end, rather than merely the last successful byte. Writers report zero. -/
def Goal.gzeof : Prop :=
  (∀ h, C.run (Zlib.Gzlib.gzeof none) h = .ok (0, h)) ∧
  (∀ h i s, h.gzstates i = some s → C.run (Zlib.Gzlib.gzeof (some (.in_gzstate_x i))) h =
    .ok ((if s.mode = GZ_READ then s.past else 0), h))

def tellValue (s : GzState) : Int := s.x.pos.toInt + if s.past ≠ 0 then 0 else s.skip.toInt

def TellContract (program : GzFilePtr → M Int64) : Prop :=
  (∀ h, C.run (program none) h = .ok (-1, h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s →
    C.run (program (some (.in_gzstate_x i))) h =
      .ok ((if -(2 ^ 63) ≤ tellValue s ∧ tellValue s < 2 ^ 63 then Int64.ofInt (tellValue s) else -1), h))

/-- `z_off64_t gztell64(gzFile file)`; uncompressed position, including a pending seek except after EOF. -/
def Goal.gztell64 : Prop := TellContract Zlib.Gzlib.gztell64

/-- `z_off_t gztell(gzFile file)`; the LP64 wrapper retains the signed 64-bit range. -/
def Goal.gztell : Prop := TellContract Zlib.Gzlib.gztell

def OffsetContract (program : GzFilePtr → G Int64) : Prop :=
  (∀ h fs, program none fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s → RegularOs fs → FileSystem fs →
    ∃ value fs', program (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), h) ∧
      { fs' with errno := fs.errno, nos := fs.nos } = fs ∧
      (if s.fd.toInt < 0 then value = -1 else match fs.fds[s.fd.toInt.toNat]? with
       | some (some file) => value.toInt = (file.pos : Int) -
           (if s.mode = GZ_READ then s.strm.avail_in.toNat else 0)
       | _ => value = -1))

/-- `z_off64_t gzoffset64(gzFile file)`.
The physical descriptor position excludes compressed input already buffered by a reader. -/
def Goal.gzoffset64 : Prop := OffsetContract Zlib.Gzlib.gzoffset64

/-- `z_off_t gzoffset(gzFile file)`; the LP64 wrapper has the same physical-position contract. -/
def Goal.gzoffset : Prop := OffsetContract Zlib.Gzlib.gzoffset

def intBytes (n : Int32) : List UInt8 :=
  (List.range 4).map fun j => UInt8.ofNat (n.toUInt32.toNat / 256 ^ j % 256)

/-- `const char *gzerror(gzFile file, int *errnum)`.
Store the optional error code and return a borrowed message pointer. The query allocates nothing. -/
def Goal.gzerror : Prop :=
  (∀ h errnum, C.run (Zlib.Gzlib.gzerror none errnum) h = .ok (.null, h)) ∧
  (∀ h i s errnum, GzValid h i s →
    (errnum ≠ .null → GzRange h i s errnum 4 true) →
    ∃ pointer after, C.run (Zlib.Gzlib.gzerror (some (.in_gzstate_x i)) errnum) h = .ok (pointer, after) ∧
      Store h errnum (if errnum = .null then [] else intBytes s.err) after ∧
      (if s.err = Z_MEM_ERROR then StaticString after pointer "out of memory"
       else if s.msg = .null then StaticString after pointer "" else pointer = s.msg))

/-- `void gzclearerr(gzFile file)`.
Clear the error and message, and rearm EOF detection for readers. Free the old owned message. -/
def Goal.gzclearerr : Prop :=
  (∀ h, C.run (Zlib.Gzlib.gzclearerr none) h = .ok ((), h)) ∧
  (∀ h i s, GzValid h i s →
    C.run (Zlib.Gzlib.gzclearerr (some (.in_gzstate_x i))) h = .ok ((),
      putGz (dropWindow h s.msg) i { s with
        eof := if s.mode = GZ_READ then 0 else s.eof
        past := if s.mode = GZ_READ then 0 else s.past
        err := Z_OK, msg := .null }))

def rewoundState (s : GzState) : GzState :=
  { s with
    eof := 0, past := 0, how := LOOK, junk := -1, again := 0, skip := 0, err := Z_OK, msg := .null
    x := { s.x with «have» := 0, pos := 0 }
    strm := { s.strm with avail_in := 0 } }

/-- `int gzrewind(gzFile file)`.
Seek back to the saved descriptor start, discard buffered output and reset reader bookkeeping. -/
def Goal.gzrewind : Prop :=
  (∀ h fs, Zlib.Gzlib.gzrewind none fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s → RegularOs fs →
    ∃ rc fs' after, Zlib.Gzlib.gzrewind (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      ((rc = -1 ∧ after = h) ∨
       (rc = 0 ∧ after = putGz (dropWindow h s.msg) i (rewoundState s) ∧
        ∃ file, fs'.fds[s.fd.toInt.toNat]? = some (some file) ∧ file.pos = s.start.toInt.toNat)) ∧
      (s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR) → rc = -1 ∧ fs' = fs))

def SeekContract (program : GzFilePtr → Int64 → Int32 → G Int64) : Prop :=
  (∀ h fs offset whence, program none offset whence fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s offset whence, GzReachable h fs i → GzValid h i s → FileSystem fs →
    ∃ rc fs' after s', program (some (.in_gzstate_x i)) offset whence fs h = .ok ((rc, fs'), after) ∧
      GzStateFrame h after fs fs' i s s' [] ∧
      (rc = -1 ∨ (0 ≤ rc.toInt ∧ rc.toInt =
        (if whence = 0 then 0 else tellValue s) + offset.toInt)) ∧
      (whence ≠ 0 ∧ whence ≠ 1 → rc = -1 ∧ after = h) ∧
      (rc = -1 → after = h) ∧
      (0 ≤ rc.toInt → s'.x.pos.toInt + s'.skip.toInt = rc.toInt ∧
        s'.skip.toInt ≥ 0) ∧
      (s.mode = GZ_WRITE → rc.toInt < s.x.pos.toInt → rc = -1))

/-- `z_off64_t gzseek64(gzFile file, z_off64_t offset, int whence)`.
Signed range checks are obligations, including negative positions created by pushback.
A successful seek can remain pending; EOF affects the separate tell query. -/
def Goal.gzseek64 : Prop := SeekContract Zlib.Gzlib.gzseek64

/-- `z_off_t gzseek(gzFile file, z_off_t offset, int whence)`; the LP64 conversion preserves the result. -/
def Goal.gzseek : Prop := SeekContract Zlib.Gzlib.gzseek

end ZlibF.Spec.Public
