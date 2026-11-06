import ZlibF.Spec.Api.Deflate

/-!
# API model: the gz file API as state machines over an abstract file

`gzopen` .. `gzclose` (`gzlib.c`, `gzread.c`, `gzwrite.c`, `gzclose.c`). The file system and the
file are abstract: a file is its content, a `List UInt8`; the operating system is not modelled
(an input/output failure is an allowed outcome of the operations that touch the file, after which
the data-level promises stop: `failed`).

*Reading.* What a reader sees is a function of the content of the file only: `GzDecoded raw D S`
says that reading the file to its end returns exactly the bytes `D` and then the status `S`
(`Z_OK`, or the error that `gzerror` reports). The handle keeps the position in `D`.

*Writing.* The handle keeps all the uncompressed bytes written and the compressed bytes the
library has handed to the file so far; `GzDecoded` of the final content gives back what was written.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

/-- The first four bytes look like a gzip header: `1F 8B 08` and flags below 32
(`gz_look`). Anything else is read transparently. -/
def GzLooksGzip (raw : List UInt8) : Prop :=
  raw.length ≥ 4 ∧ raw[0]! = 31 ∧ raw[1]! = 139 ∧ raw[2]! = 8 ∧ raw[3]!.toNat < 32

/-- Reading the whole file `raw` (`gzread` until the end; `gonly`: opened with `G`, so
transparent reading is off):

* a file that does not look like gzip is returned unchanged with status `Z_OK` (`gzdirect` is 1);
* otherwise the file is a sequence of complete gzip members, followed by `rest`. The data is the
  concatenation of the members' data. If `rest` is empty, the status is `Z_OK`. Trailing garbage
  after at least one member is ignored (`Z_OK`, `zlib.h` `gzread`); otherwise the status is the
  error (`Z_BUF_ERROR` for a truncated member, `Z_DATA_ERROR` for a corrupt one) and the data
  also holds what was decoded of `rest` before it (`Layer.Consistent`);
* `gonly` and an empty file: no data and `Z_BUF_ERROR`. -/
def GzDecoded (gonly : Bool) (raw D : List UInt8) (S : Int) : Prop :=
  (gonly = false ∧ ¬ GzLooksGzip raw ∧ D = raw ∧ S = Z.ok) ∨
  (gonly = true ∧ raw = [] ∧ D = [] ∧ S = Z.bufError) ∨
  ((GzLooksGzip raw ∨ (gonly = true ∧ raw ≠ [])) ∧
    ∃ (ms : List (List UInt8 × List UInt8)) (rest : List UInt8),
      (∀ p, p ∈ ms → Gzip.Decodes p.1 p.2) ∧ raw = (ms.map Prod.fst).flatten ++ rest ∧
      (¬ ∃ m o t, rest = m ++ t ∧ Gzip.Decodes m o) ∧
      ((rest = [] ∧ ms ≠ [] ∧ D = (ms.map Prod.snd).flatten ∧ S = Z.ok) ∨
       (rest ≠ [] ∧ ms ≠ [] ∧ D = (ms.map Prod.snd).flatten ∧ S = Z.ok) ∨
       (rest ≠ [] ∧ (S = Z.bufError ∨ S = Z.dataError) ∧
         ∃ q, D = (ms.map Prod.snd).flatten ++ q ∧ Layer.Consistent .gzip 15 [] rest q)))

/-- The mode of the mode string. A handle opened with `a` has mode `write` (as in `gz_open`, which
seeks to the end and then writes). -/
inductive GzMode where
  | read | write | append
  deriving DecidableEq, Repr

/-- `gz_open`'s reading of the mode string: the mode (`r`, `w`, `a`; the last wins), the level (a
digit), the strategy (`f`, `h`, `R`, `F`), and the direct flag (`T` is 1, `G` is -1). `none` for
`+`, for no `r`/`w`/`a`, for `T` with `r`, for `G` with `w`/`a` (a `NULL` result). -/
def gzMode? (m : List Char) : Option (GzMode × Int × Nat × Int) :=
  let step (acc : Option GzMode × Int × Nat × Int × Bool) (c : Char) :=
    let (mo, lv, st, di, bad) := acc
    if '0' ≤ c ∧ c ≤ '9' then (mo, (c.toNat - '0'.toNat : Nat), st, di, bad)
    else if c = 'r' then (some .read, lv, st, di, bad)
    else if c = 'w' then (some .write, lv, st, di, bad)
    else if c = 'a' then (some .append, lv, st, di, bad)
    else if c = '+' then (mo, lv, st, di, true)
    else if c = 'f' then (mo, lv, 1, di, bad)
    else if c = 'h' then (mo, lv, 2, di, bad)
    else if c = 'R' then (mo, lv, 3, di, bad)
    else if c = 'F' then (mo, lv, 4, di, bad)
    else if c = 'G' then (mo, lv, st, -1, bad)
    else if c = 'T' then (mo, lv, st, 1, bad)
    else acc
  match m.foldl step (none, -1, 0, 0, false) with
  | (some mo, lv, st, di, false) =>
    if mo = .read ∧ di = 1 then none
    else if mo ≠ .read ∧ di = -1 then none
    else some (mo, lv, st, di)
  | _ => none

/-- The state of an open gz file. Fields of the reader: `raw` (the content), `dec`, `dstat` (what
`GzDecoded` gives for it), `rpos` (index in `dec` of the next byte, it may be past the end after
a forward `gzseek`), `pushed` (bytes put back by `gzungetc`, delivered first), `past` (a read came up
short). Fields of the writer: `written` (all bytes written, with the zeros of forward seeks), `out`
(the compressed bytes handed to the file so far), `base` (the content that was there before an
append). Both: `err` (the code `gzerror` reports), `want` (buffer size of `gzbuffer`), `sized`
(buffers exist), `failed` (an input/output error happened). -/
structure GzHandle where
  mode : GzMode
  level : Int
  strategy : Nat
  direct : Int
  raw : List UInt8
  dec : List UInt8
  dstat : Int
  rpos : Nat
  pushed : List UInt8
  past : Bool
  err : Int
  written : List UInt8
  out : List UInt8
  base : List UInt8
  want : Nat
  sized : Bool
  failed : Bool
  deriving DecidableEq

/-- The size of the buffer unless `gzbuffer` changes it (`GZBUFSIZE`). -/
def gzBufDefault : Nat := 131072

/-- `gzopen(path, mode)` / `gzdopen(fd, mode)`: `existing` is the content of the file (`none`: it does
not exist, or the descriptor is invalid). The result is `NULL` for a bad mode, a missing file when
reading, or an input/output or allocation failure (not distinguished: any of them may happen);
otherwise a handle. Writing starts with an empty file; appending keeps the content (`base`). -/
def GzOpen (mode : List Char) (existing : Option (List UInt8)) (r : Option GzHandle) : Prop :=
  match gzMode? mode with
  | none => r = none
  | some (mo, lv, st, di) =>
    r = none ∨
    (∃ raw D S, (mo = .read → existing = some raw ∧ GzDecoded (decide (di = -1)) raw D S) ∧
      r = some
        { mode := (if mo = .append then .write else mo), level := lv, strategy := st, direct := di,
          raw := if mo = .read then raw else [], dec := if mo = .read then D else [],
          dstat := if mo = .read then S else Z.ok, rpos := 0, pushed := [], past := false,
          err := Z.ok, written := [], out := [],
          base := if mo = .append then existing.getD [] else [],
          want := gzBufDefault, sized := false, failed := false })

/-- `gzbuffer(file, size)`: allowed only before the first read or write (`-1` after); sizes below 2
become 2. -/
def GzBuffer (h : GzHandle) (size : Nat) (ret : Int) (h' : GzHandle) : Prop :=
  if h.sized = true then ret = -1 ∧ h' = h
  else ret = 0 ∧ h' = { h with want := max size 2 }

/-- `gzdirect(file)`: for a reader, 1 if the content is read as it is, 0 if it is decoded
(`GzDecoded`); the call looks at the file (`sized`). For a writer, 1 only if opened with `T`. A file
opened with `G` is never direct; an empty file, and a file of fewer than four bytes, are. -/
def GzDirect (h : GzHandle) (ret : Int) (h' : GzHandle) : Prop :=
  match h.mode with
  | .read =>
    ((ret = 1 ∧ h.dec = h.raw ∧ ¬ GzLooksGzip h.raw ∧ h.direct ≠ -1) ∨
      (ret = 0 ∧ (GzLooksGzip h.raw ∨ h.direct = -1))) ∧ h' = { h with sized := true }
  | _ => ret = (if h.direct = 1 then 1 else 0) ∧ h' = h

/-- The bytes a reader can still deliver, pushed-back bytes first. -/
def GzHandle.avail (h : GzHandle) : List UInt8 := h.pushed ++ h.dec.drop h.rpos

/-- `gztell` for a reader (`gztell64`: `x.pos + (past ? 0 : skip)`): the uncompressed position, negative
after a push back at the start. After the end was hit (`past`) a pending skip of a forward `gzseek`
is **not** counted: the position stays at the end of the data (quirk of `gzlib.c`, see `GzSeek`). -/
def GzHandle.tell (h : GzHandle) : Int :=
  (if h.past = true then ((min h.rpos h.dec.length : Nat) : Int) else (h.rpos : Int)) - h.pushed.length

/-- The reader is in the mode that copies the file as it is (`how == COPY`): the first read or
`gzdirect` looked at the file (`sized`), it is not empty and does not look like gzip. -/
def GzHandle.CopyMode (h : GzHandle) : Prop :=
  h.sized = true ∧ h.raw ≠ [] ∧ ¬ GzLooksGzip h.raw ∧ h.direct ≠ -1

/-- `gzread(file, buf, len)`: returns `bytes.length`, or `-1`. The bytes are the next bytes of
`pushed ++ dec.drop rpos`; a request longer than `2^31 - 1` is `-1` with `Z_STREAM_ERROR`; a
serious error from earlier is `-1` (data read before the error is delivered first). A read that
comes up short sets `past`, and reveals the status `dstat` of the file (`gzerror`); the status may
also be revealed earlier. `-1` is returned only if no byte was read and the error is serious.
`Z_BUF_ERROR` (a truncated file) does not stop reading. -/
def GzReadFn (h : GzHandle) (len : Nat) (bytes : List UInt8) (ret : Int) (h' : GzHandle) : Prop :=
  (h.mode ≠ .read → ret = -1 ∧ bytes = [] ∧ h' = h) ∧
  (h.mode = .read → if len > 2 ^ 31 - 1 then
    ret = -1 ∧ bytes = [] ∧
      h' = { h with err := if h.err = Z.ok ∨ h.err = Z.bufError then Z.streamError else h.err }
  else if (h.err ≠ Z.ok ∧ h.err ≠ Z.bufError) ∧ h.pushed = [] ∧ h.dec.drop h.rpos = [] then
    ret = -1 ∧ bytes = [] ∧ h' = h
  else
    bytes = h.avail.take len ∧
    h'.pushed = h.pushed.drop bytes.length ∧
    h'.rpos = h.rpos + (bytes.length - min bytes.length h.pushed.length) ∧
    h'.dec = h.dec ∧ h'.raw = h.raw ∧ h'.mode = h.mode ∧
    (0 < len → h'.sized = true) ∧ (len = 0 → h'.sized = h.sized) ∧
    (bytes.length < len → h'.past = true ∧ h'.err = h.dstat) ∧
    (bytes.length = len → h'.past = h.past ∧ (h'.err = h.err ∨ h'.err = h.dstat)) ∧
    (ret = if bytes = [] ∧ len > 0 ∧ h'.err ≠ Z.ok ∧ h'.err ≠ Z.bufError then -1
           else (bytes.length : Int)))

/-- `gzfread(buf, size, nitems, file)`: the number of whole items read; a partial item that was
read is lost (`zlib.h`). -/
def GzFread (h : GzHandle) (size nitems : Nat) (bytes : List UInt8) (items : Nat) (h' : GzHandle) :
    Prop :=
  (h.mode ≠ .read ∨ size = 0 → items = 0 ∧ bytes = [] ∧ h' = h) ∧
  (h.mode = .read → size ≠ 0 → ∃ ret, GzReadFn h (size * nitems) bytes ret h' ∧ items = bytes.length / size)

/-- `gzgetc(file)`: a byte (0 to 255) or `-1` at the end or on error. -/
def GzGetc (h : GzHandle) (ret : Int) (h' : GzHandle) : Prop :=
  ∃ bytes r, GzReadFn h 1 bytes r h' ∧ (ret = match bytes with | [b] => (b.toNat : Int) | _ => -1)

/-- `gzungetc(c, file)`: pushes the byte back and returns it; `-1` for `c < 0` or if there is no
room. At least one byte can be pushed back when the pushed-back list is empty. -/
def GzUngetc (h : GzHandle) (c : Int) (ret : Int) (h' : GzHandle) : Prop :=
  (h.mode ≠ .read → ret = -1 ∧ h' = h) ∧
  (h.mode = .read → c < 0 → ret = -1 ∧ h' = h) ∧
  (h.mode = .read → 0 ≤ c → (ret = c ∧ h'.pushed = (c.toNat.toUInt8) :: h.pushed ∧ h'.past = false ∧
      h'.rpos = h.rpos ∧ h'.dec = h.dec ∧ h'.sized = true) ∨
    (h.pushed ≠ [] ∧ ret = -1))

/-- `gzgets(file, buf, len)`: `none` for `NULL`. The line is read up to and including the first
newline, or `len - 1` bytes, or the end. `NULL` if `len < 1`, or nothing was read with `len > 1`. -/
def GzGets (h : GzHandle) (len : Int) (line : Option (List UInt8)) (h' : GzHandle) : Prop :=
  (h.mode ≠ .read ∨ len < 1 → line = none ∧ h' = h) ∧
  (h.mode = .read → 1 ≤ len →
    ∃ bytes, line = (if bytes = [] ∧ len > 1 then none else some bytes) ∧
      bytes <+: h.avail ∧ bytes.length ≤ len.toNat - 1 ∧
      (∀ b, b ∈ bytes.dropLast → b ≠ 10) ∧
      (bytes.getLast? = some 10 ∨ bytes.length = len.toNat - 1 ∨ bytes = h.avail) ∧
      h'.pushed = h.pushed.drop bytes.length ∧
      h'.rpos = h.rpos + (bytes.length - min bytes.length h.pushed.length) ∧ h'.dec = h.dec)

/-- `gzeof(file)`: true iff a read came up short (the read position is at the end and a read
tried to go past it); false for a writer. -/
def GzEof (h : GzHandle) (ret : Int) : Prop :=
  ret = (if h.mode = .read ∧ h.past = true then 1 else 0)

/-- `gzerror(file, &errnum)`: the code. It is `Z_OK` for a handle on which nothing failed. -/
def GzError (h : GzHandle) (code : Int) : Prop := code = h.err

/-- `gzclearerr(file)`: no error, no end-of-file indicator. -/
def GzClearerr (h : GzHandle) (h' : GzHandle) : Prop :=
  h' = { h with err := Z.ok, past := false }

/-- `gzrewind(file)`: reader without a serious error: back to position 0 (`0`), else `-1`. -/
def GzRewind (h : GzHandle) (ret : Int) (h' : GzHandle) : Prop :=
  (h.mode = .read ∧ (h.err = Z.ok ∨ h.err = Z.bufError) ∧
    ((ret = 0 ∧ h' = { h with rpos := 0, pushed := [], past := false, err := Z.ok }) ∨
     (ret = -1 ∧ h' = h))) ∨
  ((h.mode ≠ .read ∨ (h.err ≠ Z.ok ∧ h.err ≠ Z.bufError)) ∧ ret = -1 ∧ h' = h)

/-- `gzseek(file, offset, whence)`: `whence` 0 (`SEEK_SET`) or 1 (`SEEK_CUR`; relative to `gztell`);
anything else, a serious error, or a position before the start is `-1`. The new position is
returned, **but `gztell` need not agree with it**. A reader may seek anywhere forward (the skipping is
done by the next read); a writer only forward (zeros fill the gap).

For a reader (`gzseek64`):
* in the copying mode (`CopyMode`) the file is repositioned: nothing pushed back, `past` and the
  error are cleared, and `gztell` is the position;
* a backward seek rewinds the file and then skips: the same (nothing pushed back, `past` and the
  error cleared);
* a forward seek of `d` bytes in the decoding mode first consumes pushed-back bytes, and skips
  the rest later (`rpos` is the virtual position). It does **not** clear `past`: if a read has
  come up short before, `gzeof` stays 1 and `gztell` still reports the end of the data, not the new
  position (`gztell64` ignores the skip while `past` is set). `gzseek` returned the new
  position anyway. This was seen on the real library (a quirk, not undefined behaviour). -/
def GzSeek (h : GzHandle) (off whence : Int) (ret : Int) (h' : GzHandle) : Prop :=
  let cur : Int := if h.mode = .read then h.tell else (h.written.length : Int)
  let target : Int := (if whence = 0 then 0 else cur) + off
  let d : Nat := (target - cur).toNat
  let bad := (h.err ≠ Z.ok ∧ h.err ≠ Z.bufError) ∨ (whence ≠ 0 ∧ whence ≠ 1) ∨
    target < 0 ∨ (h.mode = .write ∧ target < cur)
  (bad → ret = -1 ∧ h' = h) ∧
  (¬ bad →
    (ret = -1 ∧ h.mode = .read) ∨
    (ret = target ∧
      (h.mode = .write → h'.written = h.written ++ List.replicate d 0) ∧
      (h.mode = .read → h'.dec = h.dec ∧ h'.sized = h.sized ∧
        ((h.CopyMode ∨ target < cur) →
          h'.pushed = [] ∧ h'.past = false ∧ h'.err = Z.ok ∧ h'.rpos = target.toNat) ∧
        (¬ h.CopyMode → cur ≤ target →
          h'.past = h.past ∧ h'.err = h.err ∧ h'.pushed = h.pushed.drop d ∧
          h'.rpos = h.rpos + (d - min d h.pushed.length)))))

/-- `gztell(file)`: the uncompressed position: bytes read (reader) or written, zeros of seeks
included (writer); the append handle counts the bytes written. -/
def GzTell (h : GzHandle) (ret : Int) : Prop :=
  ret = (if h.mode = .read then h.tell else (h.written.length : Int))

/-- `gzoffset(file)`: the position in the compressed file (`lseek` of the descriptor, less the
input not yet used by a reader), or `-1` if it is unknown. It is not bounded by the size of the
content: the descriptor of `gzdopen` may start at a position other than 0, and in the copying mode
a seek beyond the end moves the descriptor beyond the end (seen on the real library: 100 for a file
of 5 bytes). -/
def GzOffset (_h : GzHandle) (ret : Int) : Prop :=
  ret = -1 ∨ 0 ≤ ret

/-! ## Writing -/

/-- The compressed bytes of a writer are a growing prefix of one gzip member (or, for a
transparent writer, the data itself). -/
def GzHandle.OutGrows (h h' : GzHandle) : Prop :=
  h.out <+: h'.out ∧ h'.base = h.base ∧ h'.mode = h.mode ∧ h'.direct = h.direct

/-- Writing `s` succeeded or failed. On success `written` grows by `s`; on a failure of the file
the handle is marked `failed`, `err` is `Z_ERRNO` and nothing is promised about the data. -/
def GzWriteBytes (h : GzHandle) (s : List UInt8) (ok : Bool) (h' : GzHandle) : Prop :=
  h.OutGrows h' ∧ h'.sized = true ∧ h'.level = h.level ∧ h'.strategy = h.strategy ∧
  (if ok then h'.written = h.written ++ s ∧ h'.err = Z.ok ∧ h'.failed = h.failed
   else h'.failed = true ∧ h'.err = Z.errno)

/-- `gzwrite(file, buf, len)`: returns `len` (or 0 if `len = 0`); 0 for a reader, after a serious
error, for `len > 2^31 - 1`, or if the file failed. -/
def GzWrite (h : GzHandle) (s : List UInt8) (ret : Int) (h' : GzHandle) : Prop :=
  ((h.mode = .read ∨ h.err ≠ Z.ok) → ret = 0 ∧ h' = h) ∧
  (¬ (h.mode = .read ∨ h.err ≠ Z.ok) →
    (s.length > 2 ^ 31 - 1 → ret = 0 ∧ h'.err = Z.dataError ∧ h'.written = h.written) ∧
    (s.length ≤ 2 ^ 31 - 1 →
      ((ret = s.length ∧ GzWriteBytes h s true h') ∨ (ret = 0 ∧ GzWriteBytes h s false h'))))

/-- `gzputc(file, c)`: returns `c` mod 256, or `-1`. -/
def GzPutc (h : GzHandle) (c : Int) (ret : Int) (h' : GzHandle) : Prop :=
  ((h.mode = .read ∨ h.err ≠ Z.ok) → ret = -1 ∧ h' = h) ∧
  (¬ (h.mode = .read ∨ h.err ≠ Z.ok) →
    ((ret = c % 256 ∧ GzWriteBytes h [(c % 256).toNat.toUInt8] true h') ∨
     (ret = -1 ∧ GzWriteBytes h [(c % 256).toNat.toUInt8] false h')))

/-- `gzputs(file, s)`: `s` has no zero byte. Returns the length of `s`, or `-1`. -/
def GzPuts (h : GzHandle) (s : List UInt8) (ret : Int) (h' : GzHandle) : Prop :=
  ((h.mode = .read ∨ h.err ≠ Z.ok) → ret = -1 ∧ h' = h) ∧
  (¬ (h.mode = .read ∨ h.err ≠ Z.ok) →
    ((ret = s.length ∧ GzWriteBytes h s true h') ∨ (ret = -1 ∧ GzWriteBytes h s false h')))

/-- `gzprintf(file, format, ...)`: `s` is the formatted output. It is written only if it is not
empty and shorter than the buffer (`want`); otherwise 0 is returned and nothing is written. -/
def GzPrintf (h : GzHandle) (s : List UInt8) (ret : Int) (h' : GzHandle) : Prop :=
  ((h.mode = .read ∨ h.err ≠ Z.ok ∨ s = [] ∨ s.length ≥ h.want) → ret = 0 ∧ h.written = h'.written) ∧
  (¬ (h.mode = .read ∨ h.err ≠ Z.ok ∨ s = [] ∨ s.length ≥ h.want) →
    ((ret = s.length ∧ GzWriteBytes h s true h') ∨ (ret = 0 ∧ GzWriteBytes h s false h')))

/-- `gzfwrite(buf, size, nitems, file)`: writes `size * nitems` bytes; returns the number of
items written. -/
def GzFwrite (h : GzHandle) (size : Nat) (s : List UInt8) (items : Nat) (h' : GzHandle) : Prop :=
  (size = 0 → items = 0 ∧ h' = h) ∧
  (size ≠ 0 → s.length % size = 0 ∧ ∃ ret, GzWrite h s ret h' ∧ items = ret.toNat / size)

/-- `gzsetparams(file, level, strategy)`: for a writer, `Z_OK` (the new level and strategy are
used from then on; the data written is unaffected) or an error code; `Z_STREAM_ERROR` for a
reader. -/
def GzSetParams (h : GzHandle) (_level _strategy : Int) (rc : Int) (h' : GzHandle) : Prop :=
  if h.mode = .read ∨ h.err ≠ Z.ok then rc = Z.streamError ∧ h' = h
  else
    (rc = Z.ok ∧ h'.written = h.written ∧ h.OutGrows h') ∨
    (rc = Z.streamError ∧ h' = h) ∨
    (rc = Z.errno ∧ h'.failed = true ∧ h'.err = Z.errno)

/-- `gzflush(file, flush)`: `flush` is one of `Z_NO_FLUSH` .. `Z_FINISH` (0 to 4), else
`Z_STREAM_ERROR`. After `Z_FINISH` the member is ended and later writes are lost, so the model marks the handle `failed` (no data promise remains). After `Z_OK` with `Z_SYNC_FLUSH` or `Z_FULL_FLUSH` all the data written is in the
file, on a byte boundary: the bytes handed to the file so far plus `closer` are a gzip member of
exactly what was written (`F-deflate-flush`). -/
def GzFlush (h : GzHandle) (flush : Int) (rc : Int) (h' : GzHandle) : Prop :=
  if h.mode ≠ .write ∨ h.err ≠ Z.ok then rc = Z.streamError ∧ h' = h
  else if flush < 0 ∨ flush > 4 then rc = Z.streamError ∧ h' = h
  else
    (rc = Z.ok ∧ h.OutGrows h' ∧ h'.written = h.written ∧ h'.failed = h.failed ∧ h'.sized = true ∧
      ((flush = 2 ∨ flush = 3) → h.failed = false → h.direct ≠ 1 →
        Gzip.Decodes (h'.out ++ closer .gzip h.written) h.written) ∧
      (flush = 4 → h'.failed = true)) ∨
    (rc = Z.errno ∧ h.OutGrows h' ∧ h'.failed = true ∧ h'.err = Z.errno)

/-- `gzclose(file)` / `gzclose_r` / `gzclose_w`: the handle ends. Result: `Z_OK`; or for a reader
`Z_BUF_ERROR` if the file was truncated and read to its end; or `Z_ERRNO` for a writer or reader
whose file failed. The content of the file after closing a writer: for a gzip writer that did
not fail, `base` followed by one gzip member that decodes to exactly what was written (an
empty file for nothing written is a member of no data), so that `GzDecoded` gives it back
(`C7`); for a transparent writer, `base` followed by the data. `final` is that content. -/
def GzClose (h : GzHandle) (rc : Int) (final : List UInt8) : Prop :=
  (rc = Z.ok ∨ rc = Z.bufError ∨ rc = Z.errno) ∧
  (h.mode = .read → rc = Z.bufError ∨ rc = Z.ok ∨ rc = Z.errno) ∧
  (h.mode ≠ .read → h.failed = false → rc = Z.errno ∨ rc = Z.ok) ∧
  (h.mode ≠ .read → h.failed = false → rc = Z.ok →
    (h.direct = 1 → final = h.base ++ h.written) ∧
    (h.direct ≠ 1 → ∃ m, final = h.base ++ m ∧ h.out <+: m ∧ Gzip.Decodes m h.written))

end ZlibF.Spec.Api
