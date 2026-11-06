# Migrating the proofs of `gzlib.c` and `gzclose.c`

The earlier attempt proved the functions of `gzlib.c` in about 9,300 lines (48 files) and `gzclose.c` in about 800 lines
(8 files), on a memory made of byte blocks and untyped cells, with a "typed view" of the `gz_state` that every lemma had to
rebuild. Now the `gz_state` is a record in a table and a field access is a projection, so no old proof text can be
pasted; the arguments are kept and the statements are re-stated. This note says what each old family of theorems states,
whether it is pure or depends on memory, and in which order it is re-proved.

## 1. What each old family states

| old family (files) | what it states | kind | now |
| --- | --- | --- | --- |
| field offsets and tags (`Basic`) | where each field of the state lives, which type a cell has | memory model only | not needed: a record |
| `gzbuffer`, `gzeof`, `gztell64`, `gztell`, `gzerror`, `gz_intmax` (`Simple`) | the result and that nothing changes (`gzbuffer` stores `want`) | memory, small | done (`gzlib.c.simple`) |
| `gz_error` without and with a message (`Error`, `ErrorMsg`) | the old message is freed, the code recorded; with a message a block of the size of path plus text plus 3 is made and filled with "path: text"; a failed allocation gives the out-of-memory code | memory, then the printf model | no message done (`gzlib.c.error`); with message waits for the printf lemma |
| `gz_reset`, `gzclearerr` (`Reset`, `Rewind`) | the fields `gz_reset` writes, the message freed, the invariant kept | memory | done (`gzlib.c.error`, `gzlib.c.simple`) |
| `gzrewind`, `gzoffset64`, `gzoffset` (`Rewind`) | refusal rules, the call to `lseek`, the reset; the offset less the unused input | memory and file | done (`gzlib.c.rewind`) |
| position arithmetic of `gzseek64` (`SeekParts`, `SeekRaw`, `SeekFwd`, `SeekBack`, `SeekTail`, `SeekMain`, `SeekCor`) | the target, the refusal range, the three cases: raw area, forward, backward; the numbers n, skip, pos | pure core inside a memory statement | done (`gzlib.c.seek`), split into a head (checks) and tails |
| negative position and overflow (`SeekNeg`, `SeekNegUb`, `SeekFault`, `SeekWitness`) | the unpatched C overflows after an initial `gzungetc`; with the earlier patch it refuses | pure arithmetic | done as exact fault theorems on the unpatched translation |
| `gz_open` mode loop (`OpenMode`, `OpenParts`, `OpenRest`) | the loop is the fold of the characters; `+` frees the state | pure fold plus loop rule | definitions done (`parseMode`, `gzlib.c.open` in progress) |
| `gz_open` path copy, descriptor, finish (`OpenPath`, `OpenDesc`, `OpenFinish`, `Open*`, `OpenEff*`, `GzopenEff*`, `Dopen*`) | the path block holds the path, `open` flags, the file effects (creation, truncation, append position), failure frees everything | memory and file | waits for a printf lemma, see 3 |
| `Sys`, `Issues` | wrappers of `open`/`fcntl`/`lseek`; reads of uninitialised cells | old runtime only | dropped: an uninitialised integer is an arbitrary value now |
| `gzclose` (`Close`, `Dispatch`, the rest) | dispatch to the reader or writer close; the live set after | memory | dispatch done (`gzclose.c`); the close of reader and writer belongs to the read and write files |

## 2. Order

The invariant `GzGood` first (`gzlib.c.base`, finished: the record is live, strings and buffers are separate writable
blocks, the message is absent after an out-of-memory error, `Uniq`, `Fresh`), then the field functions, then
`gz_reset`/`gz_error`, then rewind, then seek, then open, then close.

## 3. Results and what waits

* Every function above keeps `GzGood`; the numeric invariant `PosInv` (skip not negative, position plus skip a `z_off64_t`)
  is kept by reset and seek and needed by `gztell64`; `NextOk` (the pointer `x.next` is not dangling and not into the
  message) is a separate hypothesis because a direct read breaks it.
* `gzseek64` is proved safe and exact for states with a position that is not negative. Two exact fault theorems cover the
  unpatched C: `SEEK_CUR` while `gztell` is negative, and `SEEK_SET` with an offset that overflows against a negative
  position. Two more: a dangling `x.next` (the caller freed the buffer of a direct read), and the raw-area seek within
  `2^32` of `2^63`.
* Observation, to confirm: after a read that came up short (`past` set), `gzseek` returns the target but `gztell` reports
  the position of the end, because the translation (like the C) never clears `past` in a forward seek. A run of the
  pinned source (read 5 bytes to the end, `gzseek(f, 5, SEEK_CUR)`) returns 10 and then `gztell` returns 5. The
  specification `GzSeek` (`ZlibF/Spec/Api/Gz.lean`) says the position after a seek is the target and `past` is false, so
  that statement cannot be proved for this case as written.
* Waits: `gz_error` with a message, `gz_open` success, `gzopen`, `gzopen64`, `gzdopen`, and the `errnum` store of `gzerror`.
  The first three call `vsnprintf` with `"%s"`, `"%s%s%s"`, `"<fd:%d>"`; `gzfs.lean` keeps `parseSpec` and `pad` private, so a
  lemma with those formats has to be added there. `gz_open` does not call the inflate or deflate initialisation (that is in
  `gz_look` and `gz_init`), so nothing waits on those.
* Not yet done: witnesses (examples on heaps made by the real functions) and mutants for these modules.
