# Findings in zlib

The idea in short: this page lists behaviour of the pinned zlib that is wrong or undefined, found while writing
the translation, the specification and the function manual. Each entry says how sure we are and where the
reproduction is. The function manual (`docs/spec/functions/`) holds the full programs.

## Confirmed by running the real library

| Name | What happens | Evidence | Scope |
| --- | --- | --- | --- |
| `gzsetparams` ignores a failure | After a write, `deflateParams` can return a buffer error. `gzsetparams` still stores the new level and returns 0, but the stream keeps the old level. Data stays valid. | Run twice, independently: writing 16640 to 16660 random bytes at level 6, then `gzsetparams(f, 0, 0)`, then 200000 zero bytes: the file is compressed (about 16.9 KB) although level 0 was requested. | Public API, normal use |
| `crc32_combine_op` never returns | `crc32_combine_op(a, b, 1UL << 32)` loops forever: the test for zero looks at all 64 bits, the multiplication scans the low 32. | Run twice, independently: killed by a timeout. Operators made by `crc32_combine_gen` never trigger it, so it needs an operator that was not made by the library. | Misuse of an undocumented argument |

## Reproduced by the documentation work, with a sanitizer

These come with a reproduction in the page named in the last column. They are confirmed once a second run has
repeated them; until then treat them as reported.

| Name | What happens | Page |
| --- | --- | --- |
| `gz_fetch` overread | After a partial read followed by a failing read, `gz_read` copies from a stale pointer and reads past the end of its buffer (address sanitizer). | `spec/functions/gz-file.md` |
| `gzseek` after `gzungetc` at position 0 | Signed overflow in `gzlib.c` (undefined behaviour sanitizer); `gztell` returns -1 and a valid seek is refused. | `spec/functions/gz-file.md` |
| Data loss with `gzclearerr` | A failed `gzflush(f, Z_FINISH)`, then `gzclearerr`, more writes and `gzclose`: `gzclose` returns 0 and the file is empty. | `spec/functions/gz-file.md` |
| `inflateCopy` compares unrelated pointers | In `inflateCopy`, a stream stopped inside a fixed block has `lencode` pointing into the static table `lenfix`; the code tests whether it lies inside `codes` with a relational comparison, which is undefined for pointers into different objects. Any `inflateCopy` of such a stream reaches it. The result is the same as an equality test, so the library behaves as intended in practice. | `docs/translation-notes/inflate-side.md` (the analysis ran the address sanitizer's pointer-comparison check); the Lean translation faults on exactly these inputs and the differential test of `inflate` shows 17 such lines |

## Candidates that depend on what the caller may do

`compress2` and `uncompress2` read `*destLen` before the null test that the `_z` functions make;
`deflateCopy(&s, &s)` leaks the old state; `inflateGetHeader(strm, NULL)` dereferences null;
`deflateSetDictionary` adds the dictionary length to `total_in`; `deflatePrime` is accepted where `zlib.h` says it
must not be called; `deflateResetKeep` followed by `deflate` writes a stream that asks for a dictionary. These are
listed under "Findings to confirm" on the pages of the function manual. Only entries that show undefined behaviour or
a wrong result on input that `zlib.h` allows will move up to the tables above.

## Candidates found while writing the API model

| Name | What happens | Evidence | Kind |
| --- | --- | --- | --- |
| `inflate` consumes and produces, then reports `Z_MEM_ERROR` without counting | When `updatewindow` fails to allocate the window at the end of an `inflate` call that wrote output, `inflate` returns `Z_MEM_ERROR` before it updates `total_in`, `total_out` and `adler`. The call has already advanced `next_in`, `avail_in`, `next_out`, `avail_out`, and the output bytes are in the caller's buffer, but the totals still say 0. The stream is then in the `MEM` state. | Real library with a `zalloc` that fails for the window (address and undefined behaviour sanitizers): zlib wrapper, 42 bytes of output room 10: rc -4, 12 bytes read, 10 written, `total_in` 0, `total_out` 0, `adler` 1; raw stream: rc -4, all 28 bytes read, 42 written, totals 0. A later call returns `Z_MEM_ERROR` again; `inflateReset` recovers. | Quirk of the error path (not undefined behaviour). `zlib.h` says only that a stream that returned `Z_MEM_ERROR` is not usable; data that was written may be mistaken for lost |
| `gzseek` forward after the end of the data | After a read came up short (`gzeof` is 1), `gzseek(f, 5, SEEK_CUR)` on a gzip file returns the new position 10 but `gztell` returns 5 and `gzeof` stays 1, because `gzseek` does not clear `past` and `gztell` ignores the pending skip while `past` is set. On a transparent file the same calls give `gztell` 10 and `gzeof` 0. | Real library, 5-byte file written by `gzopen(..., "wb")`; run again by the API model's check | Quirk (not undefined behaviour): `zlib.h` says `gzseek` returns the resulting offset, and `gztell` the current offset |
| `inflate` with a window smaller than 32 KiB rejects valid streams depending on the output splitting | A valid gzip (or zlib or raw) stream with a distance larger than the window is accepted if the output room of the call holds the data before the distance, and refused with `Z_DATA_ERROR` otherwise: the check uses the window plus the output of the current call. | Real library: gzip stream of 20000 bytes, `windowBits` 16 + 8 .. 16 + 13, room 100 per call: `Z_DATA_ERROR`; all room in one call: `Z_STREAM_END` | Documented behaviour of small windows (`zlib.h`: the window must be at least as large as the one used by the compressor), listed because the answer depends on the caller's buffer sizes |

## Not a bug in the library, but a gap that proofs must respect

After `gz_read` decompresses straight into the caller's buffer, `x.next` still points into that buffer; a later
`gzseek` or `gzdirect` adds 0 to it. No sanitizer reports it. The model treats arithmetic on a dangling pointer as
a fault, so a proof about those calls has to rule it out or use the patch proposed in
`docs/translation-notes/gz-side.md`.
