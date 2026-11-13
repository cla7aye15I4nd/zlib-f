# Report: out-of-bounds read in `longest_match` after `deflateResetKeep` and `deflateCopy`

Draft for the zlib maintainers, written for the project owner. Not sent; kept as a record.

For this project `deflateResetKeep` is an internal step of `deflateReset`: zlib.h declares it not
part of the zlib API, so the proved deflate domain excludes direct calls, and no further work is
planned on this finding.

## Summary

On zlib `develop` at commit `757f0527` (`ZLIB_VERSION "1.3.2.1-motley"`), a sequence of exported
calls with valid buffers makes `longest_match` read outside the window. The root cause is a read
of an uninitialised `prev` entry in a stream made by `deflateCopy`. AddressSanitizer reports
`heap-buffer-overflow READ of size 1` at `deflate.c:1511`.

The sequence needs a direct call of `deflateResetKeep`. `zlib.h` declares that function under
`/* undocumented functions (not part of the zlib API) */`: it is exported, but not part of the zlib
API. So this is not a bug of the documented API. It is a memory error that an exported, undocumented
function makes reachable, and it appeared with two recent changes (see Affected releases). Inside the
documented API we found no such sequence, and for our proved domain we show there is none (see
Relation to the proofs).

Confirmed on x86_64 Linux (GCC 14) with AddressSanitizer and with valgrind, and on arm64 macOS. It
affects zlib 1.4 and `develop`, not 1.3.1 or 1.3.2.

## Affected code

- `deflateResetKeep` (`deflate.c:644`) keeps the window and the hash and sets `lookahead = 0`
  ("Keep the window and the hash, but drop what was left unfinished").
- `deflateCopy` (`deflate.c:1383`) copies `prev` only below `strstart - insert`:

  ```c
  zmemcpy(ds->prev, ss->prev,
          (ss->slid || ss->strstart - ss->insert > ds->w_size ? ds->w_size :
              ss->strstart - ss->insert) * sizeof(Pos));
  ```

- `deflate_rle` (`deflate.c:2177`) and `deflate_huff` end with `s->insert = 0`.

## Affected releases

Both ingredients are recent changes, and the sequence needs both:

- `deflateCopy` copies `prev` only below the frontier since commit 8404590 ("Copy only the
  initialized deflate state in deflateCopy", 2026-01-10), first released in 1.3.2. 1.3.1 copies all
  `w_size` entries.
- `deflateResetKeep` drops the lookahead since commit 1e4178b ("Fix deflateResetKeep() when used in
  the middle of a stream", 2026-11-02), first released in 1.4. Before it, `deflate(Z_BLOCK)` after
  `deflateResetKeep` compresses the kept lookahead and leaves no head waiting for insertion.

The reproduction reports the read on 1.4 and on `develop` (757f0527), and nothing on 1.3.1 or 1.3.2
(AddressSanitizer, arm64 macOS, the same driver).

## Mechanism

1. A stream compresses some input without flushing. The positions `strstart - 2` and
   `strstart - 1` are inserted in the hash and are chain heads.
2. `deflateResetKeep` drops the lookahead and keeps the hash. The two positions stay chain heads.
3. `deflate(Z_BLOCK)` with no input sets `insert = 2`. The two positions now count as waiting for
   insertion, although the hash already holds them.
4. `deflateCopy` copies `prev` only below `strstart - insert`. In the copy, the `prev` entries of
   the two heads are never written.
5. On the copy, `deflateParams(Z_RLE)` and `deflate(Z_SYNC_FLUSH)` with no input run
   `deflate_rle`, which sets `insert = 0`. `fill_window` re-inserts waiting positions only while
   `insert` is nonzero, so the two entries stay unwritten.
6. On the copy, `deflateParams(Z_DEFAULT_STRATEGY)` and then input that starts with the three bytes
   at `strstart - 2`. `deflate_slow` inserts `strstart` under the same key and calls
   `longest_match` on the old head. The chain walk reads the unwritten `prev` entry as the next
   candidate and compares window bytes at that position.

The candidate is whatever the entry holds, up to 65535. With a small window (`windowBits` 9, 1024
bytes) most values lie outside the window allocation.

## Reproduction

[`deflate-copy-pending-prev/repro.c`](deflate-copy-pending-prev/repro.c) in this directory; the same
driver with a runner is [`tests/regression/deflate-copy-pending-prev`](../../tests/regression/deflate-copy-pending-prev/README.md).
It includes `deflate.h` only to read `strstart` and three window bytes for step 6 and to print state.
It installs an allocator that fills fresh memory with the 16-bit value 1030, which makes the
candidate deterministic; with the argument `plain` it uses the default allocator.

Build the pinned sources with `-fsanitize=address,undefined -g -O1` and run:

```
==ERROR: AddressSanitizer: heap-buffer-overflow ... READ of size 1
    #0 longest_match deflate.c:1511
    #1 deflate_slow deflate.c:2029
    #2 deflate deflate.c:1239
... is located 7 bytes after 1026-byte region ... allocated by ... deflateCopy deflate.c:1361
```

Observed:

| Variant | Platform | Result |
| --- | --- | --- |
| `repro.c` as written, ASan and UBSan | x86_64 Linux, GCC 14 | heap-buffer-overflow READ of size 1 at `deflate.c:1511`, 7 bytes after the 1026-byte window block allocated in `deflateCopy` (`deflate.c:1361`) |
| `repro plain` (default allocator), no sanitizer, valgrind `--track-origins=yes` | x86_64 Linux, GCC 14 | "Conditional jump or move depends on uninitialised value(s)" in `longest_match` (`deflate.c:1555`, the loop test on the next candidate), by `deflate_slow` (`deflate.c:2029`); the value comes from the `prev` allocation of `deflateCopy` (`deflate.c:1362`) |
| `repro.c` as written | arm64 macOS, Apple clang 21 | heap-buffer-overflow at `deflate.c:1511` |
| Default allocator | arm64 macOS, Apple clang 21 | the same report |
| `deflateCopy` changed to copy `w_size` entries of `prev` | arm64 macOS, Apple clang 21 | no report; `deflate` returns `Z_STREAM_END` |
| zlib 1.3.1, 1.3.2 | arm64 macOS, Apple clang 21 | no report |
| zlib 1.4 | arm64 macOS, Apple clang 21 | heap-buffer-overflow at `deflate.c:1511` |

The Linux output is [`report.txt`](../../tests/regression/deflate-copy-pending-prev/report.txt).
MemorySanitizer was not run; valgrind reports the uninitialised read. Without a sanitizer the read
may land inside mapped memory and show nothing.

## Impact

- A read of uninitialised memory, then a read of up to 258 bytes at an offset of up to 65535 from
  the window start. No write was observed.
- The compressed output may depend on the bytes read.
- It needs the caller to call `deflateResetKeep` directly, then `deflateCopy`, then change the
  strategy on the copy. An attacker who controls only the data being compressed cannot trigger it.

## Possible fixes

Each is a suggestion. Only the first was tried, on the one reproduction above.

1. In `deflateCopy`, copy all `w_size` entries of `prev`.
2. In `deflateResetKeep`, clear the hash (`CLEAR_HASH`), so no head refers to a position that will
   be inserted again. This also removes the stale-hash data error in
   `deflate-resetkeep-stale-hash`.
3. Leave the code: `zlib.h` already declares `deflateResetKeep` not part of the zlib API. A note
   there that it must not be combined with `deflateCopy`, or not exporting it, would make that
   explicit.

## Relation to the proofs

The deflate safety theorems exclude a direct `deflateResetKeep` call from the stream domain
(`docs/deviations.md`). This is not a narrowing below `zlib.h`, which declares the function not part
of the zlib API, and this report is a reason the exclusion cannot be removed.

For histories without that call, no chain head waits for insertion, so the partial copy of `prev`
in `deflateCopy` copies every entry a chain walk can reach. This is a theorem:
`DInv.heads_inserted` (and `DInv.slid_heads_inserted` for one pending slide at level 0,
`ZlibF/Proof/deflate.c.universal-heads.lean`) states that every nonzero `head` entry is below
`strstart - insert` in every state that satisfies the deflate invariant `DInv`. `DInv` holds after
every history of the stream domain (`reachable_inv`, under the hypotheses of
`Goal.deflate_sequence_safety`). The real-C checker of the project agrees on 4.6 million sampled
states (evidence, not proof).
