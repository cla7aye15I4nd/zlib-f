# Sanitizer reports

This page lists every retained reproduction in which a sanitizer reports undefined behaviour or a
memory error in the real C. Each one has a directory with a runner, the C driver and the raw
sanitizer output in `report.txt`.

## What these are

The rows of the main table are caller-side layouts and call orders. A program that calls zlib
has to build them on purpose: it points a header buffer into its own input or output, edits
the header record while zlib writes it, calls a function after the point zlib.h allows, or
passes `NULL` for a length cell. They are not inputs an attacker controls. No compressed byte
stream reaches any of them.

Each row is outside the proved domain: a named premise of a public goal excludes it. Where
zlib.h is silent about the layout, the premise is listed in [deviations](deviations.md).

None of these rows was reported upstream. The library defects are in the section "Library
defects": upstream has fixed one; two have a fix submitted upstream that the maintainer has not
yet confirmed; two have a local candidate fix that is not yet submitted.

## Caller layouts outside the proved domain

The verdicts come from the pinned source with the repository patches, built with
AddressSanitizer and UndefinedBehaviorSanitizer on x86_64 Linux, the project's target. Source
lines are those of the pinned source. An earlier run on arm64 macOS gave the same verdicts, with
one difference noted in the row `late deflatePrime`.

| Name | Caller layout or call sequence | Sanitizer verdict | Excluded by | Reproduction | zlib.h |
| --- | --- | --- | --- | --- | --- |
| inflate extra overlap | gzip `inflate`; `head->extra` points into the input buffer and overlaps the extra field being read | `memcpy-param-overlap`, `inflate.c:626` | `InflateHeaderProgress` (extra buffer separate from the unread input), a conjunct of `ActiveHeader`: premise of `Goal.inflate` and `Goal.inflate_sequence` | [inflate-gzip-extra](../tests/regression/inflate-gzip-extra/README.md), `overlap.c`, [report](../tests/regression/inflate-gzip-extra/report.txt) | Silent |
| inflate extra shrink | `extra_max` is `2^32 - 1`; the first `inflate` stops inside the extra field; the caller sets `head->extra_len` to 0; `inflate` | `heap-buffer-overflow` WRITE of size 4, `inflate.c:626` | `InflateHeaderProgress` (in `EXTRA`, `extra_len` is not below `state->length`): premise of `Goal.inflate` and `Goal.inflate_sequence` | [inflate-gzip-extra](../tests/regression/inflate-gzip-extra/README.md), `shrink.c`, [report](../tests/regression/inflate-gzip-extra/report.txt) | Silent |
| deflate name in output | gzip `deflate`, `memLevel` 1; `head->name` is the caller's output buffer | `heap-buffer-overflow` READ of size 1, `deflate.c:1177` | `DeflateHeaderApart` (name separate from the output range), a conjunct of `ActiveHeader`: premise of `Goal.deflate` and `Goal.deflate_sequence` | [deflate-gzip-name-output](../tests/regression/deflate-gzip-name-output/README.md), `output.c`, [report](../tests/regression/deflate-gzip-name-output/report.txt) | Silent |
| deflate name in pending buffer | gzip `deflate`; `head->name` points into the stream's own `pending_buf` | `heap-buffer-overflow` READ of size 1, `deflate.c:1177` | `DeflateHeaderApart` (name outside the storage the stream owns): premise of `Goal.deflate` and `Goal.deflate_sequence` | [deflate-gzip-name-output](../tests/regression/deflate-gzip-name-output/README.md), `pending.c`, [report](../tests/regression/deflate-gzip-name-output/report.txt) | Silent |
| late deflatePrime | raw, `memLevel` 1; `deflate(Z_NO_FLUSH)` records symbols; 200 calls of `deflatePrime(16)`; `deflate(Z_FINISH)` | UBSan: index 767 out of bounds for `_dist_code[512]`, `trees.c:930`. On arm64 macOS UBSan then also reports a signed left-shift overflow, `trees.c:937`; on x86_64 Linux it does not, since the byte read out of bounds differs | `DeflateNotStarted`, which `StreamArguments` requires of `deflatePrime`: the history is not `StreamReachable`, so it is outside `Goal.deflate` and `Goal.deflate_sequence` | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md), `prime.c`, [report](../tests/regression/deflate-history-domain/report.txt) | Excludes it: `deflatePrime` "must be used before the first deflate() call" |
| late deflateSetHeader(NULL) | gzip, `memLevel` 1, 2000-byte extra field; the first `deflate` stops inside it; `deflateSetHeader(strm, NULL)`; `deflate` | UBSan: member access within null pointer, `deflate.c:1137`; then ASan `SEGV` on a READ, `deflate.c:1137` | `DeflateNotStarted`, which `StreamArguments` requires of `deflateSetHeader`: outside `Goal.deflate` and `Goal.deflate_sequence` | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md), `header.c 1`, [report](../tests/regression/deflate-history-domain/report.txt) | Excludes it: `deflateSetHeader` "may be called ... before the first call of deflate()" |
| deflate extra shrink | the same start; the caller sets `extra_len` to 10, below the 500 bytes written; `deflate` | `heap-buffer-overflow` READ of size 512, `deflate.c:1142` | `DeflateHeaderProgress` (the field still covers `gzindex`), a conjunct of `ActiveHeader`: premise of `Goal.deflate` and `Goal.deflate_sequence` | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md), `header.c 2`, [report](../tests/regression/deflate-history-domain/report.txt) | Silent on edits while the header is written |
| deflate extra cleared | gzip, `memLevel` 1, 1500-byte extra field, 3-byte name; the first `deflate` stops inside the extra field; the caller sets `extra` to `NULL`; `deflate` | `heap-buffer-overflow` READ of size 1, `deflate.c:1177`, 496 bytes after the name | `DeflateHeaderProgress` (`gzindex` is 0 when the field is `NULL`): premise of `Goal.deflate` and `Goal.deflate_sequence` | [deflate-history-domain](../tests/regression/deflate-history-domain/README.md), `clear.c`, [report](../tests/regression/deflate-history-domain/report.txt) | Silent on edits while the header is written |
| compress null length | `compress2(dest, NULL, source, 1, 6)` and `compress(dest, NULL, source, 1)` | UBSan: load of null pointer of type `uLongf`, `compress.c:70` | `CompressorContract` with a nonnull length cell (`capacity ≠ none`): premise of `Goal.compress2` and `Goal.compress` | [compress-allocation](../tests/regression/compress-allocation/README.md), `ubwitness.c`, [report](../tests/regression/compress-allocation/report.txt) | Describes `destLen` as the buffer size on entry; does not mention `NULL` |

For `compress null length`, `report.txt` holds only the witness step of `run.sh`. The rest of
that runner is a Lean comparison with no sanitizer report.

## Call sequence of exported functions, outside the proved domain

Unlike the rows above, this is not a caller layout: every buffer is valid and separate, and every
call is to an exported function. The sequence uses `deflateResetKeep`, which zlib.h lists among the
undocumented functions and the deflate stream domain excludes. Verdicts from the pinned, unmodified
source on x86_64 Linux; the same AddressSanitizer report on arm64 macOS.

| Name | Call sequence | Sanitizer verdict | Excluded by | Reproduction | zlib.h |
| --- | --- | --- | --- | --- | --- |
| deflateCopy after deflateResetKeep | `windowBits` 9; `deflate(Z_NO_FLUSH)`; `deflateResetKeep`; `deflate(Z_BLOCK)`; `deflateCopy`; on the copy `deflateParams(Z_RLE)`, `deflate(Z_SYNC_FLUSH)` with no input, `deflateParams(Z_DEFAULT_STRATEGY)`, `deflate` on input that starts with the bytes at `strstart - 2` | ASan `heap-buffer-overflow` READ of size 1, `deflate.c:1511` (`longest_match`), with fresh memory filled by the allocator; with the default allocator, valgrind: conditional jump on an uninitialised value, `deflate.c:1555`, created by the `prev` allocation of `deflateCopy` | No direct `deflateResetKeep` in a deflate call history (`StreamOperation .deflate`, [deviations](deviations.md)) | [deflate-copy-pending-prev](../tests/regression/deflate-copy-pending-prev/README.md), `copy.c`, [report](../tests/regression/deflate-copy-pending-prev/report.txt); analysis in [findings](findings/deflate-copy-pending-prev/README.md); [report draft](findings/deflate-copy-pending-prev-report.md), not sent | Lists `deflateResetKeep` among the undocumented functions |

## Library defects

| Name | Call sequence | Sanitizer verdict | Status | Reproduction |
| --- | --- | --- | --- | --- |
| inflateCopy fixed table | default `inflateInit`; `inflate` stops inside a fixed block; `inflateCopy` | `invalid-pointer-pair`, `inflate.c:1383`, between the static `lenfix` and the inflate state | A zlib defect inside the documented use. Fixed upstream ([PR #1369](https://github.com/madler/zlib/pull/1369)); the verified source applies that fix as a temporary patch | [inflate-copy-fixed](findings/inflate-copy-fixed/README.md), [report](findings/inflate-copy-fixed/report.txt) |
| gzseek after initial gzungetc | `gzopen`; `gzungetc` at position 0 (`x.pos` becomes -1); `gzseek(f, 1, SEEK_CUR)`, or on another handle `gzseek(f, LONG_MAX, SEEK_SET)`; transparent and gzip input | UBSan: signed integer overflow, `gzlib.c:395` (`SEEK_CUR`), `gzlib.c:403` (`SEEK_SET`, transparent), `gzlib.c:424` (`SEEK_SET`, gzip) | A zlib defect inside the documented use. Fix submitted upstream ([PR #1361](https://github.com/madler/zlib/pull/1361)), not yet confirmed by the maintainer; the verified source applies it as a temporary patch | [gzseek-pushback-overflow](../tests/regression/gzseek-pushback-overflow/README.md), `seek.c`, [report](../tests/regression/gzseek-pushback-overflow/report.txt) |
| gzread stale next after partial read | transparent `gzopen`, `gzbuffer(f, 16)`; 48 `gzgetc` on a 128-byte file; `read()` returns 1 byte, then fails with `EIO`; `gzread(f, buf, 1)` | `heap-buffer-overflow` READ of size 1, `gzread.c:369` (`gz_read`), 0 bytes after the 32-byte output buffer | A zlib defect inside the documented use. Fix submitted upstream ([PR #1363](https://github.com/madler/zlib/pull/1363)), not yet confirmed by the maintainer; the verified source applies it as a temporary patch | [gzread-transparent-stale-next](../tests/regression/gzread-transparent-stale-next/README.md), `stale.c`, [report](../tests/regression/gzread-transparent-stale-next/report.txt) |
| gzread position overflow (F-1) | x86_64 Linux: `gzdopen(open("/dev/zero"), "r")`; `gzread(f, buf, 1)` (transparent); `gzseek(f, INT64_MAX, SEEK_SET)`, accepted because `lseek` on the device returns 0; `gzread(f, buf, 16)`. Also: seek to `INT64_MAX - 4`, `gzread` 1 byte, four `gzgetc()` | UBSan: signed integer overflow, `gzread.c:414` (`gz_read`, `x.pos += n`); in the second history in the `gzgetc()` macro in the caller | A zlib defect inside the documented use. Candidate fix, not yet submitted: the local patch 0004, approved by the owner on 2026-11-12 | [gzread-pos-overflow](../tests/regression/gzread-pos-overflow/README.md), `devzero.c`, [report](../tests/regression/gzread-pos-overflow/report.txt); [finding](findings/gzread-pos-overflow/README.md) |
| gzwrite position overflow (W7) | `gzdopen(open("/dev/null"), "wT")`; `gzbuffer(f, 2^29)`; `gzseek(f, INT64_MAX - 10, SEEK_SET)`; `gzwrite(f, buf, 100)` (the zero fill takes 17 minutes). Also: seek to `INT64_MAX`, `gzputc` | UBSan: signed integer overflow, `gzwrite.c:230` (`gz_write`, `x.pos += copy`); `gzwrite.c:352` (`gzputc`) | A zlib defect inside the documented use. Candidate fix, not yet submitted: the local patch 0004, approved by the owner on 2026-11-12 | [gzwrite-pos-overflow](../tests/regression/gzwrite-pos-overflow/README.md), `wpos.c`, [report](../tests/regression/gzwrite-pos-overflow/report.txt); [finding](findings/gzwrite-pos-overflow/README.md) |

These reproductions build the source without the fix on purpose; the gz runners also build it
with the fix and check that the report is gone. The F-1 and W7 reports come from x86_64 Linux
(kernel 7.0, gcc 15.2); the reports of the gzseek after gzungetc and the stale `x.next` come from
arm64 macOS (Apple clang 21), and the defects they show do not depend on the target.

## Clean runs, kept as evidence that a layout is defined

These runs use the same sanitizers and report nothing. They show that a layout is defined C,
so the proofs must cover it.

- [inflate-shared-block](../tests/regression/inflate-shared-block/README.md): the input and
  output ranges lie in one heap block, in both orders. Inside `StreamBuffers`.
- [inflate-gzip-flags-prime](../tests/regression/inflate-gzip-flags-prime/README.md):
  `inflatePrime` on a gzip stream in `FLAGS` makes the flags word 65544. This is defined,
  though zlib.h says `inflatePrime` "should only be used with raw inflate".

## Not listed

- [deflate-slide](../tests/regression/deflate-slide/README.md): UBSan reports a signed overflow
  in an artificial internal state that no call sequence is shown to reach. It tests the
  translation's overflow fault, not a caller layout.
- Differential regressions whose sanitizer builds must stay silent: `inflate-copy`,
  `inflate-deferred-distance`, `inflate-prime`, `trees-depth-read`, `crc-byte-views`.
- The data error in [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md),
  which no sanitizer reports.

## Adding a reproduction

A new sanitizer reproduction goes under `tests/regression/<name>/` with `run.sh`, `report.txt`
and a row on this page. `report.txt` holds the raw output, with process ids replaced and paths
made relative to the repository or the zlib root.
