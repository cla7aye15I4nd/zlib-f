# gzread: signed overflow of the position after a seek on a device

Status: confirmed by UndefinedBehaviorSanitizer on x86_64 Linux. Fixed in the verified source by
the local patch [0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch),
approved by the owner on 2026-11-12 and not yet submitted upstream. Write-side twin:
[gzwrite-pos-overflow](../gzwrite-pos-overflow/README.md).

Source pin: `757f0527154291bcf6bfbd6396ecde6bedd2db95`, with patches 0001 to 0003.

## What goes wrong

`state->x.pos` is the position in the uncompressed data, a signed `z_off64_t`. The readers add
the bytes they deliver to it without any bound: `gz_read` (`state->x.pos += n`), `gzgetc`,
`gzgets`, and the `gzgetc()` macro of zlib.h in the caller's code. `gzseek64` checks that the
target fits in `z_off64_t`, so it can set `x.pos` to `GZ_OFF_MAX` itself. In transparent mode
(`how == COPY`) it does so after an `lseek` of the descriptor. On Linux, `lseek` on `/dev/zero`
(also `/dev/urandom`, `/dev/null`) returns 0 and does not fail, whatever the offset, and the device
keeps delivering bytes. The next read then overflows the signed position.

## History

```
fd = open("/dev/zero", O_RDONLY);
f = gzdopen(fd, "r");
gzread(f, buf, 1);                       /* not gzip: transparent copy (COPY) */
gzseek(f, INT64_MAX, SEEK_SET);          /* lseek "succeeds"; x.pos = INT64_MAX */
gzread(f, buf, 16);                      /* x.pos += 16: signed overflow */
```

A second history seeks to `INT64_MAX - 4`, reads one byte with `gzread`, then three with the
`gzgetc()` macro; the fourth `gzgetc()` overflows in the macro, in the caller's code, because
`gz_read` filled the whole output buffer beyond the representable position.

Every call is inside the documented use: zlib.h allows `gzdopen` on any descriptor, a seek to
any position that fits in the offset type, and reads after it.

## Evidence

UndefinedBehaviorSanitizer, x86_64 Linux (kernel 7.0, gcc 15.2), source with patches 0001 to 0003:

```
gzread.c:414:22: runtime error: signed integer overflow: 9223372036854775807 + 16 cannot be represented in type 'long int'
devzero.c:45:17: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

The second line is the `gzgetc()` macro. Reproduction:
[tests/regression/gzread-pos-overflow](../../../tests/regression/gzread-pos-overflow/README.md)
(`devzero.c`, `run.sh`, [report](../../../tests/regression/gzread-pos-overflow/report.txt)).
Strength: high. Real C, a real device, a sanitizer report, and the same report from the
fault-injection harness (one history in 2 000 with a device-like `lseek`). It does not reproduce on
macOS, where `lseek` on `/dev/zero` does not accept such offsets.

## Scope

Transparent reading of a descriptor whose `lseek` succeeds without bounding the offset and which
then delivers data: character devices on Linux. For a gzip stream the same overflow needs about
2^63 bytes of decompressed output, which is not practical. The effect is undefined behaviour on a
signed counter; with the usual wrapping, `gztell` becomes negative and later seeks are computed
from a wrong position. No memory error follows from it in the code read so far (**to confirm** in
the proof).

## What zlib.h says

zlib.h says that `gzseek` returns -1 "if the resulting position would not be representable in
the offset type". It says nothing about reads that move the position past that limit, or about
devices.

## Fix

[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch), read side:
a helper `gz_room(state, max)` returns `max`, or less if delivering `max` more bytes would carry
`x.pos` past `GZ_OFF_MAX`. `gz_fetch` fills the output buffer with at most that many bytes (and at
least one, so that the end of the input is still found), so that `x.pos + x.have` never exceeds
`GZ_OFF_MAX` and the `gzgetc()` macro stays defined. `gz_read` and `gzgets` deliver at most that
many bytes; if data remains that cannot be delivered, they discard it and set `Z_DATA_ERROR`
"position overflow". Below `GZ_OFF_MAX - 2 * size` nothing changes. Near the limit the same bytes
are delivered, in smaller fills. At the limit, the end of the input is still reported as before;
only data that would have overflowed the position becomes an error.

The invariant the patch keeps is `x.pos + x.have <= GZ_OFF_MAX` whenever a call returns. Every
producer of `x.have` keeps it: `gz_fetch` loads at most `GZ_OFF_MAX - x.pos` bytes; `gz_look`
loads at most `size` bytes in transparent mode, and only at position 0 (right after `gz_reset`);
the direct paths of `gz_read` deliver at most that many bytes; `gzungetc` lowers `x.pos` by the
byte it adds; a seek in transparent mode empties the buffer. The single byte that `gz_fetch` loads
at `GZ_OFF_MAX` to find the end of the input is discarded by its only callers there, `gz_read` and
`gzgets`, before they return (`gz_skip` never fetches at `GZ_OFF_MAX`, since `x.pos + skip` is at
most `GZ_OFF_MAX`). So the fast paths that take buffered bytes one at a time (the `gzgetc` function,
the `gzgetc()` macro) and `gz_skip_have` need no check. The reproduction's `fast` run exercises
these paths at `INT64_MAX - 2`.

Checks of the patch: [upstream-description.md](upstream-description.md), section Testing.
