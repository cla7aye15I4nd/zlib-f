# gzwrite: signed overflow of the position after a forward seek

Status: confirmed by UndefinedBehaviorSanitizer on x86_64 Linux with the real `/dev/null`. Fixed
in the verified source by the local patch
[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch), approved by
the owner on 2026-11-12 and not yet submitted upstream. Read-side twin:
[gzread-pos-overflow](../gzread-pos-overflow/README.md).

Source pin: `757f0527154291bcf6bfbd6396ecde6bedd2db95`, with patches 0001 to 0003.

## What goes wrong

On a writer, `state->x.pos` (signed `z_off64_t`) counts the bytes accepted. `gzseek64` checks
only that its target fits in `z_off64_t`; a forward seek is kept as a pending skip, and the next
write first writes that many zeros (`gz_zero`), which moves `x.pos` to the target. `gz_write`
(`state->x.pos += copy` and `+= n`), the fast path of `gzputc` (`x.pos++`) and `gzprintf`
(`x.pos += len`) then add to it with no bound.

## History

```
fd = open("/dev/null", O_WRONLY);
f = gzdopen(fd, "wT");                   /* transparent writer */
gzbuffer(f, 1 << 29);
gzseek(f, INT64_MAX - 10, SEEK_SET);     /* pending skip */
gzwrite(f, buf, 100);                    /* gz_zero writes INT64_MAX - 10 zeros, then
                                            x.pos += 100: signed overflow */
```

Second history: `gzseek(f, INT64_MAX, SEEK_SET)`, then `gzputc(f, 'a')`: overflow in the fast
path of `gzputc`. Every call is inside the documented use. The zero fill is 2^34 writes of 2^29
bytes; `/dev/null` accepts them.

## Evidence

UndefinedBehaviorSanitizer, x86_64 Linux (kernel 7.0, gcc 15.2), the real `/dev/null`, source
with patches 0001 to 0003, 17 minutes:

```
gzwrite.c:230:26: runtime error: signed integer overflow: 9223372036854775797 + 100 cannot be represented in type 'long int'
```

With a `write()` that answers for `/dev/null` without a system call (`fastwrite.c`), the same
report on Linux and macOS in about a minute, and for `gzputc`:

```
gzwrite.c:352:25: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

Reproduction: [tests/regression/gzwrite-pos-overflow](../../../tests/regression/gzwrite-pos-overflow/README.md)
(`wpos.c`, `fastwrite.c`, `run.sh`, [report](../../../tests/regression/gzwrite-pos-overflow/report.txt)).
Strength: high (real C, real device, sanitizer report), but slow to reach: the overflow needs
about 2^63 bytes accepted by the sink.

## Scope

Transparent writers to a sink that accepts unbounded output (`/dev/null`, a pipe to a consumer
that discards). For a regular file the write fails long before (`EFBIG`). For a compressing
writer the zeros must be compressed first, about 2^63 bytes of CPU work, which is not practical.
The effect is undefined behaviour on a signed counter; with the usual wrapping, `gztell` becomes
negative.

## What zlib.h says

zlib.h says that `gzseek` returns -1 "if the resulting position would not be representable in
the offset type". It says nothing about writes that move the position past that limit.

## Fix

[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch), write side:
`gz_write` refuses a write of `len` bytes when `GZ_OFF_MAX - x.pos < len`, `gzputc` leaves its fast
path at `GZ_OFF_MAX` (and `gz_write` then refuses), and `gzprintf` refuses formatted output that
would pass the limit. Each sets `Z_DATA_ERROR` "position overflow". Writes that stay within the
limit are unchanged. A write that crosses the limit is refused as a whole; before, it was undefined
once the position overflowed, and defined only if an I/O error or a stall stopped it before that
point, in which case it now reports "position overflow" instead of the I/O error.

The pull request draft covering both sides is
[../gzread-pos-overflow/upstream-description.md](../gzread-pos-overflow/upstream-description.md).
