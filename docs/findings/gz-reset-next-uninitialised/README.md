# gz_reset never writes x.next; gzseek and gzdirect read it

Status: undefined by the letter of C. No sanitizer reports it, and no misbehaviour has been
observed. Fixed in the verified source by the local patch
[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch), approved by
the owner on 2026-11-12 and not yet submitted upstream. The same patch fixes
[gz-next-dangling-after-direct-read](../gz-next-dangling-after-direct-read/README.md).

Source pin: `757f0527154291bcf6bfbd6396ecde6bedd2db95`, with patches 0001 to 0004.

## What goes wrong

`gz_open` allocates the `gz_state` record with `malloc`, and `gz_reset` initialises its fields
except `x.next`. On a reader, `x.next` is first written when output is produced (`gz_look` in
transparent mode, `gz_decomp`, `gz_fetch`, `gzungetc`). Two functions evaluate it before that:

- `gzseek64`, when not in transparent mode: `n` is the part of the target that lies in the
  output buffer, 0 when the buffer is empty, and the code does `state->x.next += n` anyway
  (`gzlib.c`, in "if reading, skip what's in output buffer").
- `gz_skip_have`, called by `gzdirect` after `gz_look`: on a gzip file `gz_look` does not
  write `x.next`, and `gz_skip_have` does `state->x.next += n` with `n == 0`.

The value read is the indeterminate content of the allocation. C11 makes it undefined to use an
indeterminate value that may be a trap representation (6.2.6.1p5, J.2), and pointer arithmetic is
defined only for a pointer to an object or one past it (6.5.6p8); an indeterminate pointer is
neither. On x86_64 with the usual compilers, `p + 0` leaves `p` unchanged and nothing goes wrong.

## History

```
f = gzopen("data.gz", "rb");      /* a gzip file */
gzseek(f, 3, SEEK_SET);           /* x.next += 0 on the never-written field */

f = gzopen("data.gz", "rb");
gzdirect(f);                      /* gz_look (gzip), then gz_skip_have: x.next += 0 */
```

Both are documented uses; zlib.h even recommends `gzdirect` right after `gzopen` or `gzdopen`.

## Evidence

Strength: by the letter of C only. No sanitizer reports it: `p + 0` on an arbitrary value is
neither an out-of-bounds access nor a pointer overflow, and MemorySanitizer does not report an
uninitialised value that is only copied. The reproduction therefore routes every `x.next += n` of
`gzlib.c` and `gzread.c` through a probe (`probe.h`; the value computed is unchanged) and prints
each evaluation with `n == 0`. Under AddressSanitizer fresh allocations are filled with `0xbe`:

```
x.next + 0 at gzlib.c:435, x.next = 0xbebebebebebebebe
x.next + 0 at gzread.c:313, x.next = 0xbebebebebebebebe
```

Files: `unset.c`, `probe.h`, `run.sh`, [report.txt](report.txt) (x86_64 Linux, gcc 15.2; the same
result on arm64 macOS). `run.sh` builds the source without and with 0005 under ASan and UBSan;
before the fix the probe sees both evaluations, after it none, and neither build gets a sanitizer
report. In the Lean model a fresh pointer field is NULL and `NULL + 0` passes, so the model does
not see it either; the proof rule that a pointer field is written before it is read
(`docs/spec/safety.md`, section 3) is what exposes it.

## Scope

Every reader: the first `gzseek` that is not in transparent mode with an empty output buffer, or
`gzdirect` on a gzip file, right after `gzopen`/`gzdopen` (and after `gzrewind`, where `x.next`
keeps whatever it held before). No observable effect on common platforms.

## What zlib.h says

Nothing: the exposed `next` field "can only be used by the gzgetc() macro", which reads it only
when `have` is not zero.

## Fix

[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch): in
`gzseek64` and `gz_skip_have`, advance `x.next` only when `n` is not zero. When `n` is not zero,
`x.have` is not zero, so the field was written when that output was produced. Initialising
`x.next` to `NULL` in `gz_reset` would not do: `NULL + 0` is itself undefined in C, and clang's
`-fsanitize=pointer-overflow` reports it. No result, return value or state changes on any path.

Pull request draft: [upstream-description.md](upstream-description.md).
