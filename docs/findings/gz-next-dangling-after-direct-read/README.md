# x.next left in the caller's buffer after a direct read

Status: undefined by the letter of C. No sanitizer reports it, and no misbehaviour has been
observed. Fixed in the verified source by the local patch
[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch), approved by
the owner on 2026-11-12 and not yet submitted upstream. The same patch fixes
[gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md).

Source pin: `757f0527154291bcf6bfbd6396ecde6bedd2db95`, with patches 0001 to 0004.

## What goes wrong

For a large request on a gzip file, `gz_read` decompresses directly into the caller's buffer:
it sets `strm.next_out` to the buffer and calls `gz_decomp`, which ends with
`state->x.next = strm->next_out - state->x.have`. `gz_read` then sets `x.have` to 0 but leaves
`x.next` pointing into the caller's buffer. The caller may free that buffer: zlib.h gives the
library no claim on it after `gzread` returns. Later:

- `gzseek64` (not transparent, output buffer empty) does `state->x.next += n` with `n == 0`;
- `gzdirect`, when the member has ended (`how == LOOK`), calls `gz_skip_have`, which does the
  same.

C11 6.2.4p2: the value of a pointer becomes indeterminate when the object it points to reaches
the end of its lifetime; 6.5.6p8: pointer arithmetic needs a pointer to an object. So the
evaluation is undefined. On x86_64 with the usual compilers, `p + 0` leaves `p` unchanged, and
the pointer is never dereferenced.

## History

```
f = gzopen("data.gz", "rb");             /* 100000 bytes compressed */
buf = malloc(100000);
gzread(f, buf, 100000);                  /* direct decompression: x.next into buf */
free(buf);
gzseek(f, 1, SEEK_CUR);                  /* x.next += 0 on the dangling pointer */
                                         /* or: gzdirect(f) */
```

## Evidence

Strength: by the letter of C only. No sanitizer reports it: there is no access, and `p + 0` does
not overflow. The Lean model does report it: there the arithmetic on a pointer into a freed block
is a fault. Before the translation followed this patch, the theorem `gzseek64_dangling_next_ub`
proved that the translation of `gzseek64` reaches it; with the patch, `gzseek64_dangling_next_ok`
(`ZlibF/Proof/gzlib.c.seek.lean`) proves that a forward seek with nothing buffered does not fault,
whatever `x.next` holds. The reproduction uses the probe of
[../gz-reset-next-uninitialised/probe.h](../gz-reset-next-uninitialised/probe.h):

```
x.next + 0 at gzread.c:313, x.next = inside the freed caller buffer
x.next + 0 at gzlib.c:435, x.next = inside the freed caller buffer
```

Files: `dangling.c`, `run.sh`, [report.txt](report.txt) (x86_64 Linux, gcc 15.2; the same result
on arm64 macOS). Before the fix the probe sees both evaluations, after it none, and neither build
gets a sanitizer report.

## Scope

Readers of gzip files that read with requests of at least twice the buffer size into memory they
free before a later `gzseek` or `gzdirect` on the same file. No observable effect on common
platforms.

## What zlib.h says

Nothing about the lifetime of the `gzread` buffer after the call returns: a caller may free it.

## Fix

The same as for [gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md):
[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch) advances
`x.next` only when `n` is not zero. When `n` is not zero, the output was just produced in the
library's own buffer, where `x.next` points. No result, return value or state changes on any path.

Pull request draft (one pull request for both):
[../gz-reset-next-uninitialised/upstream-description.md](../gz-reset-next-uninitialised/upstream-description.md).
