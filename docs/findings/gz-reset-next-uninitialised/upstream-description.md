# Upstream pull request draft: x.next advanced by zero

For the owner to submit. One pull request covers
[gz-reset-next-uninitialised](README.md) and
[gz-next-dangling-after-direct-read](../gz-next-dangling-after-direct-read/README.md); the diff is
[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch). Nothing has
been sent.

---

**Title:** gzseek64, gz_skip_have: do not advance x.next when nothing is skipped

**Problem**

`gzseek64` (reading, not transparent) and `gz_skip_have` (used by `gzdirect` and `gz_skip`) do
`state->x.next += n` also when `n` is 0, that is when the output buffer is empty. In two
documented histories `x.next` holds no valid pointer at that moment:

1. Right after `gzopen`/`gzdopen` of a gzip file: `gz_reset` does not set `x.next`, and the state
   comes from `malloc`. `gzseek(f, 3, SEEK_SET)` or `gzdirect(f)` then does arithmetic on an
   indeterminate value.
2. After a `gzread` large enough to decompress directly into the caller's buffer, `gz_decomp`
   leaves `x.next` pointing into that buffer (with `x.have` 0). Once the application frees its
   buffer, a `gzseek` or (after the end of the member) `gzdirect` does arithmetic on a pointer to
   a freed object.

Both are undefined behaviour in C (C11 6.2.4p2, 6.2.6.1p5, 6.5.6p8), although `p + 0` is harmless
on current compilers and no sanitizer reports it.

**Reproduction**

```c
gzFile f = gzopen("data.gz", "rb");
gzseek(f, 3, SEEK_SET);                /* x.next += 0, x.next never written */
```

```c
gzFile f = gzopen("data.gz", "rb");   /* 100000 bytes compressed */
unsigned char *buf = malloc(100000);
gzread(f, buf, 100000);                /* x.next now points into buf */
free(buf);
gzseek(f, 1, SEEK_CUR);                /* x.next += 0 on a dangling pointer */
```

A probe on `x.next += n` shows `n == 0` with `x.next == 0xbebebebebebebebe` (fresh ASan memory)
in the first case and a pointer into the freed buffer in the second.

**Fix**

Advance `x.next` only when `n` is not zero. When `n` is not zero, `x.have` was not zero, so
`x.next` points at that output. Setting `x.next = NULL` in `gz_reset` would not be enough:
`NULL + 0` is also undefined in C, and the dangling case would remain.

**Testing**

- `make test`, default and with `-fsanitize=address,undefined`: passes.
- The probe shows the zero advances before the change and none after.
- About 30 000 random gz call histories with fault injection under ASan and UBSan on macOS and
  x86_64 Linux (with LeakSanitizer): no report, no leak, no hang.
