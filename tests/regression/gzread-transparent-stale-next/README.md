# Transparent read with a partial read then an error: gzread copies from a stale x.next

In `gz_fetch`, `case COPY`, `gz_load` stores the bytes it got in `x.have` and returns -1 when a later
`read()` fails with an error other than `EAGAIN`. `gz_fetch` then returns before it sets
`x.next = out`, and `gz_read` copies `x.have` bytes from the old `x.next`.

`stale.c` sets a 16-byte buffer (`gzbuffer(f, 16)`, so a 32-byte output buffer) and consumes 48
bytes of a 128-byte raw file with `gzgetc`: `x.have` is 0 and `x.next` is one past the output
buffer. It then replaces `read()` with one that returns one byte and then fails with `EIO`, and
calls `gzread(f, buf, 1)`. The replacement `read()` is defined in the program, so the static
`libz.a` calls it.

`run.sh` builds the pinned source twice under ASan and UBSan: without any patch, and with
`patches/*.patch`, which includes `0003-gzread-partial-copy-read-error.patch` (upstream
[PR #1363](https://github.com/madler/zlib/pull/1363)). The unpatched build must report a
`heap-buffer-overflow` READ of size 1 in `gz_read` (`gzread.c:369`), 0 bytes after the 32-byte
output buffer. The patched build must report nothing; `gzread` returns 1 and keeps `Z_ERRNO`.

`report.txt` is the raw output of one run on arm64 macOS (Apple clang 21), process ids replaced.
No C compiler was available on an x86_64 Linux host for this run. The upstream pull request reports
the same `gzread.c:369` overflow on x86_64 Linux with an `LD_PRELOAD` read override.

This is a library defect inside the documented use, not a caller layout: a `read()` that returns
some bytes and then fails is an I/O error zlib handles. The verified source applies the submitted
fix as a temporary patch ([patches](../../../patches/README.md)).
