# gzseek after an initial gzungetc: signed overflow in gzseek64

zlib.h allows `gzungetc` right after `gzopen`. It sets `state->x.pos` to -1. A following
`gzseek` then overflows signed 64-bit arithmetic in `gzseek64`:

- `gzseek(f, 1, SEEK_CUR)`: `pos` is -1, and the range check `offset > GZ_OFF_MAX - pos`
  evaluates `GZ_OFF_MAX - (-1)` (`gzlib.c:395`).
- `gzseek(f, LONG_MAX, SEEK_SET)`: the range check passes, and the displacement
  `pos - state->x.pos` is `LONG_MAX + 1`: in the `LSEEK` argument for a transparent file
  (`gzlib.c:403`), in `offset = pos - state->x.pos` for a gzip file (`gzlib.c:424`).

`seek.c` makes each call on a fresh handle. `run.sh` builds the pinned source twice under ASan and
UBSan: without any patch, and with `patches/*.patch`, which includes
`0002-gzseek-negative-position-overflow.patch` (upstream
[PR #1361](https://github.com/madler/zlib/pull/1361)). The unpatched build must report a signed
overflow in each of the four runs (transparent and gzip input, `SEEK_CUR` and `SEEK_SET`). The
patched build must report nothing; `SEEK_CUR` returns 0 and `SEEK_SET` returns -1.

`report.txt` is the raw output of one run on arm64 macOS (Apple clang 21), process ids replaced.
No C compiler was available on an x86_64 Linux host for this run; the overflow is in 64-bit
`z_off64_t` arithmetic and does not depend on the target. On x86_64 Linux, UBSan names the type
`long int` instead of `off_t`.

This is a library defect inside the documented use, not a caller layout. The verified source
applies the submitted fix as a temporary patch ([patches](../../../patches/README.md)).
