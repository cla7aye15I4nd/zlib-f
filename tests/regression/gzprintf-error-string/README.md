# gzprintf with the handle's own error message: use after free

`gzvprintf` starts with `gz_error(state, Z_OK, NULL)`, which frees `state->msg`. Only afterwards does
`vsnprintf` read the format and the arguments. A caller that passes the string `gzerror` returned
(which is `state->msg`) as a `%s` argument therefore makes `vsnprintf` read freed memory.

`gzvprintf` refuses a handle with an error, except a stalled write (`again`). `errstr.c` makes one:
a transparent writer (`gzdopen(fd, "wT")`) on the write end of a full non-blocking pipe, where
`write()` fails with `EAGAIN`. `gzwrite` stalls (`err = Z_ERRNO`, `again = 1`, a message is
allocated). The program then calls `gzerror` and passes its result to `gzprintf(f, "%s", msg)`.

`run.sh` builds the pinned source with `patches/*.patch` under ASan. The run must report a
`heap-use-after-free` READ in `gzvprintf` (`gzwrite.c:491`, the `vsnprintf` call). The block was
freed by `gz_error` (`gzlib.c:568`) called from `gzvprintf` (`gzwrite.c:448`), and allocated by
`gz_error` from `gz_comp`.

`report.txt` is the raw output of one run on arm64 macOS (Apple clang), process id replaced.

zlib.h says only that later calls of `gzerror` may invalidate the returned string. In fact any call
that reaches `gz_error` frees it: `gzprintf`, `gzputs`, `gzwrite`, `gzread` and others. The proved
domain keeps caller strings and buffers apart from the handle's own blocks: `GzRange` for the
buffers of `gzwrite`, `gzputs` and `gzread`, and the separation clause of `GzArguments` for the
format and the `%s` arguments of `gzprintf` and `gzvprintf` ([deviations](../../../docs/deviations.md)).
