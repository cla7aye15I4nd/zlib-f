# Statement test: `Goal.gz_refusal`

`run.sh` builds the pinned zlib with its patches under AddressSanitizer and
UndefinedBehaviorSanitizer (LeakSanitizer as well on Linux) and runs `harness.c`. It calls every
gz function of the goal with a `NULL` handle: `gzread`, `gzfread`, `gzwrite`, `gzfwrite`, `gzputc`,
`gzputs`, `gzprintf`, `gzvprintf`, `gzflush`, `gzsetparams`, `gzgetc`, `gzgetc_`, `gzungetc`,
`gzgets`, `gzdirect`, `gzseek`, `gzseek64`, `gztell`, `gztell64`, `gzoffset`, `gzoffset64`,
`gzrewind`, `gzeof`, `gzerror`, `gzclearerr`, `gzbuffer`, `gzclose`, `gzclose_r` and `gzclose_w`.
The other arguments range over boundary values: lengths and sizes that overflow, negative and huge
offsets, every `whence`, flush values out of range, `NULL` buffers.

Each call must return the goal's value, allocate and free nothing (counted with the malloc and free
hooks of the sanitizer allocator), leave `errno` and the lowest free descriptor unchanged, and write
no caller buffer: `gzerror` leaves `*errnum`, `gzread`, `gzfread` and `gzgets` leave `buf`.

`gzgetc` is called as the function, `(gzgetc)(NULL)`. The `gzgetc` macro of `zlib.h` dereferences
its argument, so the macro on `NULL` is undefined behaviour; the goal states the function.

Result on 2026-11-14: 204 calls, no violation and no sanitizer report. A self test that adds a
`gzdopen` and a `gzclose` of a real handle is caught by the allocation and errno checks. This is
evidence, not proof.
