# gzread position overflow after a seek on /dev/zero

Finding: [docs/findings/gzread-pos-overflow](../../../docs/findings/gzread-pos-overflow/README.md).

`devzero.c` opens `/dev/zero` with `gzdopen(fd, "r")`, reads one byte (transparent mode), seeks
to `INT64_MAX` and reads 16 bytes. With the argument `near` it seeks to `INT64_MAX - 4` and reads
one byte with `gzread`, four with the `gzgetc()` macro, then calls `gzgets`. With the argument
`fast` it seeks to `INT64_MAX - 2` and uses the paths that do not go through `gz_read`: `gzungetc`,
the `gzgetc()` macro and function, `gzclearerr`, `gzungetc` again, `gzdirect`, `gzseek` by 0 and
`gzgets` across `INT64_MAX`.

`run.sh` needs Linux, where `lseek` on `/dev/zero` succeeds without moving. It builds the pinned
source twice under ASan and UBSan: with `patches/*.patch` except 0004, and with all of them. Before
0004 each run must report a signed overflow of the position: in `gz_read`, in the `gzgetc()`
macro in `devzero.c`, and in the `gzgetc` function. With 0004 nothing may be reported, and the reads end with `Z_DATA_ERROR`
"position overflow".

`report.txt` is the raw output of one run on x86_64 Linux (kernel 7.0, gcc 15.2).
